set Job;
set Server;
set Room {Server};
set Sequence {Job};
set Noseq {Job};

param or_cost {j in Server};

var v {j in Server, l in Room[j]} integer >= 0, <= 1;

var y {i in Job, j in Server, l in Room [j]} binary;

minimize total_cost: 
sum{j in Server}(sum{l in Room[j]}(or_cost[j] * v[j,l]));

subject to c1{i in Job, j in Sequence[i]}:
sum{l in Room[j]} y[i,j,l] = 1;

subject to c2{i in Job, j in Noseq[i]}:
sum{l in Room[j]} y[i,j,l] = 0;

subject to c3{i in Job, j in Sequence[i], l in Room[j]}:
y[i,j,l] <= v[j,l];

subject to c4{j in Server, l in Room[j]}:
sum{i in Job}y[i,j,l] >= v[j,l];

