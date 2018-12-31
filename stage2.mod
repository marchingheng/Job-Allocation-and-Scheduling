#set of patient
set Job;
#set of all servers(stages)
set Server;
#set of room for server j
set Room {Server};
#process that the patient i need to go through
set Sequence {Job};
#set of server that patient i won't go to
set Noseq {Job};
#set of server that patient i go before go to server j
set Past {Job, Server};

#1 if patient i go to server j's room l 
param y {i in Job, j in Server, l in Room [j]} ;
#duration of operation of patient i in server j
param d {Job, Server};
#opening session of server j room l
param t {j in Server, l in Room[j]};
#cost of overtime in server j
param o_cost {Server};
#cost of waiting time in server j
param w_cost {Server};
#cost of idle time in server j
param i_cost {Server};
#opening cost for server j
param op_cost {Server};

#1 if patient i is arranged directly ahead of job m in server j room l
var z {i in Job, m in Job, j in Server, l in Room [j]} binary;
#idling time of patient i directly following m in server j room l 
var u {i in Job, m in Job, j in Server, l in Room[j]} >= 0;
#overtime of server j's room l
var o {j in Server, l in Room [j]} >= 0;
#waiting time of patient i directly following m in server j room l
var w {i in Job, m in Job, j in Server, l in Room [j]} >= 0;
#start time of patient i in server j's room l
var s {i in Job, j in Server, l in Room [j]} >= 0;
#
var sigma {i in Job, m in Job, j in Server, l in Room [j]} >= 0;


minimize total_cost: 
sum {i in Job}
	(sum {m in Job}
		(sum {j in Server}
			(sum {l in Room [j]}(w_cost[j]*w[i,m,j,l] + i_cost[j]*u[i,m,j,l])))) 
+ sum{j in Server}
	 (sum{l in Room[j]}(o_cost[j]*o[j,l]));

subject to c1{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
y[i,j,l] >= z[i,m,j,l];

subject to c3{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
y[i,j,l] - y[m,j,l] + z[i,m,j,l] <= 1;

subject to c4{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
y[m,j,l] - y[i,j,l] + z[i,m,j,l] <= 1;

subject to c5{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
z[i,m,j,l] + z[m,i,j,l] <= 1;

subject to c6{i in Job,j in Server, l in Room[j]}:
sum{m in Job: m<>i} z[i,m,j,l] <= 1;

subject to c7{m in Job,j in Server, l in Room[j]}:
sum{i in Job: i<>m} z[i,m,j,l] <= 1;

subject to c8{j in Server, l in Room[j]}:
sum{i in Job}y[i,j,l] <= sum{i in Job}(sum{m in Job: m<>i}(z[i,m,j,l])) + 1;

subject to c10{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
w[i,m,j,l] <= 100000*y[i,j,l];

subject to c11{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
u[i,m,j,l] <= 100000*y[i,j,l];

subject to c12{i in Job, j in Server, l in Room[j], m in Job: m<>i}:
sigma[i,m,j,l] <= 100000*y[i,j,l];

subject to c13{i in Job, j in Server, l in Room[j]}:
sum{m in Job: m<>i}(w[m,i,j,l] - w[i,m,j,l] - u[i,m,j,l])  + 
(sum{m in Job: m<>i}(sigma[i,m,j,l]))= d[i,j]*y[i,j,l] - (sum{m in Job: m<>i}(sigma[m,i,j,l]));

subject to c14{j in Server, l in Room[j]}:
o[j,l] - sum{i in Job}(sum{m in Job}(u[i,m,j,l])) = sum{i in Job}(d[i,j]*y[i,j,l]) - t[j,l];

subject to c15{i in Job, j in Sequence[i], k in Past[i,j], l in Room[j], l1 in Room[k]}:
s[i,j,l] >= s[i,k,l1] + d[i,k];

subject to c16{i in Job, j in Sequence[i], l in Room[j], m in Job: m<>i}:
s[i,j,l] >= s[m,j,l] - 100000*(1 - z[i,m,j,l]) + d[m,j];

subject to c17{i in Job, j in Sequence[i], k in Past[i,j], l in Room[j]}:
sum{m in Job: m <> i}(sigma[i,m,j,l] - sigma[i,m,k,l]) >= d[i,k];

subject to c18{i in Job, j in Sequence[i], l in Room[j]}:
sum{m in Job: m <> i}(sigma[m,i,j,l]) >= sum{m in Job: m <> i}(sigma[i,m,j,l]) - 
100000*(1- sum{m in Job: m <> i}(z[m,i,j,l])) + d[i,j];						

subject to c19{i in Job, j in Sequence[i], l in Room[j]}:
s[i,j,l] >= sum{m in Job: m <> i}(sigma[i,m,j,l]);

subject to c20{i in Job, j in Sequence[i], l in Room[j]}:
sum{m in Job: m <> i}w[i,m,j,l] = s[i,j,l] - sum{m in Job: m <> i}sigma[i,m,j,l];










