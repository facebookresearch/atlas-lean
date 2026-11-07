# Vector timestamps are monotone along one step of happened-before

In an execution,
write $V_i$ for the vector timestamp that the vector clock algorithm gives to the event at
position $i$. If the event at position $j$ follows the event at position $i$ by one step of
happened-before, then $V_i(q) \le V_j(q)$ for every process $q$.
