# Vector timestamps are monotone along happened-before

In an execution, write $V_i$ for
the vector timestamp that the vector clock algorithm gives to the event at position $i$. If the
event at position $a$ happened before the event at position $b$, then $V_a(q) \le V_b(q)$ for
every process $q$.
