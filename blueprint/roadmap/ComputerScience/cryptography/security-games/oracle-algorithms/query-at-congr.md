# The query at a counter depends only on earlier answers

Let $s$ and $s'$ be stateful oracles with $s(i, x) = s'(i, x)$ for all $i < j$ and all queries $x$.
Then for every starting counter $i \le j$, the runs against $s$ and against $s'$ from $i$ ask the same
query, or none, when the counter is $j$.
