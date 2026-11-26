# Lower bound on the number of queries

Let $T$ be a query algorithm that computes the minimax value of every instantiation of a uniform
shape of branching factor $k$ and depth $d$ with distinct leaf variables. For every input $f$ whose
value lies strictly between $\bot$ and $\top$, the total number of queries $T$ makes on $f$,
repetitions included, is at least $k^{\lceil d/2 \rceil} + k^{\lfloor d/2 \rfloor} - 1$.
