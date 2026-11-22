# Admissible sequence of partitions

An admissible sequence is an increasing sequence $(\mathcal{A}_n)_{n \ge 0}$ of partitions of $T$
with $\operatorname{card}\mathcal{A}_n \le N_n$, that is $\operatorname{card}\mathcal{A}_0 \le 1$ (so
$\mathcal{A}_0 = \{T\}$ when $T$ is nonempty) and $\operatorname{card}\mathcal{A}_n \le 2^{2^n}$ for $n \ge 1$; increasing means that every set of
$\mathcal{A}_{n+1}$ is contained in a set of $\mathcal{A}_n$ (Talagrand, *Upper and Lower Bounds
for Stochastic Processes*, 2nd ed., 2021, Definition 2.7.1). The partition $\mathcal{A}_n$ is
recorded by its cell map $t \mapsto A_n(t)$, the unique element of $\mathcal{A}_n$ containing $t$:
each point lies in its cell, two points of a cell have the same cell, the cell of $t$ at level
$n + 1$ is contained in its cell at level $n$, and the cells at level $n$ number at most $N_n$.

The bounds satisfy $N_n^2 \le N_{n+1}$: the double exponential makes $\log N_n$ double at each step, so a
partition with at most $N_n$ cells can be refined by splitting each cell into at most $N_n$ pieces.
