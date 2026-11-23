# The largest weights have the largest sum

Let $w_i \ge 0$ be weights and let $S$ hold the largest of them: $w_j \le w_i$ whenever $i \in S$ and $j \notin S$. Then every set $T$ with $\#T \le \#S$ satisfies $\sum_{i \in T} w_i \le \sum_{i \in S} w_i$. Indeed the elements of $T \setminus S$ are at most as many as those of $S \setminus T$, and each weight on $T \setminus S$ is at most the minimum weight on $S \setminus T$. This is the rearrangement step behind (2.19) of R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998).
