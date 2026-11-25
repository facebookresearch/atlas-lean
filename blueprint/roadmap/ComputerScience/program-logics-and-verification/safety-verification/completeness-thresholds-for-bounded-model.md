# Completeness thresholds for bounded model checking

Let $M$ be a finite Kripke structure with initial states $I$ and transition relation $T$, and write $M \models \mathbf{EF}\, p$ when some state satisfying $p$ is reachable from a state in $I$. Its *diameter* $d$ is the least natural number such that for every path $s_0, \dots, s_{d+1}$ of $M$ there is a path $t_0, \dots, t_l$ with $l \le d$, $t_0 = s_0$ and $t_l = s_{d+1}$. Then for every atomic proposition $p$, $M \models \mathbf{EF}\, p$ if and only if $M \models_k \mathbf{EF}\, p$ for some $k \le d$, where $\models_k$ is bounded satisfaction along paths of length $k$. Consequently, if no bounded model checking instance of length at most $d$ finds a state satisfying $p$, none is reachable.

## Sources

- A. Biere, A. Cimatti, E. Clarke and Y. Zhu, "Symbolic model checking without BDDs", *TACAS 1999*, LNCS 1579, Springer, 1999, Definition 19 and Theorem 20
