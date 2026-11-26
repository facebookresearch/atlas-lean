# Random joining has finite support and iterates the join step

For every natural number $m$ and every list $b$ of natural numbers, there is a finite set $F$ of lists of block-size lists such that

- the [random-joining law](random-joining.md) $R_m(b, \mathbf{p})$ vanishes for every $\mathbf{p}$ outside $F$, and
- for every $j \le m$ and every real function $g$ on lists of natural numbers,

$$\sum_{\mathbf{p} \in F} R_m(b, \mathbf{p})\, g(p_j) = (J^{j} g)(b),$$

where $p_j$ is the entry of index $j$ of $\mathbf{p}$ (the empty list if $\mathbf{p}$ is shorter) and $J$ is the [transition operator of random joining](join-step.md).
