# Distribution of the canonical mesh-pattern statistic

Let $2 \le k \le n$ and let $j$ be a
natural number. For a permutation $\sigma$ of $\{1, \dots, n\}$ with positions numbered
$1, \dots, n$, let $p$ be the position of its largest value, and let $N_k(\sigma)$ be the
canonical mesh-pattern statistic: the number of positions $i$ such that $\sigma(t) < \sigma(i)$
for all $t < i$ and at least $k - 1$ positions $t$ with $i < t < p$ have $\sigma(t) > \sigma(i)$,
plus $1$ if $p \ge k$. Then the number of permutations $\sigma$ of $\{1, \dots, n\}$ with
$N_k(\sigma) = j$ equals $(k-1)!\, c_{k-1}(n, j + k - 1)$, where the unsigned $r$-Stirling
number of the first kind $c_r(n, m)$ is the coefficient of $X^m$ in
$X^r (X + r)(X + r + 1) \cdots (X + n - 1)$.
