# Lower bound on the Turán number

For $r \ge 1$ and every natural number $n$, the Turán graph $T(n, r)$ has at least $(1 - 1/r)(n^2 - r^2)/2$ edges:

$$(r - 1)(n^2 - r^2) \le 2r\, t(n, r).$$

The proof is by strong induction on $n$ using the recursion $t(n + r, r) = t(n, r) + n(r - 1) + \binom{r}{2}$: adding one vertex to each part adds $n(r - 1)$ edges to the old vertices and $\binom{r}{2}$ among the new ones. For $n < r$ the left side is negative or zero.
