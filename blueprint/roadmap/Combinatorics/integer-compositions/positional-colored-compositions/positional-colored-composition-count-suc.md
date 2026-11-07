# A recurrence for positional colored compositions

For natural numbers $m$, $k$ and $\ell$
with $m \ge 1$, $m \nmid k$ and $\ell \ge 1$,
$c_{m,k+1}(\ell + 1) = c_{m,k+1}(\ell) + c_{m,k}(\ell)$.

The paper prints the hypotheses $k \ge 1$, $\ell \ge 2$ and $1 \le m \le \ell - 1$, which allow
$m \mid k$; there the identity fails: for $m = 1$, $k = 1$ and $\ell = 2$ one has
$c_{1,2}(3) = 8$ but $c_{1,2}(2) + c_{1,1}(2) = 6$. The paper's argument (remove a first part
$1$ or decrease the first part) needs the first part to be uncolored, which is the condition
$m \nmid k$.

## Sources

- Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26 (2026), Article A49, Theorem 6 (`integers-2026-A49-thm-6`).
