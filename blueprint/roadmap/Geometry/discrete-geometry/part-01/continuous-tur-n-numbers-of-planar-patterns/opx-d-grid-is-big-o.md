# Upper bound for higher-dimensional grid patterns

Let $X_1, \dots, X_d$ be finite sets of
real numbers, $k_i = |X_i|$, and $P = X_1 \times \dots \times X_d \subseteq \mathbb{R}^d$. Put
$\alpha = \max_i k_i / \prod_i k_i$ if $d \ge 1$ and every $k_i$ is positive, and $\alpha = 0$
otherwise. Then $\mathrm{opx}(n, P, d) = O(n^{d - \alpha})$ as the natural number $n \to \infty$.

When some $k_i = 0$ the grid $P$ is empty and the bound reads $O(n^d)$.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.13 (`integers-2024-A1-cor-5-13`).
