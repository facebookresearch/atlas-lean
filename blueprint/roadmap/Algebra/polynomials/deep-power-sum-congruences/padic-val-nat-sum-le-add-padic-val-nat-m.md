# A valuation bound from Kummer's theorem

Let $p$ be a prime, let $r_1, \dots, r_k$ be
natural numbers with sum $m$, and let $j$ be an index with $r_j \ne 0$. Then

$$v_p(m) \le v_p(r_j) + v_p\binom{m}{r_1, \dots, r_k},$$

that is, $v_p(r_j) \ge v_p(m) - v_p\binom{m}{r_1, \dots, r_k}$.

The hypothesis $r_j \ne 0$ is needed because $v_p(0)$ is taken to be $0$: for $(r_1, r_2) = (0, p)$
the inequality fails at $j = 1$. With the paper's convention $v_p(0) = \infty$ that case is trivial.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Corollary 24 (`integers-2024-A46-cor-24`).
