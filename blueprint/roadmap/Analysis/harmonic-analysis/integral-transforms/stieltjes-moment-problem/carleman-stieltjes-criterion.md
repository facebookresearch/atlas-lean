# Carleman's criterion for the Stieltjes moment problem

Let $\mu$ be a probability measure
on $\mathbb{R}$ with $\mu((-\infty, 0)) = 0$ such that $\int |x|^k \, d\mu(x) < \infty$ for every
integer $k \ge 1$, and write $m_k = \int x^k \, d\mu(x)$. If
$\sum_{k \ge 1} m_k^{-1/(2k)} = \infty$, where the terms are taken in $[0, \infty]$ (so a term
with $m_k = 0$ equals $\infty$), then $\mu$ is Stieltjes moment determinate.

Proof: Symmetrize through the square-root map, apply Denjoy--Carleman quasi-analytic
uniqueness to the difference of characteristic functions, then push forward by squaring.

## Sources

- Gwo Dong Lin, "Recent Developments on the Moment Problem" (2017), Theorem 2, (s6) implies (s7). Source spans: definition lines 57-75, criterion lines 297-321; JIS application lines 152-177.
