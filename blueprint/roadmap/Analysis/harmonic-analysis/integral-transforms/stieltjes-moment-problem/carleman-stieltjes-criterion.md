# Carleman's criterion for the Stieltjes moment problem

Let $\mu$ be a probability measure
on $\mathbb{R}$ with $\mu((-\infty, 0)) = 0$ such that $\int |x|^k \, d\mu(x) < \infty$ for every
integer $k \ge 1$, and write $m_k = \int x^k \, d\mu(x)$. If
$\sum_{k \ge 1} m_k^{-1/(2k)} = \infty$, where the terms are taken in $[0, \infty]$ (so a term
with $m_k = 0$ equals $\infty$), then $\mu$ is Stieltjes moment determinate.

Proof: Symmetrize through the square-root map, apply Denjoy--Carleman quasi-analytic
uniqueness to the difference of characteristic functions, then push forward by squaring.

## Sources

- Gwo Dong Lin, "Recent Developments on the Moment Problem" (2017), Theorem 2, (s6) implies (s7). Corpus `jis_grounded_5e39d97b31ef58deb38a5a58`. Source spans: definition lines 57-75, criterion lines 297-321, TeX SHA-256 e2dcb54a4b25d57ae3ad6e52267862aeca0ae2f38ffb729df0d727013d3c3080; JIS application lines 152-177, source SHA-256 66f0a4a264af03f82a43e3b37e62cc80cf0aed6f43e476e56456006203232bd0.
