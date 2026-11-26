# Global stability of the Ricker map for 0 < r ≤ 2

Let $f(x) = x e^{r(1 - x)}$ on $(0, \infty)$ with $r > 0$; its positive fixed point is $x^* = 1$, with $f'(1) = 1 - r$. If $0 < r \le 2$, then $f^n(x_0) \to 1$ for every $x_0 > 0$. An enveloping theorem of Cull (2007), as restated by Luís and Rodrigues (2016, Theorem 1.4), proves this: the function $h(x) = 2 - x$ satisfies $f(x) < h(x)$ for $x \in (0, 1)$ and $f(x) > h(x)$ for $x > 1$, and since $h \circ h$ is the identity, an envelope of this kind forces global attraction to the fixed point. Luís and Rodrigues (2016, Sec. 4.1) restate this for the Ricker maps and extend the enveloping method to periodic sequences of such maps.

## Expansion

1. The Ricker map on $(0, \infty)$, its fixed point and the local stability condition $|1 - r| \le 1$ (with the neutral case $r = 2$ handled by the global argument).
2. The enveloping lemma: for a continuous $f$ with a unique positive fixed point, $f(x) > x$ below and $f(x) < x$ above it, and an envelope $h$ of the stated kind with $h \circ h = \mathrm{id}$, every orbit converges to the fixed point.
3. The verification that $h(x) = 2 - x$ envelopes the Ricker map exactly when $r \le 2$, including the behaviour for $x \ge 2$.
4. The periodic extension (Luís and Rodrigues) as a separate statement.

## Sources

- Original result: P. Cull, Population models: stability in one dimension, Bull. Math. Biol. 69 (2007), 989–1017. <https://doi.org/10.1007/s11538-006-9129-1> The enveloping theorem follows Luís and Rodrigues (2016), Theorem 1.4.
- R. Luís and E. Rodrigues, Global stability in some one-dimensional non-autonomous discrete periodic population models, 2016, Sec. 4.1. <https://arxiv.org/abs/1603.02723>
