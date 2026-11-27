# Global stability of the Ricker map for 0 < r ≤ 2

Let $f(x) = x e^{r(1 - x)}$ on $(0, \infty)$ with $r > 0$; its positive fixed point is $x^* = 1$, with $f'(1) = 1 - r$. If $0 < r \le 2$, then $f^n(x_0) \to 1$ for every $x_0 > 0$. Cull's enveloping theorem (Cull 2007; stated as the Enveloping Theorem, Theorem 3, in Cull, Walsh and Wherry 2008, p. 31) proves this: the function $h(x) = 2 - x$ satisfies $f(x) < h(x)$ for $x \in (0, 1)$ and $f(x) > h(x)$ for $x > 1$, and since $h \circ h$ is the identity, an envelope of this kind forces global attraction to the fixed point. Cull, Walsh and Wherry (2008, Section 3.2, p. 32) show that $2 - x$ envelops $x e^{2(1 - x)}$, which in turn envelops $x e^{r(1 - x)}$ for $0 < r < 2$, and list the Ricker map with stability region $0 < r \le 2$ and envelope $2 - x$ in their table on p. 34.

## Expansion

1. The Ricker map on $(0, \infty)$, its fixed point and the local stability condition $|1 - r| \le 1$ (with the neutral case $r = 2$ handled by the global argument).
2. The enveloping lemma (Cull, Walsh and Wherry 2008, Theorem 3, p. 31, in a more general form): for a continuous $f$ with a unique positive fixed point, $f(x) > x$ below and $f(x) < x$ above it, and an envelope $h$ of the stated kind with $h \circ h = \mathrm{id}$, every orbit converges to the fixed point.
3. The verification that $h(x) = 2 - x$ envelopes the Ricker map exactly when $r \le 2$, including the behaviour for $x \ge 2$.

## Sources

- Original result: P. Cull, Population models: stability in one dimension, Bull. Math. Biol. 69 (2007), 989–1017 (the enveloping theorem). <https://doi.org/10.1007/s11538-006-9129-1>
- P. Cull, K. Walsh and J. Wherry, Stability and instability in one dimensional population models, Sci. Math. Jpn. Online e-2008, 29–48, Section 3: Theorem 3 (the Enveloping Theorem, credited to Cull 2007, p. 31), Section 3.2 (the envelope $2 - x$ of the Ricker map, p. 32), and the summary table of Section 4 (p. 34). Open access from the publisher: <https://www.jams.or.jp/scm/contents/e-2008-1/2008-3.pdf>
