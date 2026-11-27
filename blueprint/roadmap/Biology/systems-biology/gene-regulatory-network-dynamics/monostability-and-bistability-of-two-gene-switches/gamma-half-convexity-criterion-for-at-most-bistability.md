# $\gamma^{1/2}$-convexity criterion for at most bistability of two-gene switches

**System.** For $\alpha, \beta > 0$ consider the planar ODE on $\mathbb{R}_+^2$

$$
\dot x = \alpha f(y) - x, \qquad \dot y = \beta g(x) - y,
$$

where $f, g \in C^3(\mathbb{R}_+, \mathbb{R}_+)$ are both increasing (cooperative system, e.g. mutualism) or both decreasing (competitive system, e.g. the toggle switch of two mutually repressing genes), with $|f'|, |g'| > 0$ and at least one of $f, g$ bounded. Then every solution is bounded and converges to an equilibrium (the system is monotone), and equilibria are in bijection with fixed points of $x \mapsto \alpha f(\beta g(x))$.

**$\gamma^{1/2}$-convexity.** A strictly monotone $f \in C^3(I)$ is *$\gamma^{1/2}$-convex* if $\gamma_f^{1/2} = 1/\sqrt{|f'|}$ is convex on $I$, equivalently $f' f''' \le \tfrac{3}{2} (f'')^2$; *$\gamma^{1/2}$-concave* if $1/\sqrt{|f'|}$ is concave; strict versions use strict convexity or concavity. Equivalently, $f$ is $\gamma^{1/2}$-convex iff $f'(x) f'(y) \le \big(\tfrac{f(x) - f(y)}{x - y}\big)^2$ for all $x \ne y$. The class is closed under composition, and $f$ is $\gamma^{1/2}$-convex iff $f^{-1}$ is $\gamma^{1/2}$-concave. Hill functions $z \mapsto 1/(1 + z^a)$ and shifted Hill functions are $\gamma^{1/2}$-convex.

**Theorem.**

1. If $f$ and $g$ are $\gamma^{1/2}$-convex and at least one is strictly $\gamma^{1/2}$-convex, then for every $\alpha, \beta > 0$ the system has at most three equilibria and is either monostable (one stable equilibrium) or bistable (exactly two stable equilibria).
2. If $f$ and $g$ are $\gamma^{1/2}$-concave and at least one is strictly $\gamma^{1/2}$-concave, then for every $\alpha, \beta > 0$ the system is monostable.

For cyclic $n$-dimensional systems $\dot x_1 = f_1(x_n) - x_1$, $\dot x_i = f_i(x_{i-1}) - x_i$ ($2 \le i \le n$), with $f_1,\dots,f_n \in C^3(\mathbb R_+,\mathbb R_+)$ monotone, $|f_i'| > 0$ on $\mathbb R_+$ and an even number of them decreasing: if all $f_i$ are $\gamma^{1/2}$-convex (resp. $\gamma^{1/2}$-concave) and at least one is strictly so, the system has at most three (resp. at most one) equilibria; if moreover $(f_n \circ \dots \circ f_1)'(x) \ne 1$ at every fixed point $x$ of $f_n \circ \dots \circ f_1$, the system is at most bistable (Proposition 8).

## Depends on

- [Hill repression function](../../genetic-toggle-switch/hill.md)

## Expansion

Write $F = \alpha f \circ \beta g$. A counting lemma says that if a $C^1$ map has $2n$ or more fixed points then $n$ of them satisfy $F' \le 1$ and $n$ satisfy $F' \ge 1$; when $F$ is positive and bounded, $2n$ fixed points force $n + 1$ with $F' \le 1$. If $\Psi \circ F'$ is strictly convex or concave for some $\Psi$ with $\Psi(1) = 1$, $\Psi \ge 1$ on $(-\infty, 1]$ and $\Psi \le 1$ on $[1, \infty)$, then $F$ has at most three fixed points. Taking $\Psi(s) = 1/\sqrt{|s|}$, the composition rule makes $\gamma^{1/2}_F$ strictly convex whenever $f, g$ are $\gamma^{1/2}$-convex and one strictly so; for monotone planar systems the stable equilibria are the outer two of three ordered equilibria and the middle one is a saddle. In the concave case $\gamma^{1/2}_F$ is concave and the fixed point is unique.

## Sources

- J. Guilberteau, C. Pouchol, N. Pouradier Duteil, "Monostability and bistability of biological switches", arXiv:2104.04227 (2021): Section 1 (model and main theorem), Section 2 (fixed-point counting propositions, definition of $\gamma^{1/2}$-convex functions, composition, non-local and inverse characterizations), Section 3 (criterion ensuring at most bistability and its extension to cyclic $n$-dimensional ODEs, Proposition 8), Appendix (ordering of stable points, basins of attraction, further $\gamma^{1/2}$-convex sigmoid functions). <https://doi.org/10.48550/arXiv.2104.04227> Published version: Journal of Mathematical Biology 83 (2021) 65, <https://doi.org/10.1007/s00285-021-01687-y>.
