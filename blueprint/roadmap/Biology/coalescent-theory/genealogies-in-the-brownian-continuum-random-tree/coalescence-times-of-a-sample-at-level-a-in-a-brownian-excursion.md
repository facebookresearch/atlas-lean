# Coalescence times of a sample at level a in a Brownian excursion

**Setting.** Let $X$ be a Brownian excursion from $0$ conditioned to reach level $1$; it codes Aldous' continuum random tree (CRT) of height at least $1$, the scaling limit of the genealogy of a critical branching population conditioned to survive to time $1$. Fix $a \in (0,1]$ and let $L^a_t$ be the local time of $X$ at level $a$, $L^a_\infty$ its total. Conditionally on $(L^a_t)$, let $U_1,\dots,U_k$ be independent with $P(U_1 \le t \mid L^a) = L^a_t/L^a_\infty$: a uniform sample of $k$ individuals alive at time $a$. With order statistics $U_{(1)} < \dots < U_{(k)}$, let
$$S_i = \min_{t\in[U_{(i)}, U_{(i+1)}]} X_t, \qquad i = 1,\dots,k-1,$$
the time of the most recent common ancestor of neighbouring sampled individuals; the $S_i$ determine the whole sample genealogy.

**Theorem.** For $x_1,\dots,x_{k-1} \in [0,a]$,
$$P(S_1 > x_1,\dots,S_{k-1} > x_{k-1}) = k\int_0^\infty \frac{1}{(1+as)^2}\prod_{i=1}^{k-1}\frac{(a-x_i)s}{1 + (a-x_i)s}\,ds - k\int_0^\infty\frac{1-a}{(1+as)^2}\prod_{i=1}^{k-1}\frac{(a-x_i)s}{1 - x_i + (a-x_i)s}\,ds,$$
with the corresponding joint density obtained by differentiation, e.g. the first term contributes $k\int_0^\infty (1+as)^{-2}\prod_i s(1+(a-x_i)s)^{-2}\,ds$.

For $a = 1$ the second term vanishes and the formula gives the limiting law of the rescaled split times $(S_1(t)/t,\dots,S_{k-1}(t)/t)$ of $k$ particles sampled uniformly at time $t$ from a critical continuous-time Galton–Watson process conditioned on $N_t \ge k$ (Harris, Johnston and Roberts); for general $a$ it is the "sampling in the past" analogue of the result of Harris, Horton, Kyprianou and Powell for two particles sampled at times $at$ and $t$.

## Expansion

Itô's excursion theory: the excursions of $X$ above level $a$, indexed by local time at $a$, form a Poisson point process, and the excursions below $a$ between successive visits to $a$ are independent. Under the sampling, the local-time gaps between consecutive sampled points are spacings of uniforms on $[0, L^a_\infty]$, while $L^a_\infty$ itself is exponential (for the excursion conditioned to exceed $a$). The event $S_i > x_i$ says that no excursion below $a$ reaching down to $x_i$ starts in the $i$-th local-time gap; by the Poisson property this has probability $e^{-\theta_i \ell_i}$, where $\ell_i$ is the local-time length of the gap and $\theta_i$, proportional to $1/(a-x_i)$, is the excursion-measure rate of excursions below $a$ of depth at least $a - x_i$. Averaging over exponential-uniform spacings gives the joint Laplace transform $E\prod_i e^{-\theta_i(L_{i+1}-L_i)}$, which produces the products $\frac{(a-x_i)s}{1+(a-x_i)s}$ after the substitution $s$ for the exponential scale; the second term corrects for conditioning the excursion to reach level $1$, which involves the competing exponential rate of upward excursions from $a$ to $1$.

## Sources

- Sergey Bocharov and Simon C. Harris, "Sample genealogies within a Brownian excursion", arXiv:2609.06291 (2026), main theorem, the exponential-spacing propositions and the comparison with the Harris–Johnston–Roberts and Harris–Horton–Kyprianou–Powell theorems, <https://doi.org/10.48550/arXiv.2609.06291>.
