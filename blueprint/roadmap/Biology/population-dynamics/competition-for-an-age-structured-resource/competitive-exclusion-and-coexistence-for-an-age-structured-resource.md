# Competitive exclusion and coexistence for an age-structured resource

A resource of density $x(t,a)$ in age $a \ge 0$ is produced at constant rate $\Lambda$ and consumed by two competitors $y_1(t), y_2(t)$:

$$

\begin{aligned}
\partial_t x + \partial_a x &= -\mu_x(a)\,x - x\,\big(\beta_1(a) y_1 + \beta_2(a) y_2\big), \qquad x(t,0) = \Lambda,\\
y_i' &= y_i\Big(c_i \int_0^\infty \beta_i(a)\,x(t,a)\,da - \mu_i\Big), \qquad i = 1,2,
\end{aligned}

$$

with $\mu_x, \beta_1, \beta_2 \in L^\infty(\mathbb{R}_+,\mathbb{R}_+)$, $\mu_x \ge \mu_0 > 0$, and $\Lambda, \mu_i, c_i > 0$. The system defines a continuous semiflow on $L^1_+ \times \mathbb{R}_+^2$ with a compact global attractor.

**Thresholds.** Let $x_0^*(a) = \Lambda e^{-\int_0^a \mu_x}$ be the resource-only equilibrium and

$$

\mathcal R_{0,i} = \frac{c_i}{\mu_i}\int_0^\infty \beta_i(a)\,x_0^*(a)\,da .

$$

If $\mathcal R_{0,i} > 1$ there is a unique single-competitor equilibrium $E_i$ with $x_i^*(a) = x_0^*(a)\,e^{-y_i^*\int_0^a\beta_i}$, where $y_i^* > 0$ solves $\frac{c_i}{\mu_i}\int_0^\infty \beta_i x_i^* = 1$. The **invasion fitness** of competitor $j$ into $E_i$ is

$$

\gamma_{i\to j} = \frac{c_j}{\mu_j}\int_0^\infty \beta_j(a)\,x_i^*(a)\,da \;\le\; \mathcal R_{0,j}.

$$

**Theorem.** Starting from initial data with both competitors present:

1. If $\max_i \mathcal R_{0,i} \le 1$, the competitor-free equilibrium $E_0$ is globally asymptotically stable.
2. If $\mathcal R_{0,i} > 1 \ge \mathcal R_{0,j}$, then $E_i$ is globally asymptotically stable.
3. If $\min_k \mathcal R_{0,k} > 1$, $\gamma_{j\to i} > 1$ and $\gamma_{i\to j} \le 1$, then $E_i$ is globally asymptotically stable (competitive exclusion of $j$).
4. If $\min_k \mathcal R_{0,k} > 1$ and $\gamma_{1\to 2} > 1$, $\gamma_{2\to 1} > 1$, there is a unique positive equilibrium $E_3$, and it is globally asymptotically stable (coexistence).
5. If $\min_k \mathcal R_{0,k} > 1$ and $\gamma_{1\to 2} = \gamma_{2\to 1} = 1$ (equivalently $c_2\mu_1\beta_2 = c_1\mu_2\beta_1$ a.e.), the segment of equilibria joining $E_1$ and $E_2$ is globally asymptotically stable, and each orbit converges to the point $(1-\sigma)E_1 + \sigma E_2$ with $\sigma \in (0,1)$ the unique solution of $(1-\sigma)y_1^* = \frac{y_1(0)}{y_2(0)}(\sigma y_2^*)^{\mu_1/\mu_2}$.

The cases $\gamma_{1\to 2} < 1$ and $\gamma_{2\to 1} < 1$ simultaneously, or one equal to $1$ and the other below $1$, cannot occur. Coexistence therefore requires the two kernels to target sufficiently different resource ages, which is impossible when the resource is unstructured.

## Expansion

Well-posedness uses integrated semigroups for the age-transport operator with boundary condition $x(t,0) = \Lambda$. Global stability is proved with Volterra-type Lyapunov functionals of the form $\int \phi(a)\,g(x(a)/x^*(a))\,da + \sum_i k_i\,g(y_i/y_i^*)$ with $g(u) = u - 1 - \log u$, defined on complete bounded orbits in the attractor, together with uniform persistence and a generalized LaSalle invariance principle. In the critical case the quantity $y_1^{1/\mu_1}\,y_2^{-1/\mu_2}$ is conserved along orbits on the resource equilibrium, which pins down the limit point on the segment.

## Sources

- Simon Girel, Quentin Richard, "Competitive exclusion and coexistence in a model with age-structured resource", arXiv (2026). Section 2 (Assumption 2.1, Proposition 2.4, Corollary 2.5), Section 3 (Propositions 3.1–3.3, Theorems 3.5–3.8). <https://doi.org/10.48550/arXiv.2607.11247>
