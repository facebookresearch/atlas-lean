# Nonlinear environmental noise allows two species to coexist on one resource

For a Markov process $X$ of species densities, species $j$ is *persistent in probability* if for every $\varepsilon > 0$ there is $\delta > 0$ with $\liminf_{t \to \infty} \mathbb{P}_y\{X_j(t) > \delta\} \ge 1 - \varepsilon$ for all $y \in (0, \infty)^n$; the species *coexist* if all are persistent in probability. For the SDE $dx_i = x_i f_i(x)\,dt + x_i g_i(x)\,dE_i$ and an invariant probability measure $\mu$ of a subcommunity on the boundary, the invasion rate of species $i$ is

$$\Lambda_i(\mu) = \int_{\partial \mathbb{R}^n_+} \Big( f_i(x) - \frac{g_i^2(x)\sigma_{ii}}{2} \Big)\, \mu(dx).$$

**Coexistence criterion.** If species 1 alone survives with a unique invariant measure $\mu_1$ on $(0, \infty)$, species 2 alone survives with a unique invariant measure $\mu_2$, and both invasion rates $\Lambda_1(\mu_2) > 0$, $\Lambda_2(\mu_1) > 0$, then the two species coexist.

**Theorem.** Let two species share one resource $R(x) = \bar R - a_1 x_1 - a_2 x_2$ with $a_i > 0$, and

$$dx_i(t) = x_i(t)\big(-\alpha_i + b_i R(x(t))\big)dt + x_i(t)\sqrt{\beta_i x_i(t)}\, dB_i(t), \qquad i = 1, 2,$$

with independent Brownian motions $B_1, B_2$ and $\beta_i > 0$.

1. If $b_i \bar R > \alpha_i$ for $i = 1, 2$, each species survives on its own and has a unique invariant probability measure $\mu_i$ on $(0, \infty)$.
2. If moreover

$$\Lambda_{x_2} = (b_2 \bar R - \alpha_2) - b_2 a_1 \frac{b_1 \bar R - \alpha_1}{b_1 a_1 + \beta_1} > 0 \quad \text{and} \quad \Lambda_{x_1} = (b_1 \bar R - \alpha_1) - b_1 a_2 \frac{b_2 \bar R - \alpha_2}{b_2 a_2 + \beta_2} > 0,$$

then the two species coexist, although they compete for a single resource.

## Depends on

- [Competitive exclusion persists under linear environmental white noise](stochastic-competitive-exclusion-with-linear-white-noise.md)

## Expansion

Alone, species 1 follows $dx = x(b_1\bar R - \alpha_1 - b_1 a_1 x)\,dt + x\sqrt{\beta_1 x}\, dB_1$, which has a unique invariant measure $\mu_1$ on $(0, \infty)$ when $b_1 \bar R > \alpha_1$. The paper uses the stationarity identity $\int_0^\infty (-\alpha_1 + b_1(\bar R - a_1 x) - \beta_1 x)\, \mu_1(dx) = 0$, giving $\int x\, \mu_1(dx) = (b_1 \bar R - \alpha_1)/(b_1 a_1 + \beta_1)$. The invasion rate of species 2 is its per-capita growth $-\alpha_2 + b_2(\bar R - a_1 x)$ averaged against $\mu_1$ (its own noise vanishes at $x_2 = 0$), which yields the displayed $\Lambda_{x_2}$; $\Lambda_{x_1}$ is symmetric. Both are positive once $\beta_1 > b_2 a_1 (b_1 \bar R - \alpha_1)/(b_2 \bar R - \alpha_2) - b_1 a_1$ and $\beta_2 > b_1 a_2 (b_2 \bar R - \alpha_2)/(b_1 \bar R - \alpha_1) - b_2 a_2$. Density-dependent noise lowers each resident's mean density below the deterministic level $(b_i \bar R - \alpha_i)/(b_i a_i)$; this breaks the symmetry that forces one invasion rate to be negative in the linear case. The paper's example $\alpha_1 = 0.5$, $\alpha_2 = 0.6$, $\beta_1 = \beta_2 = 4$, $\bar R = 3$, $a_1 = a_2 = 1$ gives $\Lambda_{x_2} = 1.9$ and $\Lambda_{x_1} = 2.02$.

Formalization note: the Itô correction for the noise $x\sqrt{\beta_1 x}\,dB_1$ is $\beta_1 x/2$, which would replace $\beta_1$ by $\beta_1/2$ in the denominators above. A formal statement should fix this constant from the stationarity identity; the qualitative conclusion (coexistence for all sufficiently large $\beta_1, \beta_2$) holds with either constant.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* (2020), <https://doi.org/10.1007/s00285-019-01464-y>; preprint arXiv:1810.00954. Definition 3.2, Theorem 3.3, equation (4.2), Theorem 4.2, Figure 1, Appendix B.
