# Nonlinear environmental noise allows two species to coexist on one resource

For a Markov process $X$ of species densities, species $j$ is *persistent in probability* if for every $\varepsilon > 0$ there is $\delta > 0$ with $\liminf_{t \to \infty} \mathbb{P}_y\{X_j(t) > \delta\} \ge 1 - \varepsilon$ for all $y \in (0, \infty)^n$; the species *coexist* if all are persistent in probability. For the Itô SDE $dx_i = x_i f_i(x)\,dt + x_i g_i(x)\,dE_i$ with $E = \Gamma^{\mathsf T} B$, $\Gamma^{\mathsf T}\Gamma = \Sigma = (\sigma_{ij})$, and an invariant probability measure $\mu$ supported on the boundary $\partial \mathbb{R}^n_+ = [0,\infty)^n \setminus (0,\infty)^n$, the invasion rate of species $i$ is

$$\Lambda_i(\mu) = \int_{\partial \mathbb{R}^n_+} \Big( f_i(x) - \frac{g_i^2(x)\sigma_{ii}}{2} \Big)\, \mu(dx).$$

**Theorem.** Let two species share one resource $R(x) = \bar R - a_1 x_1 - a_2 x_2$ with $\bar R > 0$, $a_i > 0$, $b_i > 0$, $\alpha_i \ge 0$, and

$$dx_i(t) = x_i(t)\big(-\alpha_i + b_i R(x(t))\big)dt + x_i(t)\sqrt{\beta_i x_i(t)}\, dB_i(t), \qquad i = 1, 2,$$

with independent standard Brownian motions $B_1, B_2$ and $\beta_i > 0$, so that $f_i = -\alpha_i + b_i R$, $g_i(x) = \sqrt{\beta_i x_i}$ and $\Sigma = I$.

1. If $b_i \bar R > \alpha_i$ for $i = 1, 2$, each species survives on its own and has a unique invariant probability measure $\mu_i$ on $(0, \infty)$. The ergodic invariant probability measures of the two-species process supported on $\partial\mathbb{R}^2_+$ are then exactly $\delta_{(0,0)}$, $\mu_1 \otimes \delta_0$ and $\delta_0 \otimes \mu_2$.
2. If moreover

$$\Lambda_{x_2} = (b_2 \bar R - \alpha_2) - b_2 a_1 \frac{b_1 \bar R - \alpha_1}{b_1 a_1 + \beta_1/2} > 0 \quad \text{and} \quad \Lambda_{x_1} = (b_1 \bar R - \alpha_1) - b_1 a_2 \frac{b_2 \bar R - \alpha_2}{b_2 a_2 + \beta_2/2} > 0,$$

then the two species coexist, although they compete for a single resource.

Here $\Lambda_{x_2} = \Lambda_2(\mu_1 \otimes \delta_0)$ and $\Lambda_{x_1} = \Lambda_1(\delta_0 \otimes \mu_2)$. At the origin both invasion rates are $\Lambda_i(\delta_{(0,0)}) = b_i \bar R - \alpha_i > 0$, since $g_i$ vanishes there. Thus every ergodic boundary measure, and hence every convex combination of them, has a species with positive invasion rate, which is the hypothesis of the persistence theorem for stochastic Kolmogorov systems (Hening and Nguyen 2018, Theorem 4.1 and Example 2.4) that the source invokes; its regularity and dissipativity assumptions are checked for this system in Appendix B of the source. In the two-species form used by the source (published Theorem 3.1), the criterion reads: if each species alone has a unique invariant measure $\mu_i$ on $(0,\infty)$ and $\Lambda_1(\mu_2) > 0$, $\Lambda_2(\mu_1) > 0$, the species coexist; for this model the positive invasion rates at the origin and the regularity checks above are what make that criterion applicable.

## Expansion

Alone, species 1 follows $dx = x(b_1\bar R - \alpha_1 - b_1 a_1 x)\,dt + x\sqrt{\beta_1 x}\, dB_1$, which has a unique invariant measure $\mu_1$ on $(0, \infty)$ when $b_1 \bar R > \alpha_1$, and the boundary of the half-line carries only $\delta_0$. Along $\mu_1$ the long-run growth rate of $\log x$ is zero, and by Itô's formula its drift is $b_1\bar R - \alpha_1 - b_1 a_1 x - \beta_1 x/2$. The stationarity identity is therefore $\int_0^\infty (b_1\bar R - \alpha_1 - b_1 a_1 x - \beta_1 x/2)\, \mu_1(dx) = 0$, giving $\int x\, \mu_1(dx) = (b_1 \bar R - \alpha_1)/(b_1 a_1 + \beta_1/2)$. The invasion rate of species 2 is its per-capita growth $-\alpha_2 + b_2(\bar R - a_1 x)$ averaged against $\mu_1$ (its own noise vanishes at $x_2 = 0$), which yields the displayed $\Lambda_{x_2}$; $\Lambda_{x_1}$ is symmetric. Both are positive once $\beta_1 > 2\big(b_2 a_1 (b_1 \bar R - \alpha_1)/(b_2 \bar R - \alpha_2) - b_1 a_1\big)$ and $\beta_2 > 2\big(b_1 a_2 (b_2 \bar R - \alpha_2)/(b_1 \bar R - \alpha_1) - b_2 a_2\big)$, so coexistence holds for all sufficiently large $\beta_1, \beta_2$. Density-dependent noise lowers each resident's mean density below the deterministic level $(b_i \bar R - \alpha_i)/(b_i a_i)$; this breaks the symmetry that forces one invasion rate to be negative when the noise is linear, as on [competitive exclusion under linear white noise](stochastic-competitive-exclusion-with-linear-white-noise.md), which is a comparison and not a prerequisite.

The source writes the denominators as $b_i a_i + \beta_i$, dropping the factor $1/2$ of the Itô correction $g_i^2/2 = \beta_i x_i/2$. That changes signs in examples: with $a_i = b_i = \beta_i = 1$, $b_1\bar R - \alpha_1 = 1$ and $b_2\bar R - \alpha_2 = 0.6$, the source's formula gives $\Lambda_{x_2} = 0.1 > 0$, whereas the SDE above gives $\Lambda_{x_2} = 0.6 - 2/3 < 0$. For the source's Figure 1 parameters $\alpha_1 = 0.5$, $\alpha_2 = 0.6$, $\beta_1 = \beta_2 = 4$, $\bar R = 3$, $a_1 = a_2 = 1$, $b_1 = b_2 = 1$, the corrected rates are $\Lambda_{x_2} = 2.4 - 2.5/3 = 47/30 \approx 1.567$ and $\Lambda_{x_1} = 2.5 - 2.4/3 = 1.7$ (the source reports $1.9$ and $2.02$ from its denominators); both remain positive, so the example still exhibits coexistence.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* 80 (2020), 1323–1351, <https://doi.org/10.1007/s00285-019-01464-y>. The coexistence criterion is published Theorem 3.1 (Theorem 3.3 of the preprint arXiv:1810.00954). Other locators follow the preprint: Definition 3.2, equation (4.2), Theorem 4.2, Figure 1, Appendix B.
- A. Hening and D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, *Ann. Appl. Probab.* 28 (2018), 1893–1942, <https://doi.org/10.1214/17-AAP1347>. Theorem 4.1 and Example 2.4, as cited by the first source.
