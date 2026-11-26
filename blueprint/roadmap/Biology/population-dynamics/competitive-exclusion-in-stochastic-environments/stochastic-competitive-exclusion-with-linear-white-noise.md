# Competitive exclusion persists under linear environmental white noise

Let $n$ species with densities $x_i$ compete for $m$ abiotic resources $R_j(x) = \bar R_j - F_j(x)$, where each $F_j \ge 0$ is unbounded with $F_j(0) = 0$, so that the resources eventually get exhausted. Per-capita growth rates are linear in the resources and the environment fluctuates by white noise:

$$dx_i(t) = x_i(t)\Big(-\alpha_i + \sum_{j=1}^m b_{ij} R_j(x(t))\Big)dt + x_i(t) g_i(x(t))\, dE_i(t), \qquad i = 1, \dots, n,$$

where $E(t) = \Gamma^T B(t)$ for a standard Brownian motion $B$ in $\mathbb{R}^n$ and $\Gamma^T\Gamma = \Sigma = (\sigma_{ij})$.

*At least one species goes extinct* means: there is $\alpha > 0$ such that for every $x(0) \in (0, \infty)^n$, almost surely

$$\limsup_{t \to \infty} \frac{\ln \min_i x_i(t)}{t} \le -\alpha.$$

**Theorem.** If $n > m$ and the noise is linear, $g_i \equiv 1$ for all $i$, then for every $x(0) \in (0, \infty)^n$, with probability one at least one species goes extinct.

**Precise form proved in the appendix.** Assume in addition that $\lim_{\|x\| \to \infty} R_j(x) = -\infty$ and $0 < r_m \le \liminf_{\|x\| \to \infty} |R_j(x)|/|R_1(x)| \le r_M < \infty$ for $j = 1, \dots, m$. Let $c \ne 0$ solve $\sum_{i=1}^n c_i b_{ij} = 0$ for $j = 1, \dots, m$ (such $c$ exists because $n > m$), and suppose $\sum_{i=1}^n c_i (\alpha_i + \sigma_{ii}/2) \ne 0$. Then for every $x(0) \in (0, \infty)^n$, almost surely $\limsup_{t \to \infty} t^{-1} \ln \min_i x_i(t) < 0$.

Linear noise can still change which species wins. For two species on one resource with $\mu_i = -\alpha_i + b_i \bar R$, $\beta_{ij} = b_i a_j$ and $\Sigma = \operatorname{diag}(\sigma_1^2, \sigma_2^2)$, $\mu_i > \sigma_i^2/2$, species 1 wins and species 2 goes extinct almost surely when $\frac{\mu_1}{b_1}\big(1 - \frac{\sigma_1^2}{2\mu_1}\big) > \frac{\mu_2}{b_2}\big(1 - \frac{\sigma_2^2}{2\mu_2}\big)$, and the reverse holds when the inequality is reversed; noise can thus overturn the deterministic winner $\mu_1/b_1 > \mu_2/b_2$.

## Expansion

Since $n > m$, there is a nonzero $c \in \mathbb{R}^n$ with $\sum_i c_i b_{ij} = 0$ for every resource $j$. By Itô's formula, with $g_i \equiv 1$,

$$d \sum_i c_i \ln x_i = -\sum_i c_i \Big(\alpha_i + \frac{\sigma_{ii}}{2}\Big)dt + \sum_i c_i\, dE_i,$$

so the resource terms cancel exactly and $\sum_i c_i \ln x_i(t)$ is a Brownian motion with constant drift. Under the nondegeneracy $\sum_i c_i(\alpha_i + \sigma_{ii}/2) \ne 0$ the drift is nonzero, while the growth conditions on $R_j$ keep the process from escaping to infinity, so some $\ln x_i$ must go to $-\infty$ at a linear rate. The noise raises each effective death rate from $\alpha_i$ to $\alpha_i + \sigma_{ii}/2$, but leaves the linear dependence on resources intact, which is what makes exclusion survive. The deterministic version ($\Sigma = 0$) is the classical principle that $n$ species cannot coexist on $m < n$ resources.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* (2020), <https://doi.org/10.1007/s00285-019-01464-y>; preprint arXiv:1810.00954. Definition 3.1, equation (4.3), Theorem 4.1, Example 4.1, Appendix A.
