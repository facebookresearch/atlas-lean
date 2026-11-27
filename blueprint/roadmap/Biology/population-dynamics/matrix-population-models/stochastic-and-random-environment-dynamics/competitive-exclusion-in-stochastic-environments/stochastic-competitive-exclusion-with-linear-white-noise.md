# Competitive exclusion persists under linear environmental white noise

Let $n$ species with densities $x_i$ compete for $m$ abiotic resources $R_j(x) = \bar R_j - F_j(x)$, where each $F_j \ge 0$ is unbounded with $F_j(0) = 0$, so that the resources eventually get exhausted. Per-capita growth rates are linear in the resources and the environment fluctuates by white noise:

$$dx_i(t) = x_i(t)\Big(-\alpha_i + \sum_{j=1}^m b_{ij} R_j(x(t))\Big)dt + x_i(t) g_i(x(t))\, dE_i(t), \qquad i = 1, \dots, n,$$

where $E(t) = \Gamma^T B(t)$ for a standard Brownian motion $B$ in $\mathbb{R}^n$ and $\Gamma^T\Gamma = \Sigma = (\sigma_{ij})$.

*At least one species goes extinct* means: there is $\alpha > 0$ such that for every $x(0) \in (0, \infty)^n$, almost surely

$$\limsup_{t \to \infty} \frac{\ln \min_i x_i(t)}{t} \le -\alpha.$$

**Theorem.** Suppose $n > m$, the noise is linear ($g_i \equiv 1$ for all $i$), $b_{ij} \ge 0$ with $\sum_j b_{ij} > 0$ for every $i$, each $R_j$ satisfies $\lim_{\|x\| \to \infty} R_j(x) = -\infty$, and

$$0 < r_m \le \liminf_{\|x\| \to \infty} \frac{|R_j(x)|}{|R_1(x)|} \le r_M < \infty, \qquad j = 1, \dots, m.$$

Let $c \ne 0$ solve $\sum_{i=1}^n c_i b_{ij} = 0$ for $j = 1, \dots, m$ (such $c$ exists because $n > m$), and assume the corrected drift in this resource-null direction is nonzero:

$$K := \Big|\sum_{i=1}^n c_i \Big(\alpha_i + \frac{\sigma_{ii}}{2}\Big)\Big| > 0.$$

Replace $c$ by $-c$ if needed so that $\sum_i c_i(\alpha_i + \sigma_{ii}/2) = K$. Then $\sum_{i : c_i > 0} c_i > 0$, and for every $x(0) \in (0, \infty)^n$, almost surely

$$\limsup_{t \to \infty} \frac{\ln \min_i x_i(t)}{t} \le -\alpha, \qquad \alpha = \frac{K}{\sum_{i : c_i > 0} c_i} > 0;$$

that is, at least one species goes extinct. The conclusion bounds the minimum density; it does not say which species is lost, which can depend on the path.

The nondegeneracy $K > 0$ cannot be dropped. For $n = 2$, $m = 1$, $R = 2 - x_1 - x_2$, $\alpha_i = 0$, $b_{i1} = 1$ and $\Sigma = 0$, the null vector is $c = (1, -1)$, $K = 0$, and $(1/2, 1/2)$ is a positive equilibrium: neither species disappears.

Linear noise can still change which species wins. For two species on one resource $R = \bar R - a_1x_1 - a_2x_2$ with $a_j, b_i > 0$, $\mu_i = -\alpha_i + b_i \bar R$, $\beta_{ij} = b_i a_j$ and $\Sigma = \operatorname{diag}(\sigma_1^2, \sigma_2^2)$, $\mu_i > \sigma_i^2/2$, species 1 wins and species 2 goes extinct almost surely when $\frac{\mu_1}{b_1}\big(1 - \frac{\sigma_1^2}{2\mu_1}\big) > \frac{\mu_2}{b_2}\big(1 - \frac{\sigma_2^2}{2\mu_2}\big)$, and the reverse holds when the inequality is reversed; noise can thus overturn the deterministic winner $\mu_1/b_1 > \mu_2/b_2$.

## Expansion

Since $n > m$, there is a nonzero $c \in \mathbb{R}^n$ with $\sum_i c_i b_{ij} = 0$ for every resource $j$. By Itô's formula, with $g_i \equiv 1$,

$$d \sum_i c_i \ln x_i = -\sum_i c_i \Big(\alpha_i + \frac{\sigma_{ii}}{2}\Big)dt + \sum_i c_i\, dE_i,$$

so the resource terms cancel exactly and $\sum_i c_i \ln x_i(t)$ is a Brownian motion with constant drift $-K$, whence $t^{-1}\sum_i c_i \ln x_i(t) \to -K$ almost surely. The growth conditions on $R_j$ and $b_{ij}$ give a Lyapunov bound that keeps the process from escaping to infinity, $\limsup_{t\to\infty} t^{-1}\ln\|x(t)\| \le 0$ almost surely (Appendix A, equation (A.2), via Hening and Nguyen 2018). Hence $\sum_{c_i > 0} c_i \ln x_i(t) \le -Kt + \sum_{c_i < 0} |c_i| \ln x_i(t) \le -Kt + o(t)$; in particular some $c_i$ is positive, and since $\ln \min_k x_k \le \ln x_i$ for each $i$, $\big(\sum_{c_i > 0} c_i\big)\ln \min_k x_k(t) \le -Kt + o(t)$, which is the stated bound. The noise raises each effective death rate from $\alpha_i$ to $\alpha_i + \sigma_{ii}/2$, but leaves the linear dependence on resources intact, which is what makes exclusion survive. The deterministic version ($\Sigma = 0$, with the same nondegeneracy $\sum_i c_i \alpha_i \ne 0$) is the classical principle that $n$ species cannot coexist on $m < n$ resources.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* 80 (2020), 1323–1351, <https://doi.org/10.1007/s00285-019-01464-y>; preprint arXiv:1810.00954. Locators follow the preprint: Definition 3.1, equation (4.3), Theorem 4.1, Example 4.1, Appendix A (Theorem A.1).
