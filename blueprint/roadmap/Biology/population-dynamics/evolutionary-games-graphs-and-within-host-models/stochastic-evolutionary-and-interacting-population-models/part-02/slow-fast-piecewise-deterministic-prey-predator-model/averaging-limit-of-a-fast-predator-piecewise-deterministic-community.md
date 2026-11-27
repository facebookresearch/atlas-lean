# Averaging limit of a prey–predator community with fast deterministic predators

**Model.** The community state is $Z_t = (N_t, H_t) \in \mathbb N^* \times \mathbb R_+$: a discrete prey population $N_t \ge 1$ and a continuous predator density $H_t$. Fix positive parameters $b, d, c, B, r, D, C$ and a scale $\varepsilon \in (0,1]$. Between prey jumps the predator density follows

$$\frac{d}{dt} H^\varepsilon_t = \frac{H^\varepsilon_t}{\varepsilon}\big(rB N^\varepsilon_t - D - C H^\varepsilon_t\big),$$

and the prey jumps $n \to n+1$ at rate $bn$ ($n \ge 1$) and $n \to n-1$ at rate $n(d + cn + B H_t)$ ($n \ge 2$). For fixed $n$ the predator flow converges to $h^*_n = \max\{(rBn - D)/C,\,0\}$. The case $\varepsilon = 1$ is the large-population limit of an individual-based model with many small predators; small $\varepsilon$ encodes predators whose metabolic rates scale like the inverse of their mass.

**Theorem (averaging).** Assume $rB - D > 0$ and initial conditions in $E' = \mathbb N^* \times [h^*_1, \infty)$, converging in law to $\bar Z_0$ as $\varepsilon \to 0$ with $\sup_{\varepsilon} \mathbb E[(N^\varepsilon_0)^4] < \infty$ and $\sup_\varepsilon \mathbb E[(H^\varepsilon_0)^4] < \infty$. Then for every $T > 0$, $N^\varepsilon$ converges in law in $\mathbb D([0,T], \mathbb N)$ to the birth–death process $\bar N$ on $\mathbb N^*$ with generator

$$\mathcal L f(n) = bn\,\big(f(n+1) - f(n)\big) + n\,\big(d + cn + B h^*_n\big)\big(f(n-1) - f(n)\big)\mathbf 1_{n \ge 2},$$

i.e. the prey see the predators only through their quasi-equilibrium $h^*_n$, and the occupation measures of $H^\varepsilon$ converge to the Dirac masses at $h^*_{\bar N}$.

**Proposition (invariant law).** $\bar N$ is positive recurrent on $\mathbb N^*$ with unique invariant law $\bar\mu = \sum_{n \ge 1} \mu_n \delta_n$,

$$\mu_n = \frac{b^{n-1}}{n \prod_{i=2}^{n}\big(d + ci + B h^*_i\big)}\,\mu_1 \quad (n \ge 2),$$

so $\bar Z = (\bar N, h^*_{\bar N})$ has the unique invariant law $\sum_n \mu_n \delta_{(n, h^*_n)}$; its mode is at $n = 1$ if $\mu_1 \ge \mu_2$ and at an explicit $n_1 > 1$ otherwise.

## Expansion

Under $rB > D$ and $h \ge h^*_1$ the predator never approaches $0$, and the flow contracts uniformly: $|\phi^\varepsilon_n(h,t) - h^*_n| \le |h - h^*_n|\,e^{-\delta t/\varepsilon}$ for some $\delta > 0$. Between prey jumps (which occur on an $O(1)$ time scale) the predator therefore relaxes to $h^*_n$ in time $O(\varepsilon)$. Tightness of $(N^\varepsilon, \Gamma^\varepsilon)$, with $\Gamma^\varepsilon$ the occupation measure of the predator, follows from the fourth-moment bounds, and identifying the limit martingale problem gives the averaged generator (a Kurtz-type averaging argument). The invariant law follows from detailed balance $\mu_n\,n(d + cn + Bh^*_n) = \mu_{n-1}\,b(n-1)$; the quadratic competition term $cn$ makes the series summable.

The paper's exponential-ergodicity statement for the unscaled process ($\varepsilon = 1$, its Theorem 2.2) is flagged by the author's December 2025 erratum as incorrectly stated and is not used here.

## Sources

- Manon Costa, "A piecewise deterministic model for a prey-predator community", arXiv (2015); Annals of Applied Probability 26 (2016). Equations of Section 2.1, Theorem 2.5 (individual-based limit), Proposition 4.1, Theorem 4.2, Proposition 4.4, Corollary 4.5, Proposition 4.6. <https://doi.org/10.48550/arXiv.1503.02492>. Published version: The Annals of Applied Probability 26(6) (2016), 3491–3530, <https://doi.org/10.1214/16-aap1182>; locators above refer to the arXiv version.
