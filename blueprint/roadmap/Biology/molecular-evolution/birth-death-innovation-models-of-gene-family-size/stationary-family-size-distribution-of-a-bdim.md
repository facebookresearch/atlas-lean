# Stationary family-size distribution and power-law asymptotics of a BDIM

**Model.** Let $p_i(t)$ be the frequency of gene families of size $i \in \{0,1,\dots,N\}$, with per-family birth (duplication) rates $\lambda_i > 0$ for $i < N$ and death (loss) rates $\delta_i > 0$ for $i \ge 1$; the class $0$ represents the source of innovations. The forward equations are
$$\dot p_0 = -\lambda_0 p_0 + \delta_1 p_1,\qquad \dot p_i = \lambda_{i-1}p_{i-1} - (\lambda_i + \delta_i)p_i + \delta_{i+1}p_{i+1}\ (0<i<N),\qquad \dot p_N = \lambda_{N-1}p_{N-1} - \delta_N p_N .$$

**Stationary distribution.** The chain has a unique stationary distribution, globally attracting and approached exponentially fast, given by detailed balance
$$\frac{p_i}{p_{i-1}} = \chi(i) := \frac{\lambda_{i-1}}{\delta_i},\qquad p_i = p_0\prod_{k=1}^{i}\chi(k).$$

**Asymptotics.** If for large $i$
$$\chi(i) = i^{s}\,\theta\left(1 - \frac{\gamma}{i} + O(i^{-2})\right),$$
the model is *first-order balanced* when $s = 0$, giving $p_i \sim c\,\theta^i i^{-\gamma}$, and *second-order balanced* when $s = 0$ and $\theta = 1$, giving the power law $p_i \sim c\,i^{-\gamma}$.

**Examples.** For the linear BDIM $\lambda_i = \lambda(i+a)$, $\delta_i = \delta(i+b)$, one has $\theta = \lambda/\delta$ and $\gamma = 1 + b - a$. For the quadratic BDIM $\lambda_i = \lambda(i^2 + r_1 i + r_2)$, $\delta_i = \delta(i^2 + q_1 i + q_2)$, one has $\chi(i) = \theta\big(1 + (r_1 - q_1 - 2)/i + O(i^{-2})\big)$, so a second-order balanced quadratic BDIM has $p_i \sim c\,i^{\rho-2}$ with $\rho = r_1 - q_1$, independent of $r_2$ and $q_2$. If birth and death rates are polynomials of different degrees the model is not balanced and the stationary frequencies have no power-law tail.

## Expansion

On a finite state space with reflecting ends the probability current $J(i) = \delta_i p_i - \lambda_{i-1}p_{i-1}$ is constant at stationarity and vanishes at the boundary, so it vanishes everywhere, giving the product formula. Taking logarithms, $\log p_i = \log p_0 + \sum_{k\le i}\log\chi(k) = i\log\theta - \gamma\log i + O(1)$ when $s = 0$, which yields both asymptotic regimes. For the linear model $\chi(i) = \theta(i-1+a)/(i+b) = \theta\big(1 - (1+b-a)/i + O(i^{-2})\big)$. Rational rate laws, for example a birth rate that peaks at an intermediate family size, have the same classification.

## Sources

- Karev GP, Wolf YI, Berezovskaya FS, Koonin EV, "Gene family evolution: an in-depth theoretical and simulation analysis of non-linear birth-death-innovation models", BMC Evol Biol (2004), Section 1, Eqs. (1.1)–(1.5), and Section 2, Eqs. (2.1)–(2.3), <https://doi.org/10.1186/1471-2148-4-32>, PMCID PMC523855.
