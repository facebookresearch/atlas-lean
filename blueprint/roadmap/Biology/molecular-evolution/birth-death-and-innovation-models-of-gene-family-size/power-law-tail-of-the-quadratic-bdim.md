# Power-law tail of the quadratic BDIM

**Setting.** In the stochastic form of the birth, death and innovation model (BDIM), the frequencies $p_0, \dots, p_N$ of gene families of each size follow the forward equations of a birth–death chain on $\{0, 1, \dots, N\}$ with birth (duplication) rates $\lambda_i > 0$ for $i < N$ and death (loss) rates $\delta_i > 0$ for $i \ge 1$, the class $0$ standing for the source of innovations. Its stationary frequencies are the [stationary law of a finite birth–death chain](../../../Probability/markov-chains/birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md), $p_i = p_0 \prod_{k=1}^{i} \chi(k)$ with $\chi(k) = \lambda_{k-1}/\delta_k$. For $i \ge 1$ they are proportional to the equilibrium $f_i = f_1 \prod_{k=2}^{i} \chi(k)$ of the deterministic [master BDIM](equilibrium-of-the-birth-death-and-innovation-model.md) with the same rates, so the classification by [order of balance](order-of-balance-determines-family-size-asymptotics.md) applies to them unchanged. Write $q_i \sim r_i$ when $q_i/r_i$ tends to a constant in $(0, \infty)$.

**Theorem (quadratic BDIM).** Let $\lambda_i = \lambda\,(i^2 + r_1 i + r_2)$ and $\delta_i = \delta\,(i^2 + q_1 i + q_2)$ with $\lambda, \delta > 0$ and all these rates positive, and put $\theta = \lambda/\delta$ and $\rho = r_1 - q_1$. Then

$$\chi(i) = \theta\left(1 + \frac{\rho - 2}{i} + O\!\left(\frac{1}{i^2}\right)\right),$$

so as $i \to \infty$ (for $N$ large) $p_i \sim \theta^{i}\, i^{\rho - 2}$. In particular, when $\lambda = \delta$ the stationary frequencies follow the power law $p_i \sim i^{\rho - 2}$, whose exponent does not depend on $r_2$ and $q_2$.

If the birth and death rates are polynomials in $i$ of different degrees, then $\chi(i) \sim i^{s}$ with $s \ne 0$, the model is non-balanced and the stationary frequencies have no power-law tail.

## Depends on

- [Stationary law of a finite birth–death chain](../../../Probability/markov-chains/birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md)
- [Equilibrium of the birth, death and innovation model](equilibrium-of-the-birth-death-and-innovation-model.md)

## Proof depends on

- [Order of balance determines family-size asymptotics](order-of-balance-determines-family-size-asymptotics.md)

## Expansion

$\chi(i) = \lambda\big((i-1)^2 + r_1(i-1) + r_2\big)/\big(\delta(i^2 + q_1 i + q_2)\big) = \theta\,\big(i^2 + (r_1 - 2) i + O(1)\big)/\big(i^2 + q_1 i + O(1)\big)$, which expands as stated. In the notation of the order-of-balance theorem, $s = 0$ and $a = \rho - 2$: the model is first-order balanced when $\theta \ne 1$, and second-order (or, when $\rho = 2$, high-order) balanced when $\theta = 1$; in every case $p_i \sim \theta^i i^{\rho-2}$. For polynomial rates of degrees $d_\lambda \ne d_\delta$, $\chi(i) \sim i^{d_\lambda - d_\delta}$, the non-balanced case, with hyper-exponential growth or decay. The source uses the same expansion for rational rate laws, for example a birth rate that peaks at an intermediate family size.

## Sources

- G. P. Karev, Y. I. Wolf, F. S. Berezovskaya and E. V. Koonin, "Gene family evolution: an in-depth theoretical and simulation analysis of non-linear birth-death-innovation models", BMC Evolutionary Biology 4 (2004) 32, Section 1, Eqs. (1.1)–(1.5), and Section 2, Eqs. (2.1)–(2.3), <https://doi.org/10.1186/1471-2148-4-32>, PMCID PMC523855.
