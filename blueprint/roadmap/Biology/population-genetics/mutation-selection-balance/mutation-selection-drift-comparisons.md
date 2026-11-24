# Deterministic and stochastic descriptions of mutation–selection balance

In Birkner's two-type Moran model with population size $N$, directional selection $s \ge 0$ in favour of type $A$ and mutation rates $m_A, m_a > 0$ (Definition 3.4.1), the number of type-$A$ individuals is an irreducible birth–death chain, hence reversible with a unique equilibrium distribution, and

$$\pi^{(N)}(k) = \frac{1}{C_N}\binom Nk(1 + s)^k\,\frac{\bigl(\frac{Nm_A}{1 + s}\bigr)_{k\uparrow}\,(Nm_a)_{(N - k)\uparrow}}{\bigl(\frac{Nm_A}{1 + s} + Nm_a\bigr)_{N\uparrow}}, \qquad k = 0, \dots, N,$$

where $(y)_{k\uparrow}$ is the rising factorial and $C_N = E[(1 + s\xi)^N]$ with $\xi \sim \mathrm{Beta}(Nm_A/(1 + s), Nm_a)$ (Theorem 3.4.3(a)). Under the scaling $s = \sigma/N$, $m_A = \theta_A/N$, $m_a = \theta_a/N$, in which selection, mutation and drift act on comparable time scales, the law of $k/N$ converges weakly to the density proportional to $x^{\theta_A - 1}(1 - x)^{\theta_a - 1}e^{\sigma x}$ on $(0, 1)$ (Theorem 3.4.3(b)). The deterministic description of an infinite population is a different regime: for a deleterious allele with heterozygote fitness $1 - hs$, homozygote fitness $1 - s$ and mutation rate $\mu$, the equilibrium frequency is $q \approx \mu/(hs)$ when $h$ is not close to $0$, and $q = \sqrt{\mu/s}$ for a recessive allele (Mutation–selection balance, Wikipedia).

## Depends on

- [Mutation–selection balance in a haploid population](../../../Biology/population-genetics/mutation-selection-balance/haploid-mutation-selection-balance.md)
- [Mutation–selection balance for a recessive allele](../../../Biology/population-genetics/mutation-selection-balance/recessive-mutation-selection-balance.md)
- [Partition function of the selection–mutation stationary density](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-partition.md)

## Expansion

1. The Moran chain with selection and mutation, detailed balance, and the product formula for its equilibrium.
2. The closed form with rising factorials and the normalization $C_N = E[(1 + s\xi)^N]$.
3. The weak limit under $s = \sigma/N$, $m_A = \theta_A/N$, $m_a = \theta_a/N$.
4. The deterministic equilibria $\mu/(hs)$ and $\sqrt{\mu/s}$, and the concentration of the stationary law near the deterministic equilibrium when $N \to \infty$ with $s$ and the mutation rates fixed, as a separate statement with its own source.

## Sources

- M. Birkner, Stochastic population models, lecture notes, Johannes Gutenberg-Universität Mainz, winter 2025/26, Section 3.4, Definition 3.4.1, Observation 3.4.2 and Theorem 3.4.3.
- Mutation–selection balance, Wikipedia, sections Haploid population and Diploid population. <https://en.wikipedia.org/wiki/Mutation%E2%80%93selection_balance>
