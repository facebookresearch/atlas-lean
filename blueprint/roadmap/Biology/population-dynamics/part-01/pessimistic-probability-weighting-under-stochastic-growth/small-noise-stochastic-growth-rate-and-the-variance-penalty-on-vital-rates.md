# Small-noise stochastic growth rate and the variance penalty on vital rates

**Setting.** An age-structured population with $M$ age classes is projected by a random sequence of nonnegative Leslie matrices $\mathbf A_1, \mathbf A_2, \dots$, one per time step, each with age-specific fertilities $F_j$ on the first row and survival probabilities $P_j$ on the subdiagonal. Let $\tilde{\mathbf A} = \mathbb E[\mathbf A]$ be the mean matrix, assumed irreducible and primitive, with dominant eigenvalue $\tilde\lambda$, right eigenvector $\tilde\omega$ (stable age distribution) and left eigenvector $\tilde\nu$ (reproductive values). The fitness of a genotype is the rate of exponential growth

$$a = \lim_{n \to \infty} \frac{1}{n} \log \big\lvert \mathbf A_n \cdots \mathbf A_1\, \zeta \big\rvert$$

for any nonnegative nonzero initial age vector $\zeta$; under weak ergodicity the limit does not depend on $\zeta$, and a resident homozygote resists invasion by a mutant allele when its $a$ exceeds that of the heterozygote.

**Small-noise approximation.** For fluctuations of the matrix entries that are small relative to their means and serially uncorrelated,

$$a \approx \log \tilde\lambda - \frac{1}{2 \tilde\lambda^2 (\tilde\nu^{\mathsf T} \tilde\omega)^2}\, (\tilde\nu \otimes \tilde\nu)^{\mathsf T}\, \mathbf C\, (\tilde\omega \otimes \tilde\omega),$$

where $\mathbf C$ is the covariance matrix of the vectorized entries of $\mathbf A$. If only one entry $A_{ij}$ fluctuates, with variance $\sigma_{ij}^2$,

$$a \approx \log \tilde\lambda - \frac{1}{2 \tilde\lambda^2} \Big( \frac{\partial \tilde\lambda}{\partial A_{ij}} \Big)^2 \sigma_{ij}^2, \qquad \frac{\partial \tilde\lambda}{\partial A_{ij}} = \tilde\nu_i \tilde\omega_j \quad (\tilde\nu^{\mathsf T}\tilde\omega = 1).$$

**Variance penalty.** Hold the mean matrix fixed. Since the correction term is nonpositive and vanishes only when $\sigma_{ij} = 0$ (given $\partial\tilde\lambda/\partial A_{ij} \ne 0$), among strategies with the same mean value of a vital rate, fitness strictly decreases with its variance. For example, three fertility lotteries with common mean $1.5$ and standard deviations $0$, $0.5$ and $1$ have strictly decreasing fitness in that order.

## Expansion

Growth is multiplicative, so the long-run rate is a time average of logarithms of one-step growth factors and, by concavity of $\log$, lies below the logarithm of the mean growth factor: the matrix form of the geometric-mean principle. Expanding $\log \lambda$ to second order around $\tilde{\mathbf A}$ along the stochastic sequence, first-order terms average to zero and the second-order term gives the variance of $\lambda$ under the perturbation, $\sum (\partial \lambda/\partial A_{ij})(\partial\lambda/\partial A_{kl}) \operatorname{Cov}(A_{ij}, A_{kl})$, divided by $2\tilde\lambda^2$. The eigenvalue sensitivity $\tilde\nu_i\tilde\omega_j/\tilde\nu^{\mathsf T}\tilde\omega$ turns this into the Kronecker quadratic form. The full approximation also contains a serial autocorrelation term, omitted here. A severe shortfall in one period cannot be offset by good periods because survival multiplies across periods, which is why near-zero outcomes dominate the penalty.

## Depends on

- [Leslie matrix](../../leslie-matrix-model/leslie-matrix.md)
- [Sensitivity of the population growth rate to matrix entries](../../matrix-population-models/eigenvalue-sensitivity-formula.md)

## Sources

- M. H. Price, J. H. Jones, "Fitness-maximizers employ pessimistic probability weighting for decisions under risk", Evolutionary Human Sciences 2 (2020) e28, Section 5, Eqs (6)–(13), the sensitivity formula following Eq (13), and Table 1, <https://doi.org/10.1017/ehs.2020.28>, PMCID PMC10427448.
- S. D. Tuljapurkar, "Population dynamics in variable environments. III. Evolutionary dynamics of r-selection", Theoretical Population Biology 21 (1982) 141–165, the original small-noise approximation, <https://doi.org/10.1016/0040-5809(82)90010-7>.
