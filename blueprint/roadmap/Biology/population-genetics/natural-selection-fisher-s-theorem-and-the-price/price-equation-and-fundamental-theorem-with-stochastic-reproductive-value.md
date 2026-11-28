# Price equation and fundamental theorem with stochastic reproductive value

**Setting.** A finite class-structured population (classes $x \in X$ may differ in ploidy $L_x$, sex, age or condition) lives in a randomly fluctuating environment $e$, and its class composition $\mathbf x$ fluctuates as well. Under the *neutral* process (all individuals share a background phenotype) reproductive value is the fixed point $\phi^*$ of the operator that maps a candidate function on classes to its expected value one year later, normalized so that total reproductive value sums to one; write $\phi_i = \phi(x_i, e, \mathbf x) = L_{x_i}\phi^*(x_i, e, \mathbf x)$. Expected genetic shares of an individual's descendants, weighted by $\phi$,

$$R_x(t) = \sum_z c_{x,z}^{0,t}\, L_z\,\phi^*(z, e(t), \mathbf x(t)),$$

form a martingale for each $x$ under the neutral process. In a single *Taylor year* genotype is allowed to affect phenotype. The **fitness** of individual $i$ is the proportional change in the expected reproductive value it contributes,

$$F_i = \frac{L_i\sum_{y'}\phi(y', e', \mathbf x')\,w_{y',+i} - \phi_i}{\phi_i},$$

where $w_{y',+i}$ counts $i$'s share of offspring (or survival) in class $y'$ next year. For a p-score $p$ (a linear combination of allele frequencies), write $\mathrm{ave}_\phi$, $\mathrm{cov}_\phi$ and $\mathrm{var}_\phi$ for $\phi$-weighted moments and $\Delta^*\mathrm{ave}_\phi p$ for the change in the reproductive-value-weighted mean over the Taylor year before mutation.

**Theorem.**
1. $\mathrm{ave}_\phi F = 0$, and in a phenotypically uniform population $\mathbb E[F_i \mid e, \mathbf x, g] = 0$ for every $i$.
2. (Price equation) $\mathbb E[\Delta^*\mathrm{ave}_\phi p \mid e, \mathbf x, g] = \mathrm{cov}_\phi\big(p, \mathbb E[F \mid e, \mathbf x, g]\big)$, and averaged over the ergodic distribution of initial states, $\mathbb E[\Delta^*\mathrm{ave}_\phi p] = \mathbb E\big[\mathrm{cov}_\phi(p, \mathbb E[F \mid e, \mathbf x, a])\big]$.
3. (Fundamental theorem, one year) If $p$ is the $\phi$-weighted least-squares breeding value of expected fitness given the initial state, then $\mathbb E[\Delta^*\mathrm{ave}_\phi p \mid e, \mathbf x, a] = \mathrm{var}_\phi\, p$.
4. (Fundamental theorem, ensemble) If $p$ is the ensemble breeding value, minimizing $\mathbb E[\mathrm{ave}_\phi((\mathbb E[F \mid e, \mathbf x, a] - p)^2)]$, then $\mathbb E[\Delta^*\mathrm{ave}_\phi p] = \mathbb E[\mathrm{var}_\phi\, p] + \mathbb V[\mathrm{ave}_\phi\, p]$.

Thus natural selection acts through the arithmetic expectation of fitness over all uncertainty, not through geometric-mean fitness.

## Depends on

- [Price equation](price.md)
- [Fisher's fundamental theorem of natural selection](mean-fitness-select-sub.md)

## Expansion

The fixed-point property of reproductive value says that, absent selection, an individual's expected reproductive value next year equals its current one, which is both the martingale property and part 1. Because total reproductive value is conserved, mean fitness is zero and the usual denominator of discrete-time selection equations disappears. The Price equation then follows by writing next year's weighted mean of $p$ as a sum over parents of their offspring shares times reproductive values and subtracting this year's mean. For the fundamental theorem, apply the Price equation to the breeding value $p$ itself: the normal equations of least squares give $\mathrm{ave}_\phi p = 0$ and $\mathrm{cov}_\phi(p, \mathbb E F) = \mathrm{ave}_\phi(p^2)$, so the covariance becomes a variance; in the ensemble version the extra term is the variance across years of the population-mean breeding value. Ploidy cancels from fitness, so haploid, diploid and haplodiploid classes are covered at once. The results address only the effect of natural selection on gene frequencies; other forces acting during the year are present but not assessed.

## Sources

- P. Crewe, R. Gratwick, A. Grafen, "Defining fitness in an uncertain world", Journal of Mathematical Biology 76(5) (2018) 1059–1099, Eqs. (9)–(11) and (18)–(19), Theorem 1 (reproductive value as a martingale), Lemma 2, Theorem 2, Corollary 1 and Theorems 3–4, <https://doi.org/10.1007/s00285-017-1164-z>, PMCID PMC5829223.
