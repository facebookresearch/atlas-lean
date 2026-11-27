# GEM abundances of families in a CMJ population with immigration

Consider the supercritical homogeneous binary CMJ (splitting tree) population with birth rate $b$, Malthusian parameter $\eta$ and Poisson($\theta$) immigration of founders, where each founder starts a family carrying a clonally inherited type. Let $I(t)$ be the total population size and rank the surviving families by decreasing age, with sizes $Z^{(1)}(t), Z^{(2)}(t), \dots$.

**Theorem.**

1. (*Model I: every immigrant has a new type.*) Almost surely

$$\lim_{t\to\infty} I(t)^{-1}\big(Z^{(1)}(t), Z^{(2)}(t), \dots\big) = (P_1,P_2,\dots),$$

where $(P_i)$ has the GEM distribution with parameter $\theta/b$: $P_i = B_i\prod_{j<i}(1 - B_j)$ with $B_i$ i.i.d. $\mathrm{Beta}(1,\theta/b)$.

2. (*Model II: immigrant types drawn from a discrete law $(p_i)_{i\ge1}$.*) With $I_i(t)$ the number of type-$i$ individuals and $\theta_i = \theta p_i/b$, almost surely $I(t)^{-1}(I_1(t), I_2(t), \dots) \to (P'_1,P'_2,\dots)$, where $P'_i = B'_i\prod_{j<i}(1 - B'_j)$ with independent $B'_i \sim \mathrm{Beta}\big(\theta_i, \tfrac{\theta}{b}\sum_{j>i}p_j\big)$; in particular $P'_i \sim \mathrm{Beta}(\theta_i, \theta/b - \theta_i)$, and for finitely many types $(P'_1,\dots,P'_n) \sim \mathrm{Dir}(\theta_1,\dots,\theta_n)$.

3. (*Model III: continuous spectrum, founders arriving at rate proportional to metacommunity abundance.*) The relative abundances converge a.s. to $(\sigma_1/\sigma, \sigma_2/\sigma, \dots)$, where $(\sigma_i)$ are the points of a Poisson process on $(0,\infty)$ with intensity $\frac{\theta}{\eta}\frac{F(y)}{y}\,dy$, $F$ is the tail of the limit of a rescaled family size, and $\sigma = \sum_i\sigma_i$.

The GEM$(\theta/b)$ limit is the size-biased order of the Poisson–Dirichlet law with parameter $\theta/b$, so neutral island communities fed by immigration reproduce Ewens-type abundance spectra for arbitrary (non-exponential) lifetimes.

## Depends on

- [Negative binomial and Gamma laws of a CMJ population with immigration](negative-binomial-and-gamma-laws-of-a-cmj-population-with-immigration.md)
- [Expected counting measure of GEM and Poisson–Dirichlet masses](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/poisson-dirichlet-gem-limit-of-ewens-allele-freq.md)

## Expansion

Family $i$ founded at time $T^{(i)}$ satisfies $e^{-\eta t}Z^{(i)}(t) \to e^{-\eta T^{(i)}}E_i$, so relative abundances converge to normalized points $e^{-\eta T^{(i)}}E_i / \sum_j e^{-\eta T^{(j)}}E_j$. For exponential $E_i$ and Poisson arrival times these points form a Poisson process with intensity proportional to $y^{-1}e^{-cy}dy$, a Gamma subordinator's jumps, whose normalized jumps in age order are GEM; the shape $\theta/b$ comes from the Gamma law of the total. Thinning the immigration by type in Model II splits the Gamma subordinator into independent Gamma pieces, giving the Dirichlet and stick-breaking Beta laws.

## Sources

- Mathieu Richard, "Limit theorems for supercritical age-dependent branching processes with neutral immigration", arXiv (2010). Section 2 (Proposition 2.2, Theorems 2.4, 2.5 and 2.9, Remark 2.6, Propositions 2.7–2.8), Section 5 (Lemma 5.1). <https://doi.org/10.48550/arXiv.1007.5428>. Published version: Advances in Applied Probability 43(1) (2011), 276–300, <https://doi.org/10.1239/aap/1300198523>; locators above refer to the arXiv version.
