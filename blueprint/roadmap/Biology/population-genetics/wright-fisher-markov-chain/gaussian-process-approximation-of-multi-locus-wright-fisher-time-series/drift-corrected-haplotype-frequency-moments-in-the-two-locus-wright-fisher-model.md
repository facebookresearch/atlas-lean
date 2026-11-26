# Drift-corrected haplotype moments in the two-locus Wright–Fisher model

Consider two neutral biallelic loci in a population of $2N$ gametes with recombination fraction $r$. Let $Z_t = (Z_t(1),\dots,Z_t(4))$ be the frequencies of haplotypes $A_1B_1, A_1B_0, A_0B_1, A_0B_0$ at generation $t$, $C_t = Z_t(1)Z_t(4) - Z_t(2)Z_t(3)$ the linkage disequilibrium and $\epsilon = (-1, 1, 1, -1)$. One generation of recombination maps $Z_t \mapsto f(Z_t) = Z_t + rC_t\epsilon$, and drift samples $2N Z_{t+1} \mid Z_t \sim \mathrm{Multinomial}(2N, f(Z_t))$. Started at $Z_0 = \pi = (z(1),\dots,z(4))$ with $c_0 = z(1)z(4) - z(2)z(3)$, the expected haplotype frequencies are

$$\mathrm{E}_\pi Z_t(i) = z(i) + \epsilon_i\, t\, r\, c_0\left(1 - \frac{t-1}{4N}\right)$$

up to terms of second order in $r$ and $1/(2N)$, and by the Markov property

$$\mathrm{E}_\pi\bigl[Z_{t+u}(i)\mid Z_t\bigr] = Z_t(i) + \epsilon_i\, u\, r\, C_t\left(1 - \frac{u-1}{4N}\right)$$

to the same order. The neglected terms grow with $t$, so the approximation is intended for $t \ll 1/r$. Combined with the analogous expansions of $\mathrm{E}_\pi[Z_t(i)Z_t(j)]$ and $\mathrm{E}_\pi[Z_t(i)C_t]$, these give the within- and between-generation covariances of the marginal allele frequencies used in the Gaussian-process likelihood.

## Depends on

- [Linkage disequilibrium after $t$ generations](../../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq-iterate.md)
- [Multinomial distribution](../../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Multinomial sampling is unbiased, so $\mathrm{E}[Z_{s+1}\mid Z_s] = Z_s + rC_s\epsilon$ and $\mathrm{E}Z_t = \pi + r\epsilon\sum_{s=0}^{t-1}\mathrm{E}C_s$. Under neutral drift with recombination, $\mathrm{E}[C_{s+1}\mid Z_s] = (1-r)\bigl(1 - \tfrac{1}{2N}\bigr)C_s$, which is the deterministic decay $D_t = (1-r)^tD_0$ multiplied by the loss of heterozygosity from drift. Hence $\mathrm{E}C_s = c_0(1-r)^s\bigl(1-\tfrac{1}{2N}\bigr)^s$; inside the factor $r$ the expansion keeps the leading drift correction, $rc_0(1 - s/(2N))$, and drops the terms of order $r^2$, and $\sum_{s=0}^{t-1}(1 - s/(2N)) = t - t(t-1)/(4N)$ gives the first formula. The second is the first applied to the chain restarted at $Z_t$.

## Sources

- J. Terhorst, C. Schlötterer and Y. S. Song, "Multi-locus analysis of genomic time series data from experimental evolution", PLoS Genetics 11 (2015), e1005069, <https://doi.org/10.1371/journal.pgen.1005069>, PMCID PMC4388667. Eqs. (8)–(9), Lemma 1 and the Remark following Corollary 2 (proofs in its S1 Text).
