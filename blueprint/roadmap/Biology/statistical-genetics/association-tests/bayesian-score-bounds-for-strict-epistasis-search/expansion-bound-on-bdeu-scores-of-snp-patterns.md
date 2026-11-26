# Expansion bound on BDeu scores of SNP patterns

Let a SNP pattern have disease status $X$ ($r$ states) with a parent set of SNPs having $q$ joint genotype instantiations and counts $M_1,\dots,M_q$ per instantiation, and let $\alpha > 0$ be the BDeu prior equivalent sample size. Add further SNPs whose joint genotypes have $v$ combined states, so that the expanded pattern has $qv$ parent instantiations. Then for every way the data split over the new instantiations, the BDeu local score of disease status in the expanded pattern satisfies

$$S_{\mathrm{exp}} \le \prod_{j=1}^q \frac{\Gamma\bigl(\alpha/(qv)\bigr)\,\Gamma\bigl(\alpha/(rqv) + M_j\bigr)}{\Gamma\bigl(\alpha/(qv) + M_j\bigr)\,\Gamma\bigl(\alpha/(rqv)\bigr)} .$$

The right side depends only on the current pattern and $v$ (for biallelic coding, $v = 2, 4, 8$ when one, two or three SNPs are added; for three genotypes per SNP, $v = 3, 9, 27$). Ranking SNPs by this bound for their 1-SNP patterns, instead of by their 1-SNP scores, and expanding in that order is a heuristic search for strict epistasis, where no SNP has a marginal effect.

## Depends on

- [Purity maximizes the BDeu local score](purity-maximizes-the-bdeu-local-score.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Each old instantiation $j$ splits into $v$ new cells with counts $M_{j1},\dots,M_{jv}$ summing to $M_j$. By [purity](purity-maximizes-the-bdeu-local-score.md) the score is at most $\prod_{j,l} g(M_{jl})$ with $g(m) = \Gamma(a)\Gamma(b+m)/(\Gamma(a+m)\Gamma(b)) = \prod_{i=0}^{m-1}(b+i)/(a+i)$, $a = \alpha/(qv)$ and $b = \alpha/(rqv) < a$. The factors $(b+i)/(a+i)$ increase with $i$, so $g(m_1+m_2) \ge g(m_1)g(m_2)$ and $g(0) = 1$; hence merging all of $M_j$ into one cell can only increase the bound, $\prod_l g(M_{jl}) \le g(M_j)$. The bound is loose and does not by itself prune the search provably, but it favours patterns whose genotype counts are concentrated, which is informative even without marginal association with disease.

## Simulation results

In the source's simulations, expanding SNPs in the order of this bound reached the true 2- to 4-SNP interaction after examining a small fraction of all patterns, smallest at low minor-allele frequency.

## Sources

- X. Jiang and R. E. Neapolitan, "Mining pure, strict epistatic interactions from high-dimensional datasets: ameliorating the curse of dimensionality", PLoS ONE 7 (2012), e46771, <https://doi.org/10.1371/journal.pone.0046771>, PMCID PMC3470561. Section "SNP patterns and a bound for SNP patterns" (Eq. (3) and the bound that follows it) and Algorithm 1.
