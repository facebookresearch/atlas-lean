# Expansion bound on BDeu scores of SNP patterns

Let a SNP pattern have disease status $X$ ($r$ states) with a parent set of SNPs having $q$ joint genotype instantiations, let $s_{jk}$ be the number of individuals with disease state $k$ in instantiation $j$, and let $\alpha > 0$ be the BDeu prior equivalent sample size. Add further SNPs whose joint genotypes have $v$ combined states, so that the expanded pattern has $qv$ parent instantiations. Then for every way the data split over the new instantiations, the BDeu local score of disease status in the expanded pattern satisfies

$$S_{\mathrm{exp}} \le \prod_{j=1}^q \prod_{k=1}^r \frac{\Gamma\bigl(\alpha/(qv)\bigr)\,\Gamma\bigl(\alpha/(rqv) + s_{jk}\bigr)}{\Gamma\bigl(\alpha/(qv) + s_{jk}\bigr)\,\Gamma\bigl(\alpha/(rqv)\bigr)} .$$

The right side depends only on the current pattern and $v$ (for biallelic coding, $v = 2, 4, 8$ when one, two or three SNPs are added; for three genotypes per SNP, $v = 3, 9, 27$). Ranking SNPs by this bound for their 1-SNP patterns, instead of by their 1-SNP scores, and expanding in that order is a heuristic search for strict epistasis, where no SNP has a marginal effect.

## Depends on

- [Purity maximizes the BDeu local score](purity-maximizes-the-bdeu-local-score.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Each old instantiation $j$ splits into $v$ new cells $(j, l)$, and $s_{jlk}$ counts disease state $k$ in cell $(j, l)$, so $\sum_l s_{jlk} = s_{jk}$. Put $a = \alpha/(qv)$, $b = \alpha/(rqv) < a$ and $g(m) = \Gamma(a)\Gamma(b+m)/(\Gamma(a+m)\Gamma(b)) = \prod_{i=0}^{m-1}(b+i)/(a+i)$. Cell $(j, l)$ contributes $\frac{\Gamma(a)}{\Gamma(a+M_{jl})}\prod_k \frac{\Gamma(b+s_{jlk})}{\Gamma(b)}$ with $M_{jl} = \sum_k s_{jlk}$; since $\Gamma(a+M_{jl})/\Gamma(a) \ge \prod_k \Gamma(a+s_{jlk})/\Gamma(a)$, this is at most $\prod_k g(s_{jlk})$, with equality when the cell is [pure](purity-maximizes-the-bdeu-local-score.md). The factors $(b+i)/(a+i)$ increase with $i$, so $g(m_1+m_2) \ge g(m_1)g(m_2)$ and $g(0) = 1$; hence $\prod_l g(s_{jlk}) \le g(s_{jk})$ for each $j$ and $k$, which gives the bound. When $v \ge r$ it is reached by placing each disease state's items of old cell $j$ in a separate new cell.

## Simulation results

In the source's simulations, expanding SNPs in the order of this bound reached the true 2- to 4-SNP interaction after examining a small fraction of all patterns, smallest at low minor-allele frequency.

## Sources

- X. Jiang and R. E. Neapolitan, "Mining pure, strict epistatic interactions from high-dimensional datasets: ameliorating the curse of dimensionality", PLoS ONE 7 (2012), e46771, <https://doi.org/10.1371/journal.pone.0046771>, PMCID PMC3470561. Section "SNP patterns and a bound for SNP patterns" (Eq. (3) and the bound that follows it) and Algorithm 1.
