# Vertex-maximum pruning of convex two-locus test statistics

**Setting.** In an exhaustive two-locus (epistasis) scan, $N$ individuals have a phenotype vector and genotypes at SNPs $A$ and $B$. The association of the pair with the phenotype is measured by a statistic $T$ computed from the contingency table $O = (O_{gk})$ of counts with joint genotype $g$ of $(A,B)$ and phenotype class $k$. Fix SNP $A$ and the phenotype. Everything known before SNP $B$ is examined (the counts of each $A$-genotype within each phenotype class, nonnegativity, and any other linear constraints such as $B$'s genotype counts) confines the feasible tables of all partners $B$ to a convex polytope $P_A$.

**Theorem.** If $T$ is a convex function of the table on $P_A$, then

$$\max_{O \in P_A} T(O) = \max_{O \in \operatorname{vert}(P_A)} T(O),$$

and if this vertex maximum is below the significance threshold $\tau$, no pair $(A, B)$ can reach $\tau$, so all such pairs are discarded without being tested. The pruning is exact: it never removes a pair whose statistic exceeds $\tau$.

**Convex statistics.** For a case-control phenotype with fixed class totals $c_1, c_2$ ($c_1 + c_2 = N$) and row totals $r_g = O_{g1} + O_{g2}$, the Pearson statistic is

$$X^2 = \sum_g \frac{N^2\,(O_{g1} - r_g c_1/N)^2}{r_g\, c_1 c_2},$$

a sum of squared linear forms divided by positive linear forms, hence convex in $O$. The likelihood-ratio statistic $G = 2\sum_{g,k} O_{gk} \log\big(N O_{gk}/(r_g c_k)\big)$ is a sum of perspectives of $u \mapsto u\log u$ plus a linear term, hence also convex. Entropy-based statistics of the same form are covered likewise.

## Depends on

- [Asymptotic law of the Pearson chi-square test of independence](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/pearson-chi-square-test-of-independence.md)

## Expansion

A convex function on a polytope attains its maximum at an extreme point, since every point is a convex combination of vertices and $T$ evaluated there is at most the corresponding combination of vertex values. For a $2 \times 2 \times 2$ design the polytope is small, so the bound costs little compared with testing each of the $\binom{\#\text{SNPs}}{2}$ pairs. Because $P_A$ depends on the phenotype only through quantities shared by every partner $B$, the bound can be computed once per SNP and per permutation of the phenotype, which makes permutation-based family-wise error control feasible at genome scale. Earlier exact screens derived test-specific tight upper bounds for the two-locus ANOVA $F$ statistic and the two-locus chi-square statistic that split into a single-SNP term plus a term depending only on the genotypes of the pair; the convexity argument replaces these with one bound valid for every convex statistic.

## Sources

- X. Zhang, S. Huang, Z. Zhang, W. Wang, "Chapter 10: Mining genome-wide genetic markers", PLoS Computational Biology 8(12):e1002828 (2012), Section 3 (exact methods for two-locus association: FastANOVA Theorem 1, FastChi Theorem 2, and the COE convex-optimization bound in Section 3.3), <https://doi.org/10.1371/journal.pcbi.1002828>, PMCID PMC3531292.
