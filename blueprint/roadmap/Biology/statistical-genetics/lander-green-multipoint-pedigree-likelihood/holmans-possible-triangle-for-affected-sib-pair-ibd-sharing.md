# Holmans' possible triangle for affected sib pairs

For a pair of affected sibs, let $(z_0, z_1, z_2)$ be the probabilities that they share $0$, $1$ or $2$ alleles identical by descent at a disease-susceptibility locus; without linkage $(z_0, z_1, z_2) = (1/4, 1/2, 1/4)$. For a single disease-susceptibility locus, under random mating and Hardy–Weinberg equilibrium at that locus, the sharing probabilities satisfy the triangle constraints

$$z_1 \le \tfrac12, \qquad 2 z_0 \le z_1$$

(Suarez et al.; Holmans 1993; as stated by Dudoit and Speed 1999). The region they cut out of the simplex is the possible triangle with vertices $(1/4, 1/2, 1/4)$, $(0, 1/2, 1/2)$ and $(0, 0, 1)$. Holmans (1993) showed that restricting maximization of the affected-sib-pair likelihood to the possible triangle improves the power of Risch's likelihood-ratio test, and derived the asymptotic distributions of the resulting statistics.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

1. The model: one disease locus with arbitrary penetrances in a randomly mating population in Hardy–Weinberg equilibrium, and the sharing law of affected sib pairs.
2. The expression of $(z_0, z_1, z_2)$ through the penetrances and the proof of the two inequalities.
3. The vertices of the possible triangle, from intersecting the two constraints with the simplex.
4. The restricted maximum-likelihood test and its asymptotic null distribution, as a separate statement.
5. Failure of the constraints without random mating, and their validity under the general multilocus model with the assumptions of Dudoit and Speed, as separate statements.

## Sources

- S. Dudoit and T. P. Speed, Triangle constraints for sib-pair identity by descent probabilities under a general multilocus model for disease susceptibility, in M. E. Halloran and S. Geisser (eds.), *Statistics in Genetics*, IMA Vol. Math. Appl. 112, Springer, New York (1999), Introduction.
- P. Holmans, Asymptotic properties of affected-sib-pair linkage analysis, Am. J. Hum. Genet. 52 (1993), 362–374, abstract.
