# Pearson's `X² → χ²₁` limit theorem for Hardy–Weinberg equilibrium with estimated allele frequency

**Pearson's `X² → χ²₁` limit theorem for Hardy–Weinberg equilibrium with estimated allele
frequency.** Let the genotypes `X 0, X 1, …` (number of copies of the counted allele) be i.i.d. in
Hardy–Weinberg proportions `P(X 0 = i) = hweProb p i` at a polymorphic allele frequency
`0 < p < 1`. Then Pearson's statistic of the genotype counts of the first `N` individuals against
the Hardy–Weinberg proportions at the sample allele frequency `p̂`,
`hweStat N (cellCount X N) = ∑ᵢ (nᵢ - N hweProb p̂ i)² / (N hweProb p̂ i)`, converges in
distribution to `χ²₁` as `N → ∞`.

The proof writes `hweStat = N F̂²` (`hweStat_eq_mul_inbreedingHat_sq`), linearizes `√N F̂` around
the centered summand `1{X = 2} - p X + p²` (variance `p² (1 - p)²`), and applies the central limit
theorem, the strong law, and Slutsky's theorem.
