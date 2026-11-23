# Multiplicative haploid selection preserves linkage equilibrium

**Multiplicative haploid selection preserves linkage equilibrium** (core identity, two
alleles at each of two loci). A haplotype is `g : Bool × Bool` (`g.1` the allele at the first
locus, `g.2` the allele at the second). The haplotype frequencies are in linkage equilibrium,
`x g = p g.1 * q g.2`, and the haplotype fitnesses are multiplicative across loci,
`w g = a g.1 * b g.2`. `y` is the result of one round of haploid selection,
`y g = x g * w g / ∑ h, x h * w h`. One round of random mating with recombination fraction `r`,
`(1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2)))`, then gives the product of the two
single-locus selected frequencies `p i * a i / ∑ j, p j * a j` and
`q i * b i / ∑ j, q j * b j`, so the population stays in linkage equilibrium.

The identity holds for every real `r` and needs no nonzero mean-fitness hypothesis: when a
single-locus mean fitness vanishes, both sides are `0` (`x / 0 = 0`). The biological domain is
`0 ≤ r ≤ 1/2`, `p` and `q` on the simplex and positive fitnesses.
