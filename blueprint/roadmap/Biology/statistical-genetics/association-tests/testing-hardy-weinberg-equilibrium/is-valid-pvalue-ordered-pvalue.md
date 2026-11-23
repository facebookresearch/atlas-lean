# Validity of ordered exact HWE p-values

If the heterozygote count `H` has Levene's law,
then for every extremeness key `g` the ordered p-value `orderedPValue (leveneProb N nA) g` at
`H` is a valid p-value. No large-sample approximation is involved.

The feasibility hypothesis `nA ≤ 2 * N` is required even though the combinatorial bound
below does not use it: without it both `μ` and `leveneMeasure N nA` can be the zero measure
(e.g. `N = 0`, `nA = 1`), and validity would hold vacuously rather than under a genuine HWE
probability law.

## Sources

- Wigginton, Cutler and Abecasis (2005); Lehmann–Romano (2005), Lemma 3.3.1.
