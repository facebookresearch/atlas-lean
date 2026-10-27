---
article_id: af_10223ed2aa19b597f41f5419
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.stirling_edgeworth_expansion
---

# Stirling Edgeworth Expansion Wanted

The local Edgeworth expansion of the Ewens sampling occupancy probability mass
function `P(K_n(θ) = k) = θ^k [n,k] / θ^{(n)}`, uniformly over the parameter
on compact subsets of the positive reals and over all values in its support:
`(log n)^{(r+1)/2} sup_k |PMF − Gaussian × ∑_{j≤r} H_j/(θ log n)^{j/2}| → 0`,
stated in ε–N form with the coefficient functions `H` existentially bound.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Probability.StirlingEdgeworthExpansionWanted](../../../sources/v2/WantedExt.md)
- Zakhar Kabluchko, Alexander Marynych, and Henning Sulzbach, "Mode and Edgeworth Expansion for the Ewens Distribution and the Stirling Numbers," Journal of Integer Sequences 19 (2016), Article 16.8.8, Theorem (label `theo:stirling_edgeworth`), lines 207–226 (Ewens probability mass function at lines 143–146), https://cs.uwaterloo.ca/journals/JIS/VOL19/Kabluchko/kabl2.tex
