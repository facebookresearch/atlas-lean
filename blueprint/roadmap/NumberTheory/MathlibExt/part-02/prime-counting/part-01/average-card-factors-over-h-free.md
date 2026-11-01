---
article_id: af_681ba9327783141cefef3184
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.average_cardFactors_over_h_free
---

# Average Omega HFree

For every fixed integer `h ≥ 2`, the sum of the total numbers of prime factors
of the `h`-free positive integers at most `x` is `x * log (log x) / ζ(h)` up
to an error of order `x`. The `h`-free condition is rendered as
`n.factorization p < h` for all `p ∈ n.primeFactors`, and the main-term
constant is `(riemannZeta h).re⁻¹`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.AverageOmegaHFree](../../../../../../sources/v2/MathlibExt.md)
- Rafael Jakimczuk and Matilde Lalín, "The Number of Prime Factors on Average in Certain Integer Sequences," Journal of Integer Sequences 25 (2022), Article 22.2.3, Theorem (label `thmhfree`), lines 110–117, https://cs.uwaterloo.ca/journals/JIS/VOL25/Lalin/lalin2.tex
