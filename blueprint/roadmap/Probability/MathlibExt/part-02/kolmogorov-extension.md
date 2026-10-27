---
article_id: af_976f80d29b2f5f14e78ac25c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.KolmogorovExtensionWanted.kolmogorov_extension
---

# Kolmogorov Extension

If `P : ∀ J, Measure (∀ j ∈ J, α j)` is a projective family of probability measures on Polish
Borel factors `α i`, then there exists `μ` on `∀ i, α i` with `IsProjectiveLimit μ P`, i.e. its
finite projections are `P`. Source: A. N. Kolmogorov, Grundbegriffe der
Wahrscheinlichkeitsrechnung, 1933; P. J. Daniell 1918 precursor; textbook in Kallenberg,
Foundations of Modern Probability, 3rd ed. (Kolmogorov extension) and Tao, Introduction to Measure
Theory Lean Polish Borel projective-limit version; full general version handles standard Borel
factors.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.KolmogorovExtension](../../../../sources/v2/MathlibExt.md)
