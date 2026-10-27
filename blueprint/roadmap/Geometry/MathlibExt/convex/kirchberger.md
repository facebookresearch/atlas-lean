---
article_id: af_0fbf10d87c3b9537cfdcc5b2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kirchberger
---

# Kirchberger

Kirchberger's theorem (stable source:
https://en.wikipedia.org/wiki/Kirchberger%27s_theorem, statement id `kirchberger-s1`):
Two finite point sets `A`, `B` in `ℝ^d` are strictly separable by a hyperplane
iff every subset of at most `d + 2` points of `A ∪ B` is separable, i.e. `A ∩ C`
and `B ∩ C` are separable for all `C` of size `≤ d + 2`.

Proof: The reverse implication applies Helly's theorem to tagged strict half-spaces in one higher
dimension, following the route of Rademacher and Schoenberg (1950) from Kirchberger (1903).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Convex.Kirchberger](../../../../sources/v2/MathlibExt.md)
- Paul Kirchberger, "Über Tchebychefsche Annäherungsmethoden," Mathematische Annalen 57 (1903), 509–540, DOI 10.1007/BF01445182, https://doi.org/10.1007/BF01445182.
