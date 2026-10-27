---
article_id: af_99b24a1871987bc8373af653
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted.exists_common_indep_of_cut_le
---

# Exists common indep of cut le

Abstract rank-function form of matroid intersection: two functions
`r₁ r₂ : Finset α → ℕ` satisfying the rank axioms (bounded by cardinality,
monotone, submodular) yield a common "independent" set `I ⊆ E` of size at
least `k` whenever every cut `X ⊆ E` satisfies `k ≤ r₁ X + r₂ (E \ X)`.
Proved by induction on `E`, via deletion and contraction.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Matroid.MatroidIntersection](../../../../../../sources/v2/MathlibExt.md)
