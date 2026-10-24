---
article_id: af_e2a20e0767ce08e0c4f89219
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.CStarAlgebra.LandmarkWanted.cStarAlgebra_gns_cyclic_vector
---

# C Star Algebra gns cyclic vector

For a unital positive functional `f` with `f 1 = 1` on a C*-algebra, the GNS space contains a unit
cyclic vector `ξ` with `f a = ⟪ξ, π(a) ξ⟫` and dense span of `π(A) ξ`. Source: GNS construction,
Gelfand–Naimark 1943 and I. E. Segal, Ann. of Math. 48 (1947); see Murphy, C*-Algebras; Lean is
unital state f 1 = 1 unit cyclic vector with inner-product formula and dense span.
It is `PositiveLinearMap.exists_gns_cyclic_vector`, kept under the source's name.
Proves `Wanted` entry `cStarAlgebra_gns_cyclic_vector`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists gns cyclic vector](exists-gns-cyclic-vector.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.CStarAlgebra.GNSCyclicVector](../../../../../../sources/v2/MathlibExt.md)
