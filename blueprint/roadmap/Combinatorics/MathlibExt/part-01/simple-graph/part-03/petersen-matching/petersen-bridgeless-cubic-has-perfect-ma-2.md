---
article_id: af_613e312a9e19e1803197ac53
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted.petersen_bridgeless_cubic_has_perfect_matching
---

# Petersen bridgeless cubic has perfect matching

Petersen's theorem: every finite bridgeless cubic simple graph has a perfect matching.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Petersen bridgeless cubic has perfect matching general](petersen-bridgeless-cubic-has-perfect-ma.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.PetersenMatching](../../../../../../../sources/v2/MathlibExt.md)
- J. Petersen, "Die Theorie der regulären graphs", Acta Mathematica 15 (1891), 193-220, DOI 10.1007/BF02392606. It follows from `petersen_bridgeless_cubic_has_perfect_matching_general`; the instance `[DecidableEq V]` is unused and keeps the source's shape.
