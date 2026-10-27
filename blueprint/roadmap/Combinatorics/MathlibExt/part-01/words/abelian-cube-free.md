---
article_id: af_6b83c43356ce83ce8499d36d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.abelianCubeFree
---

# Ternary Abelian Cube Free Lower Bound

Exponential lower bound for ternary abelian-cube-free words.

The count of abelian-cube-free words of length `n` over `{0,1,2}` is
`Ω(2^(n/24))`, encoded as `2^(n/24) = O(count)`. An abelian cube is three
consecutive nonempty blocks with equal letter counts.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound](../../../../../sources/v2/MathlibExt.md)
- Ali Aberkane and James D. Currie, *The Number of Ternary Words Avoiding Abelian Cubes Grows Exponentially*, Journal of Integer Sequences 7 (2004), Article 04.2.7, <https://cs.uwaterloo.ca/journals/JIS/VOL7/Currie/currie18.tex>, Second Main Theorem, lines 558-561.
