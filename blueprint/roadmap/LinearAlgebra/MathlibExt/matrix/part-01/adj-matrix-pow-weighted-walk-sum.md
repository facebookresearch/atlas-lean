---
article_id: af_ae0d8814d53edecdcea33e0c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.adjMatrix_pow_weighted_walk_sum
---

# Adj Matrix Pow Walk

Weighted adjacency matrix powers count weighted walks: for a weighted digraph
with vertices `Fin k` and weighted adjacency matrix `A`, the `ij`th entry of
`A ^ n` is the sum, over all vertex sequences `p` of length `n + 1` from `i`
to `j`, of the product of the edge weights along the walk.

Walks are encoded as vertex sequences `Fin (n + 1) → Fin k` with `p 0 = i`
and `p (Fin.last n) = j`; the edge-weight product runs over `t : Fin n`.
The source states `n ≥ 1`; the formalization covers `n = 0` as well, where
both sides reduce to the Kronecker delta.
Proves `Wanted` entry `adjMatrix_pow_weighted_walk_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.AdjMatrixPowWalk](../../../../../sources/v2/MathlibExt.md)
- Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem (label theorem01), lines 128–130, https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
