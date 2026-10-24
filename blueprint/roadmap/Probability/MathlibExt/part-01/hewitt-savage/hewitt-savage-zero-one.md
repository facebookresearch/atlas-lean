---
article_id: af_ea7ddafef78f37f09c6a9204
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one
---

# Hewitt savage zero one

If `S` is Polish, `μ : Measure S` is a probability measure and `E : Set (ℕ → S)` is measurable and
invariant under every finitely supported permutation of `ℕ`, then `Measure.infinitePi (fun _ => μ)
E = 0` or `1`. Source: E. Hewitt and L. J. Savage, Symmetric measures on Cartesian products,
Trans. Amer. Math. Soc. 80 (1955) 470–501; textbook in Kallenberg, Probabilistic Symmetries and
Invariance Principles; general holds for product of identical Borel probabilities.

It follows from `hewitt_savage_zero_one_general`; the instances `[PolishSpace S]` and
`[BorelSpace S]` are unused and keep the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Hewitt savage zero one general](hewitt-savage-zero-one-general.md)

## Sources

- [MathlibExt, MathlibExt.Probability.HewittSavage](../../../../../sources/v2/MathlibExt.md)
