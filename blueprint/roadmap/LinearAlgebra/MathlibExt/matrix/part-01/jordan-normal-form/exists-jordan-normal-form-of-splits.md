---
article_id: af_30920a289eafd467e30d5bc9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted.exists_jordan_normal_form_of_splits
---

# Exists jordan normal form of splits

Jordan normal form: a square matrix whose characteristic polynomial splits is similar to a
block-diagonal matrix of Jordan blocks.

Proof: Decompose into the maximal generalized eigenspaces (Axler, Linear Algebra Done Right,
4th ed., 8.22), take a Jordan-chain basis of each nilpotent restriction, and collect them as in
the proof of Axler 8.46. The nilpotent case is proved by induction on the range, extending chains
by preimages and adding kernel vectors, as in Wikipedia, "Jordan normal form", section "A proof".

## Depends on

- [Jordan Block](jordan-block.md)

## Proof depends on

- [Exists jordan Basis of charpoly splits](exists-jordan-basis-of-charpoly-splits.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.JordanNormalForm](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / Jordan normal form; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 3.4.1.
