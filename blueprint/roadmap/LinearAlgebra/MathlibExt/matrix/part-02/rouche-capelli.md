---
article_id: af_484c09b52917b25d54987efb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.rouche_capelli
---

# Rouche Capelli

Rouché–Capelli theorem (statement `rouche-capelli-s1`): a linear system
`A x = b` over a field, with coefficient matrix `A` and augmented matrix
`(A | b)`, is solvable if and only if the rank of `A` equals the rank of
`(A | b)`.

Proof: Following the column-space argument in [Wikipedia, *Rouché–Capelli theorem*,
"Proof"](https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem#Proof), solvability is
membership of `b` in the column span, which we compare before and after adjoining `b`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.RoucheCapelli](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem.
