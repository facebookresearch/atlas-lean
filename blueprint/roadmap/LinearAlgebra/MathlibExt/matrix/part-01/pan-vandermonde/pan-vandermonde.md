---
article_id: af_0a2702e528121ffb1eb6be3e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pan_vandermonde
---

# Pan vandermonde

Basic properties of the generalized factorial matrices: the Stirling-mediated
matrix decomposition, the Vandermonde determinant formula (hence invertibility),
and the matrix inverse formula.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Pan vandermonde general](pan-vandermonde-general.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.PanVandermonde](../../../../../../sources/v2/MathlibExt.md)
- Jiaqiang Pan, "Matrix Decomposition of the Unified Generalized Stirling Numbers and Inversion of the Generalized Factorial Matrices," Journal of Integer Sequences 15 (2012), Article 12.6.6, Theorem (label t:Vandermonde), lines 428–460, https://cs.uwaterloo.ca/journals/JIS/VOL15/Pan/pan19.tex. It follows from `pan_vandermonde_general`; the hypothesis `hp` is unused and keeps the source's shape. Proves `Wanted` entry `pan_vandermonde`.
