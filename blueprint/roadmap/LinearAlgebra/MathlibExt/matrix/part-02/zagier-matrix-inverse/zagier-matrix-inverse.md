---
article_id: af_e403d564b587bf4ae8f82f0d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.zagier_matrix_inverse
---

# Zagier matrix inverse

Zagier's matrix conjecture: the two Bernoulli-number formulas for `P`
coincide, and `P` is the two-sided inverse of `A`. The three conjuncts are
the equality of the two formulas for `P`, then `A * P = 1`, then `P * A = 1`.
Source indices are 1-based; here rows and columns run over `Fin (K - 1)` with
`i.val + 1` and `j.val + 1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Zagier Inverse P](zagier-inverse-p.md)
- [Zagier Inverse P eq zagier Inverse Q](zagier-inverse-p-eq-zagier-inverse-q.md)
- [Zagier Inverse P mul zagier Matrix](zagier-inverse-p-mul-zagier-matrix.md)
- [Zagier Inverse Q](zagier-inverse-q.md)
- [Zagier Matrix](zagier-matrix.md)
- [Zagier Matrix mul zagier Inverse P](zagier-matrix-mul-zagier-inverse-p.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.ZagierMatrixInverse](../../../../../../sources/v2/MathlibExt.md)
- Yawen Ma and Lee-Peng Teo, "Another Proof of Zagier's Matrix Conjecture," Journal of Integer Sequences 25 (2022), Article 22.6.4, Theorem [Zagier's conjecture], equations (eq12) and (eq13), lines 279–285, https://cs.uwaterloo.ca/journals/JIS/VOL25/Teo/teo4.tex
