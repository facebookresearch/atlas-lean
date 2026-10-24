---
article_id: af_31dc6ed896218401103508aa
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.Matrix.det_toeplitzHessenberg_eq_sum_compositions
---

# Det toeplitz Hessenberg eq sum compositions

Trudi's formula for the determinant of the Hessenberg–Toeplitz matrix
  `A_n(a_0; a_1, …, a_n)` as a signed sum over ordered compositions of `n`.

Source: Taras Goy and Mark Shattuck, *Determinants of Some
  Hessenberg-Toeplitz Matrices with Motzkin Number Entries*, Journal of Integer
  Sequences 26 (2023), Article 23.3.4, matrix display `DetHess` lines 146–155,
  Lemma `lem1` lines 157–166 with equation `Trudi` at lines 159–161 and the
  equivalent composition sum at lines 163–165,
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Shattuck/sh36.tex>.

The multinomial partition-indexed display over `s_1 + 2 * s_2 + … + n * s_n = n`
  is a source-declared equivalent encoding of this composition sum and is not
  stated separately; Brioschi's formula is the `a_0 = 1` specialization (line 167).
Proves `Wanted` entry `Matrix.det_toeplitzHessenberg_eq_sum_compositions`.
It follows from `Matrix.det_toeplitzHessenberg_eq_sum_compositions_general`; the hypotheses `hn`
and `ha0` are unused and keep the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Det toeplitz Hessenberg eq sum compositions general](det-toeplitz-hessenberg-eq-sum-compositi.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant](../../../../../../sources/v2/MathlibExt.md)
