/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix
public import MathlibExt.Combinatorics.Enumerative.HessenbergToeplitzRecurrence
public import MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization
public import MathlibExt.Combinatorics.Enumerative.PascalDiagonalExponential
public import MathlibExt.Combinatorics.Enumerative.ShiftedAlphaStirlingMatrix

/-!
# A generalization of the Pascal and Stirling matrices

Statements from A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal
and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.

The α-upper entries, their symmetric polynomial formula, the matrix and its determinant formula
are in `MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix`. The α-Stirling and shifted
α-Stirling entries and matrices, the factorization, and the shifted determinant formula are in
`MathlibExt.Combinatorics.Enumerative.ShiftedAlphaStirlingMatrix`. The banded Hessenberg–Toeplitz
determinant formula is in `MathlibExt.Combinatorics.Enumerative.HessenbergToeplitzRecurrence`.

The factorial matrix of a power series (`powerSeriesFactorialMatrix`), the lemma on its diagonal
entries (`powerSeriesFactorialMatrix_apply_self`) and the proved multiplicativity
`powerSeriesFactorialMatrix_mul` are in
`MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization`, which this module imports.
-/
