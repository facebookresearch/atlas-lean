/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Polynomial.Roots
public import MathlibExt.LinearAlgebra.GeneralizedEigenvalueInterlacing
public import MathlibExt.LinearAlgebra.MaxMinGeneralizedEigenvalue

/-!
# Generalized eigenvalues of MAX matrices to MIN matrices

Results from Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen,
*On Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*,
Journal of Integer Sequences 28 (2025), Article 25.7.1.

A generalized eigenvalue (g-eigenvalue) of `A` to `B` (with `B` invertible) is a root of
`det (A - λ B)`. The g-eigenvalues with multiplicity are the roots of the polynomial
`det (A - X • B)`, written `(A.map C - (X : R[X]) • B.map C).det`.
-/
