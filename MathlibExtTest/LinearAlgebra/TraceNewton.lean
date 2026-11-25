/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.TraceNewton

open MathlibExt.LinearAlgebra.TraceNewtonWanted.LinearAlgebra.TraceNewton
open Matrix Polynomial

variable {R : Type*} [CommRing R]

-- The empty matrix has characteristic polynomial 1 and all positive descending coefficients zero.
example (A : Matrix (Fin 0) (Fin 0) R) (m : ℕ) :
    charpolyDescendingCoeff A 0 = 1 ∧ charpolyDescendingCoeff A (m + 1) = 0 := by
  simp [charpolyDescendingCoeff]

-- At k = 3 in dimension two the surviving terms give tr(A³) - tr(A²) tr(A) + tr(A) det(A).
example (A : Matrix (Fin 2) (Fin 2) R) :
    trace (A ^ 3) - trace (A ^ 2) * trace A + trace A * det A = 0 := by
  nontriviality R
  have h := trace_cayley_hamilton_newton A (k := 3) (by decide)
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide] at h
  simpa [charpolyDescendingCoeff, A.charpoly_fin_two, coeff_X_pow, coeff_C, coeff_X,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
