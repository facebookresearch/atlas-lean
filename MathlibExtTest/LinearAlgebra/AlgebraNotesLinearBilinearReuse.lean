/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical rank-nullity, bilinear matrix correspondence and real quadratic-form normalization.
Rectangular and empty matrix indices are kept explicit.
-/

namespace AlgebraNotesApiProbe

private theorem rank_nullity {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    Module.finrank K f.range + Module.finrank K f.ker = Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

private theorem transpose_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℚ) : A.transpose.rank = A.rank :=
  Matrix.rank_transpose A

private theorem bilinear_roundtrip (B : LinearMap.BilinForm ℚ (Fin 2 → ℚ)) :
    Matrix.toBilin' (B.toMatrix') = B := Matrix.toBilin'_toMatrix' B

private theorem bilinear_symmetry (B : LinearMap.BilinForm ℚ (Fin 2 → ℚ)) :
    B.toMatrix'.IsSymm ↔ B.IsSymm :=
  LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm

private theorem bilinear_nondegenerate {K V ι : Type*} [CommRing K] [IsDomain K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (B : LinearMap.BilinForm K V) :
    B.Nondegenerate ↔ (B.toMatrix b).det ≠ 0 :=
  LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b

private theorem normalized_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) :
    ∃ w : Fin (Module.finrank ℝ V) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) :=
  QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q

private theorem positive_signature_invariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q Q' : QuadraticForm ℝ V} (h : QuadraticMap.Equivalent Q Q') :
    sigPos Q = sigPos Q' := h.sigPos_eq

-- Rectangular and empty matrix indices are admitted, not silently restricted to GL_n.
example : (0 : Matrix (Fin 0) (Fin 2) ℚ).rank = 0 := by simp

#print axioms rank_nullity
#print axioms transpose_rank
#print axioms bilinear_roundtrip
#print axioms bilinear_symmetry
#print axioms bilinear_nondegenerate
#print axioms normalized_quadratic
#print axioms positive_signature_invariant

end AlgebraNotesApiProbe
