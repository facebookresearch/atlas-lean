/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.Arnoldi
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.Arnoldi

namespace MathlibExtTest.Analysis.InnerProductSpace.Arnoldi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first Krylov vector is the starting vector. -/
example (T : E →ₗ[ℝ] E) (r : E) : krylovVec T r 3 0 = r := by simp [krylovVec]

/-- The Arnoldi matrix is upper Hessenberg: entry `(3, 1)` vanishes for `k = 4`. -/
example (T : E →ₗ[ℝ] E) (r : E) (h : LinearIndependent ℝ (krylovVec T r 4)) :
    hessenberg T r 4 3 1 = 0 :=
  hessenberg_eq_zero h (by decide)

/-- For symmetric `T` the Arnoldi matrix is tridiagonal: entry `(0, 2)` vanishes too. -/
example (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (r : E)
    (h : LinearIndependent ℝ (krylovVec T r 3)) : hessenberg T r 3 0 2 = 0 :=
  hessenberg_eq_zero_of_isSymmetric hT h (by decide)

/-- Entries on and next to the diagonal are not forced to vanish: for `T = 2 • id` and a unit
vector `r`, `h_00 = ⟪q_0, T q_0⟫ = 2`. -/
example (r : EuclideanSpace ℝ (Fin 2)) (hr : ‖r‖ = 1) :
    hessenberg ((2 : ℝ) • LinearMap.id (R := ℝ) (M := EuclideanSpace ℝ (Fin 2))) r 1 0 0 = 2 := by
  have hq : arnoldiVec ((2 : ℝ) • LinearMap.id (R := ℝ) (M := EuclideanSpace ℝ (Fin 2))) r 1 0
      = r := by
    have hg : InnerProductSpace.gramSchmidt ℝ
        (krylovVec ((2 : ℝ) • LinearMap.id (R := ℝ) (M := EuclideanSpace ℝ (Fin 2))) r 1) 0 =
          r := by
      rw [InnerProductSpace.gramSchmidt_def]
      have : Finset.Iio (0 : Fin 1) = ∅ := by decide
      simp [krylovVec, this]
    rw [arnoldiVec, InnerProductSpace.gramSchmidtNormed, hg, hr]
    simp
  simp only [hessenberg, Matrix.of_apply, hq, LinearMap.smul_apply, LinearMap.id_apply,
    inner_smul_right, real_inner_self_eq_norm_sq, hr]
  norm_num

end MathlibExtTest.Analysis.InnerProductSpace.Arnoldi
