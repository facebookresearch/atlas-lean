/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.CokernelSchur
public import MathlibExt.LinearAlgebra.ScalarCokernelPi
public import MathlibExt.LinearAlgebra.Matrix.PivotElimination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Actual matrix coordinates for the full pivot cokernel

The coordinate equivalence is the existing sum decomposition and evaluation
on the singleton block. The original matrix map becomes the literal module
block map, with both off-diagonal maps retained. These comparisons connect
division-free determinant elimination to full singular cokernel lengths.
-/

@[expose] public section
noncomputable section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- The actual canonical coordinates for the singleton pivot and remaining
indices, using existing linear equivalences. -/
def pivotCoordinates : ((Unit ⊕ ι) → R) ≃ₗ[R] R × (ι → R) :=
  (LinearEquiv.sumArrowLequivProdArrow Unit ι R R).trans
    ((LinearEquiv.funUnique Unit R R).prodCongr (LinearEquiv.refl R (ι → R)))

/-- The original row matrix, evaluated in the actual singleton coordinate. -/
def pivotRowLinear (r : Matrix Unit ι R) : (ι → R) →ₗ[R] R :=
  (LinearEquiv.funUnique Unit R R).toLinearMap.comp r.mulVecLin

/-- The original column matrix, with the actual singleton inverse coordinate. -/
def pivotColumnLinear (c : Matrix ι Unit R) : R →ₗ[R] (ι → R) :=
  c.mulVecLin.comp (LinearEquiv.funUnique Unit R R).symm.toLinearMap

/-- The actual original matrix map is the original module pivot map in
canonical coordinates, rather than an assumed matrix-map comparison. -/
theorem pivotBlock_coordinate_map (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    (pivotCoordinates (R := R) (ι := ι)).toLinearMap.comp
        ((pivotBlock a r c B).mulVecLin.comp (pivotCoordinates (R := R) (ι := ι)).symm.toLinearMap) =
      LinearMap.pivotBlock a (pivotRowLinear r) (pivotColumnLinear c) B.mulVecLin := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hy : (LinearEquiv.sumArrowLequivProdArrow Unit ι R R).symm
      ((AddEquiv.funUnique Unit R).symm x, y) ∘ Sum.inr = y := by
    funext i
    rfl
  apply Prod.ext
  · simp [hy, pivotCoordinates, pivotBlock, pivotRowLinear, LinearMap.pivotBlock,
      Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct]
  · funext i
    simp [hy, pivotCoordinates, pivotBlock, pivotColumnLinear, LinearMap.pivotBlock,
      Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct]

/-- The actual Schur matrix map agrees with the original full module
Schur map, preserving the off-diagonal composition. -/
theorem pivotSchur_linear_map (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    (pivotSchur a r c B).mulVecLin =
      LinearMap.pivotSchur a (pivotRowLinear r) (pivotColumnLinear c) B.mulVecLin := by
  apply LinearMap.ext
  intro y
  funext i
  simp [pivotSchur, pivotRowLinear, pivotColumnLinear, LinearMap.pivotSchur,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- For every original full-rank pivot matrix over a domain, its full
cokernel lengths satisfy the exact arbitrary-size elimination relation.
Injectivity and coordinate comparison are earned from the determinant and
canonical maps; no length equality or finite-length premise is assumed. -/
theorem length_coker_pivot_matrix_relation [DecidableEq ι] [IsDomain R]
    (a : R) (ha : a ≠ 0) (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R)
    (hA : (pivotBlock a r c B).det ≠ 0) :
    Module.length R (((Unit ⊕ ι) → R) ⧸ (pivotBlock a r c B).mulVecLin.range) +
        (Fintype.card ι : ℕ∞) * Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) =
      Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) +
        Module.length R ((ι → R) ⧸ (pivotSchur a r c B).mulVecLin.range) := by
  classical
  let e := pivotCoordinates (R := R) (ι := ι)
  let A := pivotBlock a r c B
  let P := LinearMap.pivotBlock a (pivotRowLinear r) (pivotColumnLinear c) B.mulVecLin
  have hAinj : Function.Injective A.mulVecLin := by
    change Function.Injective A.mulVec
    exact Matrix.mulVec_injective_of_det_ne_zero (M := A) hA
  have hp : Function.Injective P := by
    change Function.Injective (LinearMap.pivotBlock a (pivotRowLinear r) (pivotColumnLinear c) B.mulVecLin)
    rw [← pivotBlock_coordinate_map a r c B]
    exact e.injective.comp (hAinj.comp e.symm.injective)
  have hpost := LinearMap.length_coker_postcompose_equiv A.mulVecLin e
  have hpre := LinearMap.length_coker_precompose_equiv (e.toLinearMap.comp A.mulVecLin) e.symm
  have hc : (e.toLinearMap.comp A.mulVecLin).comp e.symm.toLinearMap = P :=
    pivotBlock_coordinate_map a r c B
  rw [hc] at hpre
  have hlength : Module.length R (((Unit ⊕ ι) → R) ⧸ A.mulVecLin.range) =
      Module.length R ((R × (ι → R)) ⧸ P.range) := hpost.symm.trans hpre.symm
  let _ : NoZeroSMulDivisors R (ι → R) := ⟨by
    intro b v h
    by_cases hb : b = 0
    · exact Or.inl hb
    · apply Or.inr
      funext i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_left hb⟩
  have h := LinearMap.length_coker_pivot_relation a ha (pivotRowLinear r) (pivotColumnLinear c)
    B.mulVecLin hp
  rw [← hlength, LinearMap.length_scalar_coker_pi, ← pivotSchur_linear_map] at h
  exact h

end Matrix
