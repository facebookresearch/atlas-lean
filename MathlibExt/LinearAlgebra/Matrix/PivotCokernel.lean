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
# Pivot coordinates and cokernel lengths

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). The decomposition R^(1 ⊕ I) ≃ R × R^I identifies the block matrix
[[a,r],[c,B]] with (x,y) ↦ (ax + ry,cx + By). Over a domain, a ≠ 0 and nonzero block
determinant imply ℓ(coker P) + |I|ℓ(R/aR) = ℓ(R/aR) + ℓ(coker(aB − cr)), with module lengths
in ℕ∞.
-/

@[expose] public section
noncomputable section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- **Coordinates for a distinguished pivot.**

For a commutative ring R and finite I, the R-linear equivalence R^(1 ⊕ I) ≃ R × R^I sends z to
(z(*), i ↦ z(i)); its inverse combines the singleton coordinate and the I-coordinates.
-/
def pivotCoordinates : ((Unit ⊕ ι) → R) ≃ₗ[R] R × (ι → R) :=
  (LinearEquiv.sumArrowLequivProdArrow Unit ι R R).trans
    ((LinearEquiv.funUnique Unit R R).prodCongr (LinearEquiv.refl R (ι → R)))

/-- **The linear functional of a pivot row.**

For a commutative ring R, finite I and r ∈ Mat(1,I;R), the R-linear functional associated to r
is y ↦ ∑ⱼ r(*,j)yⱼ on R^I.
-/
def pivotRowLinear (r : Matrix Unit ι R) : (ι → R) →ₗ[R] R :=
  (LinearEquiv.funUnique Unit R R).toLinearMap.comp r.mulVecLin

/-- **The linear map of a pivot column.**

For a commutative ring R, finite I and c ∈ Mat(I,1;R), the R-linear map associated to c sends
x ∈ R to the vector i ↦ c(i,*)x in R^I.
-/
def pivotColumnLinear (c : Matrix ι Unit R) : R →ₗ[R] (ι → R) :=
  c.mulVecLin.comp (LinearEquiv.funUnique Unit R R).symm.toLinearMap

/-- **The block matrix in pivot coordinates.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). Under C : R^(1 ⊕ I) ≃ R × R^I, the conjugate C P C⁻¹ of the matrix map P =
[[a,r],[c,B]] is the linear map (x,y) ↦ (ax + ∑ⱼ r(*,j)yⱼ, i ↦ c(i,*)x + (By)ᵢ).
-/
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

/-- **The Schur matrix as a linear map.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). The matrix map of S = aB − cr is y ↦ a(By) − c(ry), where ry = ∑ⱼ r(*,j)yⱼ and
c(x)ᵢ = c(i,*)x.
-/
theorem pivotSchur_linear_map (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    (pivotSchur a r c B).mulVecLin =
      LinearMap.pivotSchur a (pivotRowLinear r) (pivotColumnLinear c) B.mulVecLin := by
  apply LinearMap.ext
  intro y
  funext i
  simp [pivotSchur, pivotRowLinear, pivotColumnLinear, LinearMap.pivotSchur,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- **The pivot cokernel length relation.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). Assume R is a domain, a ≠ 0 and det P ≠ 0 for P = [[a,r],[c,B]]. Write S = aB
− cr and ℓ for R-module length in ℕ∞. Then ℓ(R^(1 ⊕ I)/im P) + |I|ℓ(R/aR) = ℓ(R/aR) + ℓ(R^I/im
S). The equality does not require these lengths to be finite.
-/
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
