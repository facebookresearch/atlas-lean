/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExtTest.AlgebraicTopology.CyclicObject.LodayBCIntegerMatrices

import Mathlib.Tactic.Abel

/-!
# Mixed-law obstruction from an isolated Connes sign change

For the word `E₀₁ ⊗ E₁₀` in `M₂(ℤ)`, the Hochschild boundary is
`D = E₀₀ - E₁₁`, and `B₀(D)` has entry-00 tensor probe value `2`.
Changing only `B₀` to `-B₀` while retaining `B₁` and the Hochschild differential
gives mixed-law defect `-2(B₀ ∘ b₁)`. The probe evaluates that defect to `-4`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open ModuleCat.Algebra.Hochschild.NonUnital
open scoped TensorProduct

namespace MathlibExtTest.LodayBCIntegerMatrices

/--
The coefficient-first tensor word `E₀₁ ⊗ E₁₀` over `ℤ`.
-/
def degreeOneWord : A ⊗[ℤ] TensorPower ℤ 1 A :=
  e01 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 1 => e10)

/--
The linear functional reading entry `(0,0)` of the single matrix in the
tensor tail.
-/
def tailEntry00 : TensorPower ℤ 1 A →ₗ[ℤ] ℤ :=
  (entry 0 0).comp
    (PiTensorProduct.subsingletonEquiv (R := ℤ) (s := fun _ : Fin 1 => A) (0 : Fin 1)).toLinearMap

/--
The tensor functional multiplying the `(0,0)` entries of the coefficient
and tail matrices.
-/
def probe00 : A ⊗[ℤ] TensorPower ℤ 1 A →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map (entry 0 0) tailEntry00)

/--
The entry-00 tensor probe on `a ⊗ b` equals `a₀₀ * b₀₀`.
-/
@[simp]
theorem probe00_tmul_tprod (a : A) (b : Fin 1 → A) :
    probe00 (a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ b) = a 0 0 * (b 0) 0 0 := by
  change (TensorProduct.lid ℤ ℤ)
      ((TensorProduct.map (entry 0 0) tailEntry00) (a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ b)) = _
  rw [TensorProduct.map_tmul]
  change a 0 0 * ((PiTensorProduct.subsingletonEquiv
    (R := ℤ) (s := fun _ : Fin 1 => A) (0 : Fin 1)) (PiTensorProduct.tprod ℤ b)) 0 0 = _
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod]

/--
The degree-one Hochschild boundary of `E₀₁ ⊗ E₁₀` is the coefficient
`E₀₁E₁₀ - E₁₀E₀₁` with empty tensor tail.
-/
theorem b_one_word : ((bComplex ℤ A).d 1 0).hom degreeOneWord =
    (e01 * e10 - e10 * e01) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun i : Fin 0 => Fin.elim0 i) := by
  unfold degreeOneWord
  rw [bComplex_d ℤ A 0, ModuleCat.hom_sum, LinearMap.sum_apply, Fin.sum_univ_two]
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_smul]
  rw [ModuleCat.hom_neg, LinearMap.neg_apply]
  erw [regularFace_first_tprod, regularFace_last_tprod]
  have hfirst : ModuleCat.Algebra.Hochschild.hochschildDropFirst (fun _ : Fin 1 => e10) =
      (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  have hlast : ModuleCat.Algebra.Hochschild.hochschildDropLast (fun _ : Fin 1 => e10) =
      (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hfirst, hlast]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_zsmul, TensorProduct.sub_tmul, sub_eq_add_neg, TensorProduct.add_tmul, TensorProduct.neg_tmul]

/--
Applying `B₀` after the Hochschild boundary of the degree-one word gives
entry-00 tensor probe value `2`.
-/
theorem B_zero_b_one_value :
    probe00 ((connesBoundary ℤ A 0).hom (((bComplex ℤ A).d 1 0).hom degreeOneWord)) = 2 := by
  rw [b_one_word]
  erw [connesBoundary_zero_tprod]
  rw [map_add, probe00_tmul_tprod, probe00_tmul_tprod]
  norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

private theorem isolated_sign_defect {C : Type*} [Category C] [Preadditive C]
    (K : MixedComplex C) :
    K.B 1 ≫ K.underlying.d 2 1 + K.underlying.d 1 0 ≫ (-K.B 0) =
      -((2 : ℤ) • (K.underlying.d 1 0 ≫ K.B 0)) := by
  have h := K.B_comp_d_add_d_comp_B 0
  have hg : K.B 1 ≫ K.underlying.d 2 1 = -(K.underlying.d 1 0 ≫ K.B 0) :=
    eq_neg_of_add_eq_zero_left h
  rw [comp_neg, hg]
  simp only [two_zsmul]
  abel

/--
With the Hochschild differential unchanged and only `B₀` replaced by `-B₀`,
the degree-one mixed-law expression is `-2(B₀ ∘ b₁)`.
-/
theorem raw_B_only_mixed_defect :
    M.B 1 ≫ M.underlying.d 2 1 + M.underlying.d 1 0 ≫ (-M.B 0) =
      -((2 : ℤ) • (M.underlying.d 1 0 ≫ M.B 0)) := isolated_sign_defect M

private theorem raw_defect_linear :
    (M.B 1 ≫ M.underlying.d 2 1 + M.underlying.d 1 0 ≫ (-M.B 0)).hom =
      -((2 : ℤ) • (((connesBoundary ℤ A 0).hom).comp ((bComplex ℤ A).d 1 0).hom)) := by
  rw [raw_B_only_mixed_defect, ModuleCat.hom_neg, ModuleCat.hom_zsmul, ModuleCat.hom_comp]
  erw [connesMixedComplexModel_B ℤ A 0]
  congr 3

private theorem raw_linear_defect_value :
    probe00 ((-((2 : ℤ) • (((connesBoundary ℤ A 0).hom).comp
      ((bComplex ℤ A).d 1 0).hom))) degreeOneWord) = -4 := by
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, map_neg]
  rw [LinearMap.smul_apply, map_smul, LinearMap.comp_apply, B_zero_b_one_value]
  norm_num

/--
The entry-00 tensor probe of the isolated-sign mixed-law defect on the
specified degree-one word is `-4`.
-/
theorem raw_B_only_degree_one_defect_value :
    probe00 ((M.B 1 ≫ M.underlying.d 2 1 + M.underlying.d 1 0 ≫ (-M.B 0)).hom degreeOneWord) = -4 := by
  have h := LinearMap.congr_fun raw_defect_linear degreeOneWord
  exact (congrArg (fun y : A ⊗[ℤ] TensorPower ℤ 1 A => probe00 y) h).trans raw_linear_defect_value

end MathlibExtTest.LodayBCIntegerMatrices
