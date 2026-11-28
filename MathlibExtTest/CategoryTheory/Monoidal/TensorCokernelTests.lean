/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
import MathlibExt.CategoryTheory.Monoidal.TensorCokernel
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Tensor descent for nonzero torsion relations

Multiplication modulo two on `ZMod 4 ⊗[ℤ] ZMod 6` kills multiplication by two
in both factors. It descends through the two genuine cokernel projections and
takes their tensor class of `(1,1)` to the nonzero element of `ZMod 2`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace MathlibExtTest.TensorCokernel

private abbrev A : Ab.{0} := AddCommGrpCat.of (ZMod 4)
private abbrev B : Ab.{0} := AddCommGrpCat.of (ZMod 6)
private abbrev D : Ab.{0} := AddCommGrpCat.of (ZMod 2)

private def castA : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
private def castB : ZMod 6 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)

private def multiplication : A ⊗ B ⟶ D :=
  AddCommGrpCat.ofHom
    ((LinearMap.mul' ℤ (ZMod 2)).comp
      (TensorProduct.map castA.toAddMonoidHom.toIntLinearMap
        castB.toAddMonoidHom.toIntLinearMap)).toAddMonoidHom

private lemma multiplication_tmul (x : A) (y : B) :
    multiplication (x ⊗ₜ[ℤ] y) = castA x * castB y := by
  change (LinearMap.mul' ℤ (ZMod 2))
    (TensorProduct.map castA.toAddMonoidHom.toIntLinearMap
      castB.toAddMonoidHom.toIntLinearMap (x ⊗ₜ[ℤ] y)) = _
  simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

private theorem tensor_ext {X Y Z : Ab.{0}} {f g : X ⊗ Y ⟶ Z}
    (h : ∀ x y, f (x ⊗ₜ[ℤ] y) = g (x ⊗ₜ[ℤ] y)) : f = g := by
  apply ConcreteCategory.ext_apply
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => simp only [map_add, hx, hy]

private def twiceA : A ⟶ A := (2 : ℤ) • 𝟙 A
private def twiceB : B ⟶ B := (2 : ℤ) • 𝟙 B

private lemma kills_relations :
    coprod.desc (twiceA ▷ B) (A ◁ twiceB) ≫ multiplication = 0 := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, comp_zero]
    apply tensor_ext
    intro x y
    norm_num [twiceA, AddCommGrpCat.whiskerRight_apply, multiplication_tmul,
      map_zsmul, zsmul_eq_mul, castA, castB]
  · rw [coprod.inr_desc_assoc, comp_zero]
    apply tensor_ext
    intro x y
    norm_num [twiceB, AddCommGrpCat.whiskerLeft_apply, multiplication_tmul,
      map_zsmul, zsmul_eq_mul, castA, castB]

private def descended : cokernel twiceA ⊗ cokernel twiceB ⟶ D :=
  tensorCokernelDesc twiceA twiceB multiplication kills_relations

example : MonoidalPreadditive Ab.{0} := inferInstance
example : PreservesColimitsOfSize.{0, 0} (tensorRight A) := inferInstance

example : twiceA (1 : ZMod 4) ≠ 0 := by
  change (2 : ZMod 4) ≠ 0
  norm_num
example : twiceB (1 : ZMod 6) ≠ 0 := by
  change (2 : ZMod 6) ≠ 0
  norm_num

example :
    descended ((cokernel.π twiceA ⊗ₘ cokernel.π twiceB)
      ((1 : ZMod 4) ⊗ₜ[ℤ] (1 : ZMod 6))) = 1 := by
  have h := tensor_cokernel_π_comp_tensorCokernelDesc
    twiceA twiceB multiplication kills_relations
  have he := ConcreteCategory.congr_hom h ((1 : ZMod 4) ⊗ₜ[ℤ] (1 : ZMod 6))
  exact he.trans (by rw [multiplication_tmul]; norm_num [castA, castB])

-- This abstract client cannot supply the omitted coproduct or third preservation hypothesis.
example {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] {X₁ Y₁ X₂ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCokernel f₁] [HasCokernel f₂]
    [PreservesColimit (parallelPair f₂ 0) (tensorLeft (cokernel f₁))]
    [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)] :
    Epi (cokernel.π f₁ ⊗ₘ cokernel.π f₂) := epi_tensor_cokernel_π f₁ f₂

end MathlibExtTest.TensorCokernel
