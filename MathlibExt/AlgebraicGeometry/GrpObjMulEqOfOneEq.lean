/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq.lean`
and
`P2M/Sol/S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.ExistsEqPullbackSndComp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Tactic

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open CategoryTheory.Limits

theorem AlgebraicGeometry.GrpObj.mul_eq_of_one_eq {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced (CategoryTheory.Limits.pullback x x)]
    (G₁ G₂ : GrpObj (Over.mk x)) (h : G₁.one = G₂.one) : G₁.mul = G₂.mul := by
  classical

  let θ : Over.mk x ⊗ Over.mk x ⟶ Over.mk x :=
    lift G₁.mul (G₂.mul ≫ G₂.inv) ≫ G₂.mul

  let sliceR : Over.mk x ⟶ Over.mk x ⊗ Over.mk x := lift (𝟙 _) (toUnit _ ≫ G₂.one)
  let sliceL : Over.mk x ⟶ Over.mk x ⊗ Over.mk x := lift (toUnit _ ≫ G₂.one) (𝟙 _)

  have h1R : sliceR ≫ G₁.mul = 𝟙 (Over.mk x) := by
    rw [show sliceR = lift (𝟙 _) (toUnit _ ≫ G₁.one) by rw [h]]
    letI : MonObj (Over.mk x) := G₁.toMonObj
    exact MonObj.lift_comp_one_right _ _
  have h2R : sliceR ≫ G₂.mul = 𝟙 (Over.mk x) := by
    letI : MonObj (Over.mk x) := G₂.toMonObj
    exact MonObj.lift_comp_one_right _ _
  have h1L : sliceL ≫ G₁.mul = 𝟙 (Over.mk x) := by
    rw [show sliceL = lift (toUnit _ ≫ G₁.one) (𝟙 _) by rw [h]]
    letI : MonObj (Over.mk x) := G₁.toMonObj
    exact MonObj.lift_comp_one_left _ _
  have h2L : sliceL ≫ G₂.mul = 𝟙 (Over.mk x) := by
    letI : MonObj (Over.mk x) := G₂.toMonObj
    exact MonObj.lift_comp_one_left _ _
  have hR : sliceR ≫ θ = toUnit _ ≫ G₂.one := by
    have e1 : sliceR ≫ θ
        = lift (sliceR ≫ G₁.mul) (sliceR ≫ (G₂.mul ≫ G₂.inv)) ≫ G₂.mul := by
      rw [show sliceR ≫ θ = (sliceR ≫ lift G₁.mul (G₂.mul ≫ G₂.inv)) ≫ G₂.mul by
        rw [Category.assoc], comp_lift]
    rw [e1, h1R, show sliceR ≫ (G₂.mul ≫ G₂.inv) = G₂.inv by
      rw [← Category.assoc, h2R, Category.id_comp]]
    letI : GrpObj (Over.mk x) := G₂
    exact GrpObj.right_inv _
  have hL : sliceL ≫ θ = toUnit _ ≫ G₂.one := by
    have e1 : sliceL ≫ θ
        = lift (sliceL ≫ G₁.mul) (sliceL ≫ (G₂.mul ≫ G₂.inv)) ≫ G₂.mul := by
      rw [show sliceL ≫ θ = (sliceL ≫ lift G₁.mul (G₂.mul ≫ G₂.inv)) ≫ G₂.mul by
        rw [Category.assoc], comp_lift]
    rw [e1, h1L, show sliceL ≫ (G₂.mul ≫ G₂.inv) = G₂.inv by
      rw [← Category.assoc, h2L, Category.id_comp]]
    letI : GrpObj (Over.mk x) := G₂
    exact GrpObj.right_inv _

  have hy₀ : (G₂.one).left ≫ x = 𝟙 (Spec (CommRingCat.of K)) := by
    have hw := Over.w (G₂.one)
    simp only [Over.mk_hom, Over.tensorUnit_hom] at hw
    exact hw
  have hcontr : pullback.lift (𝟙 X) (x ≫ (G₂.one).left)
      (show 𝟙 X ≫ x = (x ≫ (G₂.one).left) ≫ x by
        rw [Category.id_comp, Category.assoc]
        exact (Category.comp_id x).symm.trans (congrArg (x ≫ ·) hy₀.symm)) ≫ θ.left
      = x ≫ (G₂.one).left := by
    have hc := congrArg CommaMorphism.left hR
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_left, Over.mk_hom] at hc
    convert hc using 2
    rfl
    rfl
    rfl
    rfl
  obtain ⟨g, hg⟩ := AlgebraicGeometry.exists_eq_pullback_snd_comp_of_isProper
    x x x θ.left (by simpa using θ.w) (G₂.one).left hy₀ (G₂.one).left hcontr

  have hgval : g = x ≫ (G₂.one).left := by
    have hsl := congrArg CommaMorphism.left hL
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_left, Over.mk_hom] at hsl
    have hsnd : (sliceL.left) ≫ pullback.snd x x = 𝟙 X := by
      show (CartesianMonoidalCategory.lift (toUnit (Over.mk x) ≫ G₂.one)
        (𝟙 (Over.mk x))).left ≫ pullback.snd x x = 𝟙 X
      rw [Over.lift_left]
      exact pullback.lift_snd _ _ _
    have hstep : sliceL.left ≫ pullback.snd x x ≫ g = sliceL.left ≫ θ.left :=
      congrArg (fun t => sliceL.left ≫ t) hg.symm
    have hlast : sliceL.left ≫ θ.left = x ≫ (G₂.one).left := by
      simpa only [sliceL, Over.lift_left, Over.toUnit_left, Over.id_left,
        Over.mk_left, Over.mk_hom] using hsl
    exact (Category.id_comp g).symm.trans
      (((congrArg (fun t => t ≫ g) hsnd).symm.trans (Category.assoc _ _ _)).trans
        (hstep.trans hlast))

  have hθ : θ = toUnit _ ≫ G₂.one := by
    apply Over.OverMorphism.ext
    rw [hg, hgval]
    simp only [Over.comp_left, Over.toUnit_left]
    change pullback.snd x x ≫ x ≫ (G₂.one).left
      = (pullback.fst x x ≫ x) ≫ (G₂.one).left
    rw [Category.assoc]
    exact (pullback.condition_assoc _).symm

  letI : GrpObj (Over.mk x) := G₂
  have hcancel := (GrpObj.lift_inv_right_eq G₁.mul G₂.mul (toUnit _ ≫ G₂.one)).mp hθ
  rw [hcancel]
  exact MonObj.lift_comp_one_left _ _
