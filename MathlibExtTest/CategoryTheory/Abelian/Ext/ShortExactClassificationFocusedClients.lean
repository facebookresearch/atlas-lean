/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Abelian.Ext.ShortExactClassification
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ZMod.Basic

/-!
# Focused clients for the classification of extensions by Ext¹

Over `ℤ`, the split extension `0 → ℤ/2 → ℤ/2 ⊞ ℤ/2 → ℤ/2 → 0` and the extension
`0 → ℤ/2 → ℤ/4 → ℤ/2 → 0` are not related by an endpoint-fixing isomorphism:
the middle term of the first is killed by `2`, while `1 : ℤ/4` is not. The
classification therefore separates them, so the second extension has a nonzero
class in `Ext¹(ℤ/2, ℤ/2)`, and the classifying equivalence sends the split class
to `0`.
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace MathlibExtTest.CategoryTheory.Abelian.Ext.ShortExactClassificationFocusedClients

open CategoryTheory.ShortExactSequence.WithEndpoints

/-- The category of abelian groups has Ext groups in the same universe. -/
instance : HasExt.{0} (ModuleCat.{0} ℤ) := hasExt_of_enoughInjectives.{0} _

/-- The group `ℤ/2`. -/
abbrev Z2 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)

/-- The group `ℤ/4`. -/
abbrev Z4 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)

/-- Multiplication by `2`, from `ℤ/2` to `ℤ/4`. -/
def double : Z2 ⟶ Z4 :=
  ModuleCat.ofHom (ZMod.lift 2 ⟨zmultiplesHom (ZMod 4) 2, by decide⟩).toIntLinearMap

/-- Reduction modulo `2`, from `ℤ/4` to `ℤ/2`. -/
def reduce : Z4 ⟶ Z2 :=
  ModuleCat.ofHom (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)).toAddMonoidHom.toIntLinearMap

theorem double_reduce : double ≫ reduce = 0 := by
  ext x
  fin_cases x <;> rfl

theorem shortExact : (ShortComplex.mk double reduce double_reduce).ShortExact := by
  have hf : Function.Injective double.hom := by
    intro x y h
    fin_cases x <;> fin_cases y <;> first | rfl | exact absurd h (by decide)
  have hg : Function.Surjective reduce.hom := by
    intro y
    fin_cases y
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have hm : Mono double := (ModuleCat.mono_iff_injective _).2 hf
  have he : Epi reduce := (ModuleCat.epi_iff_surjective _).2 hg
  refine ShortComplex.ShortExact.mk' ?_ hm he
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  fin_cases y
  · exact ⟨0, rfl⟩
  · exact absurd hy (by decide)
  · exact ⟨1, rfl⟩
  · exact absurd hy (by decide)

/-- The extension `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`. -/
def nonsplit : ShortExactSequence.WithEndpoints Z2 Z2 := mk double reduce double_reduce shortExact

theorem two_smul_id_Z2 : (2 : ℤ) • 𝟙 Z2 = 0 := by
  ext x
  fin_cases x <;> rfl

/-- The middle term of the split extension is killed by `2`. -/
theorem two_smul_id_split : (2 : ℤ) • 𝟙 (split Z2 Z2).complex.X₂ = 0 := by
  change (2 : ℤ) • 𝟙 (Z2 ⊞ Z2) = 0
  apply biprod.hom_ext
  · rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (biprod.fst : Z2 ⊞ Z2 ⟶ Z2), ← Preadditive.comp_zsmul, two_smul_id_Z2,
      comp_zero]
  · rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (biprod.snd : Z2 ⊞ Z2 ⟶ Z2), ← Preadditive.comp_zsmul, two_smul_id_Z2,
      comp_zero]

/-- No endpoint-fixing isomorphism relates the split and the `ℤ/4` extensions. -/
theorem not_rel_split_nonsplit : ¬ Rel (split Z2 Z2) nonsplit := by
  rintro ⟨h, -, -⟩
  let e : (split Z2 Z2).complex.X₂ ≅ Z4 := ShortComplex.π₂.mapIso h
  have h4 : (2 : ℤ) • 𝟙 Z4 = 0 := by
    calc (2 : ℤ) • 𝟙 Z4 = e.inv ≫ ((2 : ℤ) • 𝟙 (split Z2 Z2).complex.X₂) ≫ e.hom := by simp
      _ = 0 := by rw [two_smul_id_split]; simp
  have h1 := congrArg (fun f : Z4 ⟶ Z4 ↦ f.hom (1 : ZMod 4)) h4
  exact absurd h1 (by decide)

/-- The two extensions have different classes. -/
example : classOf (split Z2 Z2) ≠ classOf nonsplit := fun h ↦
  not_rel_split_nonsplit (rel_of_classOf_eq h)

/-- The `ℤ/4` extension has a nonzero class in `Ext¹(ℤ/2, ℤ/2)`. -/
theorem extClass_nonsplit_ne_zero : extClass.{0} nonsplit ≠ 0 := fun h ↦
  not_rel_split_nonsplit (rel_of_extClass_eq (by rw [extClass_split, h]))

/-- The classifying equivalence sends the split class to `0` and separates the
two classes. -/
example :
    classifyingEquiv.{0} (classOf (split Z2 Z2)) = 0 ∧
      classifyingEquiv.{0} (classOf nonsplit) ≠ 0 := by
  rw [classifyingEquiv_classOf, classifyingEquiv_classOf, extClass_split]
  exact ⟨rfl, extClass_nonsplit_ne_zero⟩

end MathlibExtTest.CategoryTheory.Abelian.Ext.ShortExactClassificationFocusedClients
