/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Category.Grp.ForgetCorepresentable
public import MathlibExt.Algebra.Category.Grp.ULiftZModuleEquivalence
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.SetTheory.Cardinal.Regular

/-!
# A canonical generator for modules over the lifted integers

This file packages the regular module over `ULift ℤ` as the canonical
projective, finitely presentable separator used by integral excision arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

universe u


namespace ModuleCat

/-- The regular module over `ULift ℤ`, used as the canonical excision
generator. -/
noncomputable abbrev uliftIntGenerator :
    ModuleCat.{u} (ULift.{u} ℤ) :=
  ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)

/-- The monoid structure on the lifted-integer coefficient module corresponding
to the tensor-unit monoid. -/
noncomputable instance uliftIntGenerator_monObj :
    MonObj (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) :=
  inferInstanceAs (MonObj (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))))

/-- The canonical lifted-integer generator is finitely presentable for
diagrams in the ambient universe. -/
noncomputable instance uliftIntGenerator_isFinitelyPresentable :
    IsFinitelyPresentable.{u} (uliftIntGenerator.{u}) := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact (isCardinalPresentable_iff_of_isEquivalence
    (X := uliftIntGenerator.{u}) Cardinal.aleph0
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).mp
      (inferInstance : IsFinitelyPresentable.{u} (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- The canonical lifted-integer generator separates morphisms. -/
theorem uliftIntGenerator_isSeparator :
    IsSeparator (uliftIntGenerator.{u}) := by
  intro X Y f g h
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff,
    ModuleCat.hom_comp, LinearMap.ext_iff, LinearMap.coe_comp,
    Function.comp_apply, forall_eq'] at h
  ext x
  have hx := h (ModuleCat.ofHom
    (LinearMap.toSpanSingleton (ULift.{u} ℤ) X x)) 1
  change f.hom ((LinearMap.toSpanSingleton (ULift.{u} ℤ) X x) 1) =
    g.hom ((LinearMap.toSpanSingleton (ULift.{u} ℤ) X x) 1) at hx
  simpa only [LinearMap.toSpanSingleton_apply_one] using hx

end ModuleCat
