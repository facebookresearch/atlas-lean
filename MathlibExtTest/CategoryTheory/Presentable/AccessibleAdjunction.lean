/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.AccessibleAdjunction
public import MathlibExt.CategoryTheory.Presentable.Completeness
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.SingleObj

/-!
# Entire original right-adjoint accessibility contracts

The generic contracts use the actual adjunction and its two Hom functions.
Concrete evaluation/cofree cases include empty, infinite, nonthin and raised
original diagram indices, with no right-accessibility premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w vC vE uC uE uI

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presentable.AccessibleAdjunctionTest

open AccessibleAdjunction

variable {C : Type uC} [Category.{vC} C] {E : Type uE} [Category.{vE} E]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ]
  {L : C ⥤ E} {R : E ⥤ C}

example (a : L ⊣ R) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : ∀ s : generatorIndex C κ,
      IsCardinalPresentable (L.obj ((generator C κ).obj s)) μ) :
    R.IsCardinalAccessible μ :=
  right_isCardinalAccessible_of_generator_images (κ := κ) a μ h

example [IsAccessibleCategory.{w} E] (a : L ⊣ R) : Functor.IsAccessible.{w} R :=
  right_isAccessible (κ := κ) a

example (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : (generator C κ).obj s ⟶ R.obj X) :
    (componentIso a s).hom.app X (ULift.up f) =
      ULift.up ((a.homEquiv _ X).symm f) :=
  componentIso_hom_apply a s X f

example (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : L.obj ((generator C κ).obj s) ⟶ X) :
    (componentIso a s).inv.app X (ULift.up f) = ULift.up (a.homEquiv _ X f) :=
  componentIso_inv_apply a s X f

example (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : (generator C κ).obj s ⟶ R.obj X) :
    (componentIso a s).hom.app X (ULift.up f) = ULift.up (L.map f ≫ a.counit.app X) :=
  componentIso_hom_counit a s X f

example (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : L.obj ((generator C κ).obj s) ⟶ X) :
    (componentIso a s).inv.app X (ULift.up f) =
      ULift.up (a.unit.app ((generator C κ).obj s) ≫ R.map f) :=
  componentIso_inv_unit a s X f

example (a : L ⊣ R) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : ∀ s : generatorIndex C κ,
      IsCardinalPresentable (L.obj ((generator C κ).obj s)) μ)
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ E) (c : Cocone F) (hc : IsColimit c) : IsColimit (R.mapCocone c) := by
  let : R.IsCardinalAccessible μ := right_isCardinalAccessible_of_generator_images (κ := κ) a μ h
  let : PreservesColimitsOfShape J R := R.preservesColimitsOfShape_of_isCardinalAccessible μ J
  exact isColimitOfPreserves R hc

section Common

variable [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} E]

example {I : Type uI} [Small.{w} I] (left : I → C ⥤ E) (right : I → E ⥤ C)
    (a : ∀ i, left i ⊣ right i) :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular),
      IsCardinalAccessibleCategory C μ ∧ IsCardinalAccessibleCategory E μ ∧
      (∀ i, (right i).IsCardinalAccessible μ) ∧
      (∀ i, (left i).IsCardinalAccessible μ) ∧
      (∀ i, (right i).PreservesCardinalPresentable μ) ∧
        ∀ i, (left i).PreservesCardinalPresentable μ :=
  common_rank left right a

end Common

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

local instance : IsAccessibleCategory.{0} (Type) where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

example : Functor.IsAccessible.{0} (𝟭 (Type)) :=
  right_isAccessible_of_accessible (Adjunction.id)

example : ∃ (μ : Cardinal.{0}) (_ : Fact μ.IsRegular),
    IsCardinalAccessibleCategory (Type) μ ∧ IsCardinalAccessibleCategory (Type) μ ∧
    (∀ _ : PEmpty.{1}, (𝟭 (Type)).IsCardinalAccessible μ) ∧
    (∀ _ : PEmpty.{1}, (𝟭 (Type)).IsCardinalAccessible μ) ∧
    (∀ _ : PEmpty.{1}, (𝟭 (Type)).PreservesCardinalPresentable μ) ∧
      ∀ _ : PEmpty.{1}, (𝟭 (Type)).PreservesCardinalPresentable μ :=
  common_rank (fun _ : PEmpty.{1} ↦ 𝟭 (Type)) (fun _ : PEmpty.{1} ↦ 𝟭 (Type))
    (fun _ ↦ Adjunction.id)

/-- This actual infinite nonthin index has infinitely many original endomorphisms. -/
abbrev Nonthin := SingleObj ℕ

example (d : Nonthin) :
    Functor.IsAccessible.{0}
      (Completeness.cofree (Type) Cardinal.aleph0.{0}
        (equivSmallModel.{0} Nonthin) d) := by
  let : HasPullbacks (Type) := inferInstance
  let : IsCardinalLocallyPresentable (Nonthin ⥤ Type) Cardinal.aleph0.{0} :=
    inferInstance
  let : IsAccessibleCategory.{0} (Nonthin ⥤ Type) :=
    ⟨Cardinal.aleph0, inferInstance, inferInstance⟩
  exact right_isAccessible_of_accessible
    (Completeness.evaluationCofreeAdjunction (Type) Cardinal.aleph0.{0}
      (equivSmallModel.{0} Nonthin) d)

example : IsAccessibleCategory.{0} (Discrete PEmpty.{1} ⥤ Type) := by
  let : IsCardinalLocallyPresentable (Discrete PEmpty.{1} ⥤ Type) Cardinal.aleph0.{0} :=
    inferInstance
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

example : IsAccessibleCategory.{0} (Discrete ℕ ⥤ Type) := by
  let : IsCardinalLocallyPresentable (Discrete ℕ ⥤ Type) Cardinal.aleph0.{0} :=
    inferInstance
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

example : IsAccessibleCategory.{0} (Discrete (ULift.{1} ℕ) ⥤ Type) := by
  let : IsCardinalLocallyPresentable (Discrete (ULift.{1} ℕ) ⥤ Type) Cardinal.aleph0.{0} :=
    inferInstance
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

end Concrete

end CategoryTheory.Presentable.AccessibleAdjunctionTest
