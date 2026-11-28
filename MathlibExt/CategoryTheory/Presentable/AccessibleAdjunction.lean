/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Presentable.Uniformization
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Accessibility of an actual original right adjoint

The actual working-small presentable-generator family in the original source
category gives a full faithful restricted Yoneda functor. Compactness of its
actual left-adjoint images makes the composite with the original right
adjoint preserve filtered colimits pointwise. Full-faithful reflection then
proves preservation by that same right functor.

For accessible endpoint categories the left-image compactness rank is
constructed internally. The original functors, Hom equivalence, unit and
counit are retained; no right-adjoint accessibility is a premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w vC vE uC uE uI

namespace CategoryTheory.Presentable.AccessibleAdjunction

open Limits Opposite

variable (C : Type uC) [Category.{vC} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalAccessibleCategory C κ]

/-- The actual small model of the ORIGINAL presentable-object subcategory. -/
abbrev generatorIndex := SmallModel.{w} (isCardinalPresentable C κ).FullSubcategory

/-- The actual original dense family uses that same native small-model equivalence. -/
def generator : generatorIndex C κ ⥤ C :=
  (equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).inverse ⋙
    (isCardinalPresentable C κ).ι

instance generatorIsDense : (generator C κ).IsDense := by
  dsimp [generator]
  infer_instance

instance generatorObjPresentable (s : generatorIndex C κ) :
    IsCardinalPresentable ((generator C κ).obj s) κ :=
  ((equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).inverse.obj s).property

/-- This original restricted Yoneda is used to reflect filtered colimits.
Its explicit auxiliary lift accommodates both original Hom universes. -/
def restrictedYoneda : C ⥤ (generatorIndex C κ)ᵒᵖ ⥤ Type max w vC vE :=
  Presheaf.restrictedULiftYoneda.{max w vE} (generator C κ)

instance restrictedYonedaFull : (restrictedYoneda.{w, vC, vE} C κ).Full := by
  dsimp [restrictedYoneda]
  infer_instance

instance restrictedYonedaFaithful : (restrictedYoneda.{w, vC, vE} C κ).Faithful := by
  dsimp [restrictedYoneda]
  infer_instance

variable {C κ} {E : Type uE} [Category.{vE} E] {L : C ⥤ E} {R : E ⥤ C}

/-- The component comparison is the actual adjunction Hom isomorphism,
including its original two Hom universes and both ULift functions. -/
def componentIso (a : L ⊣ R) (s : generatorIndex C κ) :
    (R ⋙ restrictedYoneda.{w, vC, vE} C κ) ⋙
        (evaluation (generatorIndex C κ)ᵒᵖ (Type max w vC vE)).obj (op s) ≅
      uliftCoyoneda.{max w vC}.obj (op (L.obj ((generator C κ).obj s))) :=
  (a.compUliftCoyonedaIso.{w}).symm.app (op ((generator C κ).obj s))

/-- The full forward component function is the original inverse Hom transpose. -/
theorem componentIso_hom_apply (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : (generator C κ).obj s ⟶ R.obj X) :
    (componentIso a s).hom.app X (ULift.up f) =
      ULift.up ((a.homEquiv _ X).symm f) := rfl

/-- The full inverse component function is the original forward Hom transpose. -/
theorem componentIso_inv_apply (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : L.obj ((generator C κ).obj s) ⟶ X) :
    (componentIso a s).inv.app X (ULift.up f) = ULift.up (a.homEquiv _ X f) := rfl

/-- The original counit determines the entire forward component function. -/
theorem componentIso_hom_counit (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : (generator C κ).obj s ⟶ R.obj X) :
    (componentIso a s).hom.app X (ULift.up f) =
      ULift.up (L.map f ≫ a.counit.app X) := by
  rw [componentIso_hom_apply, Adjunction.homEquiv_counit]

/-- The original unit determines the entire inverse component function. -/
theorem componentIso_inv_unit (a : L ⊣ R) (s : generatorIndex C κ) (X : E)
    (f : L.obj ((generator C κ).obj s) ⟶ X) :
    (componentIso a s).inv.app X (ULift.up f) =
      ULift.up (a.unit.app ((generator C κ).obj s) ≫ R.map f) := by
  rw [componentIso_inv_apply, Adjunction.homEquiv_unit]

/-- Actual compactness of the original small dense left images proves
filtered-colimit preservation by the SAME original right functor. -/
theorem right_isCardinalAccessible_of_generator_images
    (a : L ⊣ R) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : ∀ s : generatorIndex C κ,
      IsCardinalPresentable (L.obj ((generator C κ).obj s)) μ) :
    R.IsCardinalAccessible μ := by
  refine ⟨fun J _ _ ↦ ?_⟩
  let Y := restrictedYoneda.{w, vC, vE} C κ
  let : Y.Full := restrictedYonedaFull C κ
  let : Y.Faithful := restrictedYonedaFaithful C κ
  let : PreservesColimitsOfShape J (R ⋙ Y) :=
    preservesColimitsOfShape_of_evaluation (R ⋙ Y) J (fun s ↦ by
      have hs := h s.unop
      let : IsCardinalPresentable (L.obj ((generator C κ).obj s.unop)) μ := hs
      let : (uliftCoyoneda.{max w vC}.obj
        (op (L.obj ((generator C κ).obj s.unop)))).IsCardinalAccessible μ := inferInstance
      have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (uliftCoyoneda.{max w vC}.obj (op (L.obj ((generator C κ).obj s.unop)))) μ J
      exact preservesColimitsOfShape_of_natIso (componentIso a s.unop).symm)
  exact preservesColimitsOfShape_of_reflects_of_preserves R Y

/-- A whole original-presentable-family image bound is a sufficient fixed-rank criterion. -/
theorem right_isCardinalAccessible_of_left_images
    (a : L ⊣ R) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : isCardinalPresentable C κ ≤ (isCardinalPresentable E μ).inverseImage L) :
    R.IsCardinalAccessible μ :=
  right_isCardinalAccessible_of_generator_images (κ := κ) a μ
    (fun s ↦ h _ (generatorObjPresentable C κ s))

include κ in
/-- An actual accessible target supplies a compactness rank for the actual
small original left-image family, so no right accessibility is assumed. -/
theorem right_isAccessible [IsAccessibleCategory.{w} E] (a : L ⊣ R) :
    Functor.IsAccessible.{w} R := by
  obtain ⟨μ, _, hμ⟩ := ((isCardinalPresentable C κ).map L).le_isCardinalPresentable
  let : R.IsCardinalAccessible μ := right_isCardinalAccessible_of_left_images a μ
    (fun X hX ↦ hμ _ (ObjectProperty.prop_map_obj _ _ hX))
  exact Functor.isAccessible_of_isCardinalAccessible R μ

section BothAccessible

variable [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} E]

/-- The cardinal-free entry produces the original dense-generator rank internally. -/
theorem right_isAccessible_of_accessible (a : L ⊣ R) : Functor.IsAccessible.{w} R := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact right_isAccessible (κ := κ) a

/-- An actual small family of original adjunctions has a common compatible
regular rank, retaining both original functors and their compactness preservation. -/
theorem common_rank {I : Type uI} [Small.{w} I]
    (left : I → C ⥤ E) (right : I → E ⥤ C) (a : ∀ i, left i ⊣ right i) :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular),
      IsCardinalAccessibleCategory C μ ∧ IsCardinalAccessibleCategory E μ ∧
      (∀ i, (right i).IsCardinalAccessible μ) ∧
      (∀ i, (left i).IsCardinalAccessible μ) ∧
      (∀ i, (right i).PreservesCardinalPresentable μ) ∧
        ∀ i, (left i).PreservesCardinalPresentable μ := by
  let (i : I) : Functor.IsAccessible.{w} (right i) := right_isAccessible_of_accessible (a i)
  obtain ⟨μ, _, hE, hC, hR, hRP⟩ := IsCardinalAccessibleCategory.uniformization_of_small right
  let : IsCardinalAccessibleCategory C μ := hC
  let : IsCardinalAccessibleCategory E μ := hE
  let (i : I) : (right i).IsCardinalAccessible μ := hR i
  refine ⟨μ, inferInstance, hC, hE, hR, ?_, hRP, ?_⟩
  · intro i
    let : PreservesColimitsOfSize.{w, w} (left i) := (a i).leftAdjoint_preservesColimits
    infer_instance
  · intro i
    refine ⟨fun X hX ↦ ?_⟩
    let : IsCardinalPresentable X μ := hX
    exact (a i).isCardinalPresentable_leftAdjoint_obj μ X

end BothAccessible

end CategoryTheory.Presentable.AccessibleAdjunction
