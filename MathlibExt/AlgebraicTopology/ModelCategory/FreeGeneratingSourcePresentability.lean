/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Presentable.SmallFamily
import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
import MathlibExt.CategoryTheory.SmallObject.RelativeSourceSmallness
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# Presentability and relative smallness of original free generating sources

An actual adjunction carries the original presentable generator endpoints to
presentable free endpoints when its right functor preserves the specified
filtered colimits. A small pair of original generator families has one
constructed regular upper rank. The same original free arrows and relative
cell diagrams then satisfy the source Hom preservation and small-object
eligibility contracts.
-/

noncomputable section
set_option autoImplicit false

universe w uC vC uD vD uJ vJ

namespace CategoryTheory.FreeGeneratingSource

open Limits Opposite MorphismProperty SmallObject

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {F : C ⥤ D} {U : D ⥤ C}

/-- The original sources and targets of both original generator families.
The Boolean selects the source (`false`) or target (`true`). -/
def endpoint (I J : MorphismProperty C) : (I.toSet ⊕ J.toSet) × Bool → C
  | (.inl i, false) => i.1.left
  | (.inl i, true) => i.1.right
  | (.inr j, false) => j.1.left
  | (.inr j, true) => j.1.right

/-- Every original free endpoint is presentable at the supplied regular rank. -/
theorem freeEndpoints_presentable (adj : F ⊣ U)
    (I J : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [U.IsCardinalAccessible κ]
    (h : ∀ s, IsCardinalPresentable (endpoint I J s) κ) :
    ∀ s, IsCardinalPresentable (F.obj (endpoint I J s)) κ := by
  intro s
  let : IsCardinalPresentable (endpoint I J s) κ := h s
  exact adj.isCardinalPresentable_leftAdjoint_obj κ (endpoint I J s)

/-- The actual free arrow is the original functor applied to the supplied generator map. -/
theorem original_free_arrow {I : MorphismProperty C} (i : I.toSet) :
    (I.strictMap F) (F.map i.1.hom) := .map i.2

/-- The small original I/J source and target family has a common regular rank,
at least the original right-functor preservation rank. Both original and free
endpoints are presentable there, and the same right functor preserves it. -/
theorem exists_common_free_endpoint_rank (adj : F ⊣ U)
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [IsLocallyPresentable.{w} C]
    (κ₀ : Cardinal.{w}) [Fact κ₀.IsRegular] [U.IsCardinalAccessible κ₀] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧
      U.IsCardinalAccessible κ ∧
      (∀ s, IsCardinalPresentable (endpoint I J s) κ) ∧
      (∀ s, IsCardinalPresentable (F.obj (endpoint I J s)) κ) := by
  obtain ⟨κ₁, hκ₁, hEndpoints⟩ := exists_cardinalPresentable_small_family (endpoint I J)
  let : Fact κ₁.IsRegular := hκ₁
  let κ := max κ₀ κ₁
  let : Fact κ.IsRegular := by
    rcases le_total κ₀ κ₁ with h | h
    · simpa [κ, max_eq_right h] using hκ₁
    · simpa [κ, max_eq_left h] using (inferInstance : Fact κ₀.IsRegular)
  have h₀ : κ₀ ≤ κ := le_max_left _ _
  have h₁ : κ₁ ≤ κ := le_max_right _ _
  let : U.IsCardinalAccessible κ := U.isCardinalAccessible_of_le h₀
  have hC (s) : IsCardinalPresentable (endpoint I J s) κ := by
    let : IsCardinalPresentable (endpoint I J s) κ₁ := hEndpoints s
    exact isCardinalPresentable_of_le (endpoint I J s) h₁
  exact ⟨κ, inferInstance, h₀, inferInstance, hC, freeEndpoints_presentable adj I J κ hC⟩

/-- A presentable original free source preserves every supplied filtered
diagram at the same source rank and original index universes. -/
theorem freeSource_preservesColimitsOfShape (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [U.IsCardinalAccessible κ]
    (X : C) [IsCardinalPresentable X κ]
    (J : Type uJ) [Category.{vJ} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op (F.obj X))) := by
  let : IsCardinalPresentable (F.obj X) κ := adj.isCardinalPresentable_leftAdjoint_obj κ X
  exact preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall (F.obj X) κ J

/-- The actual supplied cocone, with every original colimit leg, remains
colimiting after Hom from the original free source. -/
def freeSourceMappedCocone (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [U.IsCardinalAccessible κ]
    (X : C) [IsCardinalPresentable X κ]
    {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    (K : J ⥤ D) (c : Cocone K) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op (F.obj X))).mapCocone c) := by
  let : PreservesColimitsOfShape J (coyoneda.obj (op (F.obj X))) :=
    freeSource_preservesColimitsOfShape adj κ X J
  exact isColimitOfPreserves (coyoneda.obj (op (F.obj X))) hc

/-- Every original arrow from a free source to the supplied colimit factors
through an original stage, using its unchanged cocone leg. -/
theorem freeSource_exists_stage (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [U.IsCardinalAccessible κ]
    (X : C) [IsCardinalPresentable X κ]
    {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    (K : J ⥤ D) (c : Cocone K) (hc : IsColimit c) (f : F.obj X ⟶ c.pt) :
    ∃ j, ∃ g : F.obj X ⟶ K.obj j, g ≫ c.ι.app j = f := by
  let : PreservesColimitsOfShape J (coyoneda.obj (op (F.obj X))) :=
    freeSource_preservesColimitsOfShape adj κ X J
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  exact exists_hom_of_preservesColimit_coyoneda hc f

/-- Equality at the supplied colimit is witnessed at an actual common later
stage, preserving both original maps and the original diagram transitions. -/
theorem freeSource_exists_stage_equality (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [U.IsCardinalAccessible κ]
    (X : C) [IsCardinalPresentable X κ]
    {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    (K : J ⥤ D) (c : Cocone K) (hc : IsColimit c) {i j : J}
    (f : F.obj X ⟶ K.obj i) (g : F.obj X ⟶ K.obj j)
    (hfg : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ k, ∃ a : i ⟶ k, ∃ b : j ⟶ k, f ≫ K.map a = g ≫ K.map b := by
  let : PreservesColimitsOfShape J (coyoneda.obj (op (F.obj X))) :=
    freeSource_preservesColimitsOfShape adj κ X J
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda hc f g hfg

/-- The smallness field for an actual original relative-cell complex follows
from source presentability, independently of its particular cell labels. -/
theorem freeSource_relativeComplex_preservesColimit (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [U.IsCardinalAccessible κ] (X : C) [IsCardinalPresentable X κ]
    (P : MorphismProperty D) {A B : D} {f : A ⟶ B}
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op (F.obj X))) := by
  let : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op (F.obj X))) :=
    freeSource_preservesColimitsOfShape adj κ X κ.ord.ToType
  infer_instance

/-- Hom from the original free source preserves the supplied relative-cell
endpoint cocone with exactly its original inclusion natural transformation. -/
def freeSourceRelativeComplexMappedCocone (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [U.IsCardinalAccessible κ] (X : C) [IsCardinalPresentable X κ]
    (P : MorphismProperty D) {A B : D} {f : A ⟶ B}
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    IsColimit ((coyoneda.obj (op (F.obj X))).mapCocone (Cocone.mk B c.incl)) := by
  let : PreservesColimit c.F (coyoneda.obj (op (F.obj X))) :=
    freeSource_relativeComplex_preservesColimit adj κ X P c
  exact isColimitOfPreserves (coyoneda.obj (op (F.obj X))) c.isColimit

/-- Every map to the actual relative-cell endpoint factors through one of
its original stages and the original endpoint inclusion. -/
theorem freeSource_relativeComplex_exists_stage (adj : F ⊣ U)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [U.IsCardinalAccessible κ] (X : C) [IsCardinalPresentable X κ]
    (P : MorphismProperty D) {A B : D} {f : A ⟶ B}
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) (g : F.obj X ⟶ B) :
    ∃ j, ∃ h : F.obj X ⟶ c.F.obj j, h ≫ c.incl.app j = g :=
  freeSource_exists_stage adj κ X c.F (Cocone.mk B c.incl) c.isColimit g

/-- Presentable original free sources satisfy the full same-chain uniform
relative-cell smallness predicate, with the supplied κ as their bound. -/
theorem freeSources_uniformRelativeSmallness (adj : F ⊣ U)
    (I : MorphismProperty C) (κ₀ : Cardinal.{w}) [Fact κ₀.IsRegular]
    [U.IsCardinalAccessible κ₀]
    (hI : ∀ i : I.toSet, IsCardinalPresentable i.1.left κ₀) :
    UniformRelativeSourceSmallness.{w} (I.strictMap F) := by
  rintro ⟨⟨_, _, f⟩, hf⟩
  cases hf with
  | @map A B i hi =>
    refine ⟨κ₀, ?_⟩
    intro κ _ _ hκ K _ _
    let : IsCardinalPresentable A κ₀ := hI ⟨Arrow.mk i, hi⟩
    let : IsCardinalPresentable (F.obj A) κ₀ := adj.isCardinalPresentable_leftAdjoint_obj κ₀ A
    let : IsCardinalPresentable (F.obj A) κ := isCardinalPresentable_of_le (F.obj A) hκ.le
    let : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op (F.obj A))) :=
      preservesColimitsOfShape_of_isCardinalPresentable (F.obj A) κ κ.ord.ToType
    infer_instance

/-- The actual free images of both source families have the full uniform
relative-cell source-smallness predicates at an internally produced rank. -/
theorem exists_common_uniform_free_source_smallness (adj : F ⊣ U)
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [IsLocallyPresentable.{w} C]
    (κ₀ : Cardinal.{w}) [Fact κ₀.IsRegular] [U.IsCardinalAccessible κ₀] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧
      (∀ s, IsCardinalPresentable (F.obj (endpoint I J s)) κ) ∧
      UniformRelativeSourceSmallness.{w} (I.strictMap F) ∧
      UniformRelativeSourceSmallness.{w} (J.strictMap F) := by
  obtain ⟨κ, hκ, hκ₀, hU, hC, hD⟩ := exists_common_free_endpoint_rank adj I J κ₀
  let : Fact κ.IsRegular := hκ
  let : U.IsCardinalAccessible κ := hU
  exact ⟨κ, hκ, hκ₀, hD,
    freeSources_uniformRelativeSmallness adj I κ (fun i => hC (.inl i, false)),
    freeSources_uniformRelativeSmallness adj J κ (fun j => hC (.inr j, false))⟩

/-- The complete original small-object eligibility dictionary follows from
actual source presentability and the stated original colimit constructions.
The relative complex and its source/endpoint maps are not replaced. -/
theorem eligibility_of_presentable_sources (P : MorphismProperty D)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [P.IsSmall.{w}] [LocallySmall.{w} D] [HasPushouts D] [HasCoproducts.{w} D]
    [HasIterationOfShape κ.ord.ToType D]
    (hP : ∀ p : P.toSet, IsCardinalPresentable p.1.left κ) :
    P.IsCardinalForSmallObjectArgument κ where
  preservesColimit := by
    intro A B X Y i hi f c
    let : IsCardinalPresentable A κ := hP ⟨Arrow.mk i, hi⟩
    let : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op A)) :=
      preservesColimitsOfShape_of_isCardinalPresentable A κ κ.ord.ToType
    infer_instance

/-- Both original free generator families have complete eligibility at a
constructed regular upper rank, retaining their actual strict functor images. -/
theorem exists_common_free_generation_cardinal (adj : F ⊣ U)
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [IsLocallyPresentable.{w} C]
    (κ₀ : Cardinal.{w}) [Fact κ₀.IsRegular] [U.IsCardinalAccessible κ₀]
    [LocallySmall.{w} D] [HasPushouts D] [HasCoproducts.{w} D]
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType D) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      κ₀ ≤ κ ∧
      (∀ s, IsCardinalPresentable (F.obj (endpoint I J s)) κ) ∧
      (I.strictMap F).IsCardinalForSmallObjectArgument κ ∧
      (J.strictMap F).IsCardinalForSmallObjectArgument κ := by
  obtain ⟨κ, hκ, hκ₀, hU, _, hD⟩ := exists_common_free_endpoint_rank adj I J κ₀
  let : Fact κ.IsRegular := hκ
  let : U.IsCardinalAccessible κ := hU
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let bottom : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let : OrderBot κ.ord.ToType := bottom
  let : HasIterationOfShape κ.ord.ToType D := hIteration κ
  let : (I.strictMap F).IsSmall.{w} := IsSmall.strictMap (inferInstance : I.IsSmall.{w}) F
  let : (J.strictMap F).IsSmall.{w} := IsSmall.strictMap (inferInstance : J.IsSmall.{w}) F
  have hI : ∀ p : (I.strictMap F).toSet, IsCardinalPresentable p.1.left κ := by
    rintro ⟨⟨_, _, _⟩, h⟩
    cases h with
    | map hi => exact hD (.inl ⟨Arrow.mk _, hi⟩, false)
  have hJ : ∀ p : (J.strictMap F).toSet, IsCardinalPresentable p.1.left κ := by
    rintro ⟨⟨_, _, _⟩, h⟩
    cases h with
    | map hj => exact hD (.inr ⟨Arrow.mk _, hj⟩, false)
  exact ⟨κ, hκ, bottom, hκ₀, hD,
    eligibility_of_presentable_sources (I.strictMap F) κ hI,
    eligibility_of_presentable_sources (J.strictMap F) κ hJ⟩

end CategoryTheory.FreeGeneratingSource
