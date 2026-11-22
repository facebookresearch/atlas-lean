/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.ConstructionIndependence
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalInjectiveProperness
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Coefficient Quillen transport on original ordinary diagrams

Postcomposition uses the native whiskering adjunction and its original unit,
counit, actions and adjunct functions. The conventional combinatorial source
factories construct both diagram models internally. Their actual pointwise
right or left classes prove that this same adjunction is Quillen. Cofibrant
and fibrant diagrams have genuine cofibrant and fibrant coefficient objects;
the coefficient Hovey criterion then proves both diagram Quillen equivalences.

This is the complete coefficient assertion of *Higher Topos Theory*, Remark
A.2.8.6, supplied author version of April 9, 2017, printed pages 832–833
(PDF pages 850–851), extended through the actual essentially small index.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uC vC uE vE

namespace HomotopicalAlgebra.FunctorCoefficientQuillen

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.MorphismProperty

section NativeAdjunction

variable (D : Type uD) [Category.{vD} D]
  {C : Type uC} [Category.{vC} C] {E : Type uE} [Category.{vE} E]
  {L : C ⥤ E} {R : E ⥤ C} (a : L ⊣ R)

/-- The exact native postcomposition adjunction on the original functor categories. -/
def adjunction : (whiskeringRight D C E).obj L ⊣ (whiskeringRight D E C).obj R :=
  a.whiskerRight D

/-- No new adjunction data replace the native whiskering construction. -/
theorem adjunction_eq_native : adjunction D a = a.whiskerRight D := rfl

/-- Postcomposition preserves every original source diagram action. -/
theorem left_action (X : D ⥤ C) {d e : D} (f : d ⟶ e) :
    (((whiskeringRight D C E).obj L).obj X).map f = L.map (X.map f) := rfl

/-- The right functor likewise retains every original target diagram action. -/
theorem right_action (Y : D ⥤ E) {d e : D} (f : d ⟶ e) :
    (((whiskeringRight D E C).obj R).obj Y).map f = R.map (Y.map f) := rfl

/-- Every original natural-transformation component is mapped by the actual left functor. -/
theorem left_map_app {X Y : D ⥤ C} (f : X ⟶ Y) (d : D) :
    (((whiskeringRight D C E).obj L).map f).app d = L.map (f.app d) := rfl

/-- Every right component is the actual coefficient right-functor map. -/
theorem right_map_app {X Y : D ⥤ E} (f : X ⟶ Y) (d : D) :
    (((whiskeringRight D E C).obj R).map f).app d = R.map (f.app d) := rfl

/-- The unit retains the original coefficient unit at every original index object. -/
theorem unit_app_app (X : D ⥤ C) (d : D) :
    ((adjunction D a).unit.app X).app d = a.unit.app (X.obj d) :=
  CategoryTheory.Adjunction.whiskerRight_unit_app_app D a X d

/-- The counit retains the original coefficient counit at every object. -/
theorem counit_app_app (Y : D ⥤ E) (d : D) :
    ((adjunction D a).counit.app Y).app d = a.counit.app (Y.obj d) :=
  CategoryTheory.Adjunction.whiskerRight_counit_app_app D a Y d

/-- The original full adjunct function acts by the actual coefficient adjuncts. -/
theorem homEquiv_app (X : D ⥤ C) (Y : D ⥤ E)
    (f : ((whiskeringRight D C E).obj L).obj X ⟶ Y) (d : D) :
    ((adjunction D a).homEquiv X Y f).app d =
      a.homEquiv (X.obj d) (Y.obj d) (f.app d) := by
  rw [CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Adjunction.homEquiv_unit]
  change ((adjunction D a).unit.app X).app d ≫ R.map (f.app d) = _
  rw [unit_app_app]

/-- The full inverse adjunct function retains the same original coefficient data. -/
theorem homEquiv_symm_app (X : D ⥤ C) (Y : D ⥤ E)
    (f : X ⟶ ((whiskeringRight D E C).obj R).obj Y) (d : D) :
    (((adjunction D a).homEquiv X Y).symm f).app d =
      (a.homEquiv (X.obj d) (Y.obj d)).symm (f.app d) := by
  rw [CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.Adjunction.homEquiv_counit]
  change L.map (f.app d) ≫ ((adjunction D a).counit.app Y).app d = _
  rw [counit_app_app]

/-- The whole unit naturality square retains every original diagram map. -/
theorem unit_naturality {X Y : D ⥤ C} (f : X ⟶ Y) :
    f ≫ (adjunction D a).unit.app Y =
      (adjunction D a).unit.app X ≫
        ((whiskeringRight D E C).obj R).map (((whiskeringRight D C E).obj L).map f) :=
  (adjunction D a).unit.naturality f

/-- The whole counit naturality square retains the original target transformation. -/
theorem counit_naturality {X Y : D ⥤ E} (f : X ⟶ Y) :
    ((whiskeringRight D C E).obj L).map (((whiskeringRight D E C).obj R).map f) ≫
        (adjunction D a).counit.app Y =
      (adjunction D a).counit.app X ≫ f := (adjunction D a).counit.naturality f

/-- The original left triangle holds as a whole natural-transformation equation. -/
theorem left_triangle (X : D ⥤ C) :
    ((whiskeringRight D C E).obj L).map ((adjunction D a).unit.app X) ≫
        (adjunction D a).counit.app (((whiskeringRight D C E).obj L).obj X) = 𝟙 _ :=
  (adjunction D a).left_triangle_components X

/-- The same native unit and counit satisfy the entire right triangle. -/
theorem right_triangle (Y : D ⥤ E) :
    (adjunction D a).unit.app (((whiskeringRight D E C).obj R).obj Y) ≫
        ((whiskeringRight D E C).obj R).map ((adjunction D a).counit.app Y) = 𝟙 _ :=
  (adjunction D a).right_triangle_components Y

end NativeAdjunction

section ComponentObjects

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] [ModelCategory (D ⥤ C)]

private theorem cofibrant_obj_of_cofibrations_le
    (hC : cofibrations (D ⥤ C) ≤ (cofibrations C).functorCategory D)
    (X : D ⥤ C) [IsCofibrant X] (d : D) : IsCofibrant (X.obj d) := by
  let ev := (evaluation D C).obj d
  let hEv : PreservesColimitsOfShape (Discrete PEmpty.{1}) ev :=
    evaluation_preservesColimitsOfShape (J := Discrete PEmpty.{1}) d
  let : PreservesColimit (Functor.empty.{0} (D ⥤ C)) ev :=
    PreservesColimitsOfShape.preservesColimit (self := hEv)
  have hp : Cofibration (ev.map (initial.to X)) :=
    (cofibration_iff _).mpr (hC (initial.to X) ((cofibration_iff _).mp inferInstance) d)
  have hi : IsInitial (ev.obj (⊥_ (D ⥤ C))) :=
    initialIsInitial.isInitialObj ev _
  exact (isCofibrant_iff_of_isInitial (ev.map (initial.to X)) hi).mpr hp

private theorem fibrant_obj_of_fibrations_le
    (hF : fibrations (D ⥤ C) ≤ (fibrations C).functorCategory D)
    (X : D ⥤ C) [IsFibrant X] (d : D) : IsFibrant (X.obj d) := by
  let ev := (evaluation D C).obj d
  let hEv : PreservesLimitsOfShape (Discrete PEmpty.{1}) ev :=
    evaluation_preservesLimitsOfShape (J := Discrete PEmpty.{1}) d
  let : PreservesLimit (Functor.empty.{0} (D ⥤ C)) ev :=
    PreservesLimitsOfShape.preservesLimit (self := hEv)
  have hp : Fibration (ev.map (terminal.from X)) :=
    (fibration_iff _).mpr (hF (terminal.from X) ((fibration_iff _).mp inferInstance) d)
  have ht : IsTerminal (ev.obj (⊤_ (D ⥤ C))) :=
    terminalIsTerminal.isTerminalObj ev _
  exact (isFibrant_iff_of_isTerminal (ev.map (terminal.from X)) ht).mpr hp

end ComponentObjects

section SourceModels

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C]

/-- Every cofibration of the actually constructed projective model is
objectwise a coefficient cofibration, through its actual index equivalence. -/
theorem projective_cofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    cofibrations (D ⥤ C) ≤ (cofibrations C).functorCategory D := by
  let : Fact (FunctorProjective.SourceConstruction.cardinal C).IsRegular :=
    FunctorProjective.SourceConstruction.cardinal_regular C
  let : OrderBot (FunctorProjective.SourceConstruction.cardinal C).ord.ToType :=
    FunctorProjective.SourceConstruction.orderBot C
  let s := FunctorProjective.SourceConstruction.essentialIndex (D := D) (C := C)
  let d := FunctorProjective.SourceConstruction.baseData C
  let : LocallySmall.{w} s.index := locallySmall_self s.index
  let : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
  intro X Y f hf
  have h := FunctorProjective.cofibrations_le_objectwise (D := s.index) d
    ((s.equivalence.congrLeft (E := C)).functor.map f) hf
  exact (functorCategory_inverseImage_congrLeft s.equivalence (cofibrations C)) ▸ h

/-- Actual projective cofibrant diagrams have cofibrant coefficient objects. -/
theorem projective_cofibrant_obj (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    IsCofibrant X → ∀ d : D, IsCofibrant (X.obj d) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  intro hX d
  let : IsCofibrant X := hX
  exact cofibrant_obj_of_cofibrations_le projective_cofibrations_le_objectwise X d

/-- Actual projective fibrant diagrams are fibrant at every original object. -/
theorem projective_fibrant_obj (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    IsFibrant X → ∀ d : D, IsFibrant (X.obj d) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  intro hX d
  let : IsFibrant X := hX
  exact fibrant_obj_of_fibrations_le
    (FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).2.1.le X d

/-- The constructed injective fibration class is genuinely objectwise fibrant;
the original free-J lifting tests, rather than a supplied outcome, prove it. -/
theorem injective_fibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
    fibrations (D ⥤ C) ≤ (fibrations C).functorCategory D := by
  let c := FunctorInjective.SourceConstruction.coefficientData C
  let : Fact c.cardinal.IsRegular := c.regular
  let : OrderBot c.cardinal.ord.ToType := c.bottom
  let : IsCardinalLocallyPresentable C c.cardinal := c.locallyPresentable
  exact FunctorInjective.originalInjectiveModel_fibrations_le_objectwise
    c.generation c.cardinal (FunctorInjective.SourceConstruction.essentialIndex (D := D) (C := C))

/-- The actual injective cofibrancy class retains cofibrancy at all original objects. -/
theorem injective_cofibrant_obj (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
    IsCofibrant X → ∀ d : D, IsCofibrant (X.obj d) := by
  let : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
  intro hX d
  let : IsCofibrant X := hX
  exact cofibrant_obj_of_cofibrations_le
    (FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := C)).2.1.le X d

/-- Actual injectively fibrant diagrams have genuine fibrant coefficient objects. -/
theorem injective_fibrant_obj (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
    IsFibrant X → ∀ d : D, IsFibrant (X.obj d) := by
  let : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
  intro hX d
  let : IsFibrant X := hX
  exact fibrant_obj_of_fibrations_le injective_fibrations_le_objectwise X d

end SourceModels

section CoefficientTransport

variable {D : Type uD} [Category.{vD} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {L : C ⥤ E} {R : E ⥤ C} (a : L ⊣ R)

private theorem quillenEquivalence_of_components
    [ModelCategory (D ⥤ C)] [ModelCategory (D ⥤ E)] [a.IsQuillenEquivalence]
    (hQ : (adjunction D a).IsQuillenAdjunction)
    (hWC : weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D)
    (hWE : weakEquivalences (D ⥤ E) = (weakEquivalences E).functorCategory D)
    (hC : ∀ (X : D ⥤ C), IsCofibrant X → ∀ d : D, IsCofibrant (X.obj d))
    (hE : ∀ (Y : D ⥤ E), IsFibrant Y → ∀ d : D, IsFibrant (Y.obj d)) :
    (adjunction D a).IsQuillenEquivalence := by
  let : (adjunction D a).IsQuillenAdjunction := hQ
  refine CategoryTheory.Adjunction.IsQuillenEquivalence.mk ?_
  intro X Y hX hY f
  rw [hWE, hWC]
  constructor
  · intro hf d
    let : IsCofibrant (X.obj d) := hC X hX d
    let : IsFibrant (Y.obj d) := hE Y hY d
    rw [homEquiv_app]
    exact (CategoryTheory.Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
      (adj := a) (f.app d)).mp (hf d)
  · intro hf d
    let : IsCofibrant (X.obj d) := hC X hX d
    let : IsFibrant (Y.obj d) := hE Y hY d
    apply (CategoryTheory.Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
      (adj := a) (f.app d)).mpr
    simpa only [homEquiv_app] using hf d

variable [IsCombinatorialModelCategory.{w} C] [IsCombinatorialModelCategory.{w'} E]
  [EssentiallySmall.{w} D] [EssentiallySmall.{w'} D]

/-- Coefficient right-class preservation makes the native postcomposition
adjunction Quillen for the two projective models constructed from source data. -/
theorem projective_isQuillen [a.IsQuillenAdjunction] :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    letI : ModelCategory (D ⥤ E) := FunctorProjective.SourceConstruction.modelCategory
    (adjunction D a).IsQuillenAdjunction := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  let : ModelCategory (D ⥤ E) := FunctorProjective.SourceConstruction.modelCategory
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := E)).2.1] at hf
    rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).2.1]
    intro d
    exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
      (adj := a) (f.app d) (hf d)
  · intro X Y f hf
    rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := E)).2.2.1] at hf
    rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).2.2.1]
    intro d
    exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
      (adj := a) (f.app d) (hf d)

/-- Coefficient left-class preservation makes that same actual adjunction
Quillen for both source-constructed injective models. -/
theorem injective_isQuillen [h : a.IsQuillenAdjunction] :
    letI : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
    letI : ModelCategory (D ⥤ E) := FunctorInjective.SourceConstruction.modelCategory
    (adjunction D a).IsQuillenAdjunction := by
  let : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
  let : ModelCategory (D ⥤ E) := FunctorInjective.SourceConstruction.modelCategory
  constructor
  · intro X Y f hf
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := C)).2.1] at hf
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := E)).2.1]
    intro d
    exact h.preservesCofibrations (f.app d) (hf d)
  · intro X Y f hf
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := C)).2.2.1] at hf
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := E)).2.2.1]
    intro d
    exact h.preservesTrivialCofibrations (f.app d) (hf d)

/-- A coefficient Quillen equivalence gives a Quillen equivalence of the
actual projective diagram models, using all original adjunct components. -/
theorem projective_isQuillenEquivalence [a.IsQuillenEquivalence] :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    letI : ModelCategory (D ⥤ E) := FunctorProjective.SourceConstruction.modelCategory
    (adjunction D a).IsQuillenEquivalence := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  let : ModelCategory (D ⥤ E) := FunctorProjective.SourceConstruction.modelCategory
  exact quillenEquivalence_of_components a (projective_isQuillen a)
    (FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).1
    (FunctorProjective.SourceConstruction.five_classes (D := D) (C := E)).1
    projective_cofibrant_obj projective_fibrant_obj

/-- The complete coefficient Hovey criterion also gives a Quillen equivalence
of both actual injective diagram models, with no incoming diagram outcome. -/
theorem injective_isQuillenEquivalence [a.IsQuillenEquivalence] :
    letI : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
    letI : ModelCategory (D ⥤ E) := FunctorInjective.SourceConstruction.modelCategory
    (adjunction D a).IsQuillenEquivalence := by
  let : ModelCategory (D ⥤ C) := FunctorInjective.SourceConstruction.modelCategory
  let : ModelCategory (D ⥤ E) := FunctorInjective.SourceConstruction.modelCategory
  exact quillenEquivalence_of_components a (injective_isQuillen a)
    (FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := C)).1
    (FunctorInjective.SourceConstruction.fiveClasses (D := D) (C := E)).1
    injective_cofibrant_obj injective_fibrant_obj

end CoefficientTransport

end HomotopicalAlgebra.FunctorCoefficientQuillen
