/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction

set_option autoImplicit false
noncomputable section

universe w uD vD uE vE uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.FunctorProjective

namespace ProjectiveSourceConstructionPublicClients

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C]

/-- The caller supplies the conventional source hypotheses only. -/
@[instance_reducible]
def originalModel : ModelCategory (D ⥤ C) := SourceConstruction.modelCategory

/-- The returned generation is genuinely eligible at the same produced rank
as diagram local presentability, with both full original right classes. -/
theorem generatedOutputAtSourceRank :
    letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
    ∃ (rho : Cardinal.{w}) (_ : Fact rho.IsRegular) (_ : OrderBot rho.ord.ToType),
      IsCardinalLocallyPresentable (D ⥤ C) rho ∧
        ∃ g : CofibrantGenerationData (D ⥤ C) rho,
          g.I.IsCardinalForSmallObjectArgument rho ∧
          g.J.IsCardinalForSmallObjectArgument rho ∧
          g.I.rlp = (trivialFibrations C).functorCategory D ∧
          g.J.rlp = (fibrations C).functorCategory D := by
  let : Fact (SourceConstruction.cardinal C).IsRegular :=
    SourceConstruction.cardinal_regular C
  let : OrderBot (SourceConstruction.cardinal C).ord.ToType := SourceConstruction.orderBot C
  let : IsCardinalLocallyPresentable C (SourceConstruction.cardinal C) :=
    SourceConstruction.coefficientPresentable C
  let s := SourceConstruction.essentialIndex (D := D) (C := C)
  let : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
  let g := SourceConstruction.generationData (D := D) (C := C)
  have hPresentable : IsCardinalLocallyPresentable (D ⥤ C) (SourceConstruction.cardinal C) := by
    let : SmallCategory s.index := s.indexCategory
    let : IsCardinalLocallyPresentable (s.indexᵒᵖᵒᵖ ⥤ C) (SourceConstruction.cardinal C) :=
      inferInstance
    let : IsCardinalLocallyPresentable (s.index ⥤ C) (SourceConstruction.cardinal C) :=
      ((opOpEquivalence s.index).congrLeft (E := C)).isCardinalLocallyPresentable _
    exact (s.equivalence.congrLeft (E := C)).symm.isCardinalLocallyPresentable _
  refine ⟨SourceConstruction.cardinal C, inferInstance, inferInstance, hPresentable, g,
    g.I_smallObject, g.J_smallObject, ?_, ?_⟩
  · exact (SourceConstruction.FromData.generationData_right_classes
      (SourceConstruction.baseData C) s).1
  · exact (SourceConstruction.FromData.generationData_right_classes
      (SourceConstruction.baseData C) s).2

/-- Arbitrary original index objects and coefficient I-arrows occur in the
isomorphism closure of the actual returned small representative family. -/
theorem originalFreeI_member (x : D) {A B : C} (f : A ⟶ B)
    (hf : letI : Fact (SourceConstruction.cardinal C).IsRegular :=
            SourceConstruction.cardinal_regular C
          letI : OrderBot (SourceConstruction.cardinal C).ord.ToType :=
            SourceConstruction.orderBot C
          (SourceConstruction.baseData C).I f) :
    letI : Fact (SourceConstruction.cardinal C).IsRegular :=
      SourceConstruction.cardinal_regular C
    letI : OrderBot (SourceConstruction.cardinal C).ord.ToType := SourceConstruction.orderBot C
    letI : LocallySmall.{w} D :=
      (SourceConstruction.essentialIndex (D := D) (C := C)).locallySmallIndex
    letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
    (SourceConstruction.generationData (D := D) (C := C)).I.isoClosure
      ((freeFunctor (SourceConstruction.baseData C) x).map f) := by
  let : Fact (SourceConstruction.cardinal C).IsRegular :=
    SourceConstruction.cardinal_regular C
  let : OrderBot (SourceConstruction.cardinal C).ord.ToType := SourceConstruction.orderBot C
  let s := SourceConstruction.essentialIndex (D := D) (C := C)
  let : LocallySmall.{w} D := s.locallySmallIndex
  let : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
  change (SourceConstruction.FromData.generationData (SourceConstruction.baseData C) s).I.isoClosure
    ((freeFunctor (SourceConstruction.baseData C) x).map f)
  rw [(SourceConstruction.FromData.generationData_original_free_families
    (SourceConstruction.baseData C) s).1]
  exact (le_isoClosure (freeGenerators (D := D) (SourceConstruction.baseData C)
    (SourceConstruction.baseData C).I)) _
      (freeGenerator_mem (SourceConstruction.baseData C) (SourceConstruction.baseData C).I x f hf)

/-- An arbitrary original Arrow square induces the actual first projection
Arrow map, retaining its original target transformation. -/
def originalProjectionArrowMap {f g : Arrow (D ⥤ C)} (a : f ⟶ g) :
    Arrow.mk ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).p.app f) ⟶
      Arrow.mk ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).p.app g) :=
  Arrow.homMk
    ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).Z.map a)
    a.right ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).p.naturality a)

/-- Every original target component of that whole Arrow map is retained. -/
theorem originalProjectionArrowMap_target {f g : Arrow (D ⥤ C)} (a : f ⟶ g) (d : D) :
    (originalProjectionArrowMap a).right.app d = a.right.app d := rfl

/-- The actual native small-index algorithm, not an arbitrary factorization,
acts on both middle maps of every original Arrow square. -/
theorem originalSmallIndexArrowMaps {f g : Arrow (D ⥤ C)} (a : f ⟶ g) :
    letI : Fact (SourceConstruction.cardinal C).IsRegular :=
      SourceConstruction.cardinal_regular C
    letI : OrderBot (SourceConstruction.cardinal C).ord.ToType := SourceConstruction.orderBot C
    let s := SourceConstruction.essentialIndex (D := D) (C := C)
    letI : LocallySmall.{w} s.index := locallySmall_self s.index
    letI : ModelCategory (s.index ⥤ C) :=
      FunctorProjective.modelCategory (J := s.index) (SourceConstruction.baseData C)
    (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).Z.map a =
        (s.equivalence.congrLeft (E := C)).inverse.map
          ((FunctorProjective.cofibrantFactorizationData (D := s.index)
            (SourceConstruction.baseData C)).Z.map
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.map a)) ∧
      (SourceConstruction.fibrantFactorizationData (D := D) (C := C)).Z.map a =
        (s.equivalence.congrLeft (E := C)).inverse.map
          ((FunctorProjective.fibrantFactorizationData (D := s.index)
            (SourceConstruction.baseData C)).Z.map
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.map a)) := ⟨rfl, rfl⟩

/-- The original first inclusion lifts against an arbitrary whole pointwise
trivial fibration, with the full original natural-transformation square. -/
def firstFactorLift (f : Arrow (D ⥤ C)) {X Y : D ⥤ C} (p : X ⟶ Y)
    (hp : (trivialFibrations C).functorCategory D p) (a : f.left ⟶ X)
    (b : (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).Z.obj f ⟶ Y)
    (sq : CommSq a
      ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).i.app f) p b) :
    sq.LiftStruct := by
  letI : HasLiftingProperty
      ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).i.app f) p :=
    (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).hi f _ hp
  exact (CommSq.HasLift.exists_lift (sq := sq)).some

/-- Every original object sees both triangles of that same whole selected lift. -/
theorem firstFactorLift_components (f : Arrow (D ⥤ C)) {X Y : D ⥤ C} (p : X ⟶ Y)
    (hp : (trivialFibrations C).functorCategory D p) (a : f.left ⟶ X)
    (b : (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).Z.obj f ⟶ Y)
    (sq : CommSq a
      ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).i.app f) p b) (d : D) :
    ((SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).i.app f).app d ≫
        (firstFactorLift f p hp a b sq).l.app d = a.app d ∧
      (firstFactorLift f p hp a b sq).l.app d ≫ p.app d = b.app d :=
  ⟨NatTrans.congr_app (firstFactorLift f p hp a b sq).fac_left d,
    NatTrans.congr_app (firstFactorLift f p hp a b sq).fac_right d⟩

/-- The output combinatoriality is usable for another actual essentially
small functor category, with no fresh coefficient witness supplied by the caller. -/
@[instance_reducible]
def nestedModel :
    letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
    letI : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
      SourceConstruction.isCombinatorial (D := D) (C := C)
    ModelCategory (E ⥤ (D ⥤ C)) := by
  letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
  letI : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
    SourceConstruction.isCombinatorial (D := D) (C := C)
  exact SourceConstruction.modelCategory

/-- Iteration retains both full original index families in the fibration class. -/
theorem nestedFibration_iff {F G : E ⥤ (D ⥤ C)} (f : F ⟶ G) :
    letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
    letI : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
      SourceConstruction.isCombinatorial (D := D) (C := C)
    letI : ModelCategory (E ⥤ (D ⥤ C)) := nestedModel (D := D) (E := E) (C := C)
    fibrations (E ⥤ (D ⥤ C)) f ↔ ∀ e : E, ∀ d : D, fibrations C ((f.app e).app d) := by
  let : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
  let : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
    SourceConstruction.isCombinatorial (D := D) (C := C)
  let : ModelCategory (E ⥤ (D ⥤ C)) := nestedModel (D := D) (E := E) (C := C)
  have hOuter := (SourceConstruction.five_classes (D := E) (C := D ⥤ C)).2.1
  have hInner := (SourceConstruction.five_classes (D := D) (C := C)).2.1
  rw [hOuter]
  constructor
  · intro h e
    have he := h e
    rw [hInner] at he
    exact he
  · intro h e
    rw [hInner]
    exact h e

/-- The same actual nested carrier retains the original coefficient weak
equivalences at every object of both unchanged categories. -/
theorem nestedWeakEquivalence_iff {F G : E ⥤ (D ⥤ C)} (f : F ⟶ G) :
    letI : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
    letI : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
      SourceConstruction.isCombinatorial (D := D) (C := C)
    letI : ModelCategory (E ⥤ (D ⥤ C)) := nestedModel (D := D) (E := E) (C := C)
    weakEquivalences (E ⥤ (D ⥤ C)) f ↔
      ∀ e : E, ∀ d : D, weakEquivalences C ((f.app e).app d) := by
  let : ModelCategory (D ⥤ C) := originalModel (D := D) (C := C)
  let : IsCombinatorialModelCategory.{w} (D ⥤ C) :=
    SourceConstruction.isCombinatorial (D := D) (C := C)
  let : ModelCategory (E ⥤ (D ⥤ C)) := nestedModel (D := D) (E := E) (C := C)
  have hOuter := (SourceConstruction.five_classes (D := E) (C := D ⥤ C)).1
  have hInner := (SourceConstruction.five_classes (D := D) (C := C)).1
  rw [hOuter]
  constructor
  · intro h e
    have he := h e
    rw [hInner] at he
    exact he
  · intro h e
    rw [hInner]
    exact h e

end ProjectiveSourceConstructionPublicClients
