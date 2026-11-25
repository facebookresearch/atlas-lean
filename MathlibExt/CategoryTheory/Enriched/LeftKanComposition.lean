/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of the original enriched Kan adjunctions

The original weighted-coend prolongations and complete restrictions determine
the same composite adjunction. The comparison retains both Hom functions,
every source and target transformation, and the actual unit and counit maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA uB uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LeftKanComposition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C)

variable
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V B) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight k c) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V B) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight k c) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V B) (c : C),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight k c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight k c) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)]

/-- The full prolongation/restriction functor data is typed independently before native
specialization. -/
structure FunctorData where
  /-- The original left Kan functor from A to B. -/
  prolongationAB : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V B
  /-- The original left Kan functor from B to C. -/
  prolongationBC : EnrichedFunctorCat V B ⥤ EnrichedFunctorCat V C
  /-- The original left Kan functor along the composite index map. -/
  prolongationAC : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V C
  /-- The original full restriction functor from B to A. -/
  restrictionBA : EnrichedFunctorCat V B ⥤ EnrichedFunctorCat V A
  /-- The original full restriction functor from C to B. -/
  restrictionCB : EnrichedFunctorCat V C ⥤ EnrichedFunctorCat V B
  /-- The original full restriction functor along the composite index map. -/
  restrictionCA : EnrichedFunctorCat V C ⥤ EnrichedFunctorCat V A

/-- The original actual coend and restriction values populate the independently typed full data. -/
def functorData : FunctorData (V := V) (A := A) (B := B) (C := C) where
  prolongationAB := leftKan j
  prolongationBC := leftKan k
  prolongationAC := leftKan (j.comp V k)
  restrictionBA := restriction j
  restrictionCB := restriction k
  restrictionCA := restriction (j.comp V k)

/-- The entire comparison type is formed before any native dictionaries or map getters are selected.
-/
def StoredComparisonType : Type _ :=
  (functorData j k).prolongationAC ≅
    (functorData j k).prolongationAB ⋙ (functorData j k).prolongationBC

/-- The original entire restriction composite, including every enriched action. -/
def restrictionIso : restriction k ⋙ restriction j ≅ restriction (j.comp V k) :=
  eqToIso (RestrictionInversePair.restriction_comp j k)

/-- The actual composed adjunction is compared at the original composite restriction. -/
def composedAdjunction : leftKan j ⋙ leftKan k ⊣ restriction (j.comp V k) :=
  ((leftKanRestrictionAdjunction j).comp (leftKanRestrictionAdjunction k)).ofNatIsoRight
    (restrictionIso j k)

/-- The original single coend prolongation and the iterated original coends are naturally
isomorphic. -/
def comparison : leftKan (j.comp V k) ≅ leftKan j ⋙ leftKan k :=
  Adjunction.leftAdjointUniq (leftKanRestrictionAdjunction (j.comp V k)) (composedAdjunction j k)

/-- Forward naturality retains arbitrary whole original source transformations. -/
theorem comparison_hom_naturality {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    (leftKan (j.comp V k)).map f ≫ (comparison j k).hom.app Y =
      (comparison j k).hom.app X ≫ (leftKan j ⋙ leftKan k).map f :=
  (comparison j k).hom.naturality f

/-- Inverse naturality uses the same original transformations and both comparison maps. -/
theorem comparison_inv_naturality {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    (leftKan j ⋙ leftKan k).map f ≫ (comparison j k).inv.app Y =
      (comparison j k).inv.app X ≫ (leftKan (j.comp V k)).map f :=
  (comparison j k).inv.naturality f

omit [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)] in
/-- The full forward composed Hom map uses both original Kan transposes and the restriction
comparison. -/
theorem composedAdjunction_homEquiv (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : (leftKan j ⋙ leftKan k).obj X ⟶ Y) :
    (composedAdjunction j k).homEquiv X Y f =
      (leftKanHomEquiv j X ((restriction k).obj Y))
        (leftKanHomEquiv k ((leftKan j).obj X) Y f) ≫ (restrictionIso j k).hom.app Y := by
  rw [composedAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    leftKanRestrictionAdjunction_homEquiv, leftKanRestrictionAdjunction_homEquiv]
  rfl

omit [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)] in
/-- The inverse composed Hom map retains both original inverse Kan transposes. -/
theorem composedAdjunction_homEquiv_symm (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : X ⟶ (restriction (j.comp V k)).obj Y) :
    ((composedAdjunction j k).homEquiv X Y).symm f =
      (leftKanHomEquiv k ((leftKan j).obj X) Y).symm
        ((leftKanHomEquiv j X ((restriction k).obj Y)).symm
          (f ≫ (restrictionIso j k).inv.app Y)) := by
  rw [composedAdjunction, Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.comp_homEquiv,
    leftKanRestrictionAdjunction_homEquiv, leftKanRestrictionAdjunction_homEquiv]
  rfl

/-- The complete original unit commutes with the prolongation comparison. -/
theorem comparison_unit (X : EnrichedFunctorCat V A) :
    (leftKanRestrictionAdjunction (j.comp V k)).unit.app X ≫
      (restriction (j.comp V k)).map ((comparison j k).hom.app X) =
        (composedAdjunction j k).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (leftKanRestrictionAdjunction (j.comp V k)) (composedAdjunction j k) X

/-- The complete original counit commutes with the same prolongation comparison. -/
theorem comparison_counit (Y : EnrichedFunctorCat V C) :
    (comparison j k).hom.app ((restriction (j.comp V k)).obj Y) ≫
      (composedAdjunction j k).counit.app Y =
        (leftKanRestrictionAdjunction (j.comp V k)).counit.app Y :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (leftKanRestrictionAdjunction (j.comp V k)) (composedAdjunction j k) Y

omit [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)] in
/-- Both original composed triangle laws hold on the full unmodified diagrams. -/
theorem composedAdjunction_triangles (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C) :
    (leftKan j ⋙ leftKan k).map ((composedAdjunction j k).unit.app X) ≫
      (composedAdjunction j k).counit.app ((leftKan j ⋙ leftKan k).obj X) = 𝟙 _ ∧
    (composedAdjunction j k).unit.app ((restriction (j.comp V k)).obj Y) ≫
      (restriction (j.comp V k)).map ((composedAdjunction j k).counit.app Y) = 𝟙 _ :=
  ⟨(composedAdjunction j k).left_triangle_components X,
    (composedAdjunction j k).right_triangle_components Y⟩

/-- The comparison preserves the full original forward Hom correspondence. -/
theorem comparison_homEquiv (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : (leftKan j ⋙ leftKan k).obj X ⟶ Y) :
    leftKanHomEquiv (j.comp V k) X Y ((comparison j k).hom.app X ≫ f) =
      (composedAdjunction j k).homEquiv X Y f := by
  let a := leftKanRestrictionAdjunction (j.comp V k)
  let b := composedAdjunction j k
  have h := a.homEquiv_naturality_right ((comparison j k).hom.app X) f
  have hu : a.homEquiv X _ ((comparison j k).hom.app X) = b.unit.app X :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app a b X
  rw [hu, ← b.homEquiv_unit] at h
  rw [leftKanRestrictionAdjunction_homEquiv] at h
  exact h

/-- Both inverse Hom functions retain the same complete original comparison. -/
theorem comparison_homEquiv_symm (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : X ⟶ (restriction (j.comp V k)).obj Y) :
    (leftKanHomEquiv (j.comp V k) X Y).symm f =
      (comparison j k).hom.app X ≫ ((composedAdjunction j k).homEquiv X Y).symm f := by
  apply (leftKanHomEquiv (j.comp V k) X Y).injective
  rw [Equiv.apply_symm_apply, comparison_homEquiv, Equiv.apply_symm_apply]

omit [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)] in
/-- The composed unit is the original pair of units followed by the actual restriction comparison.
-/
theorem composedAdjunction_unit (X : EnrichedFunctorCat V A) :
    (composedAdjunction j k).unit.app X =
      leftKanUnit j X ≫ (restriction j).map (leftKanUnit k ((leftKan j).obj X)) ≫
        (restrictionIso j k).hom.app ((leftKan j ⋙ leftKan k).obj X) := by
  have hu := (composedAdjunction j k).homEquiv_id X
  have hk : leftKanHomEquiv k ((leftKan j).obj X) ((leftKan j ⋙ leftKan k).obj X)
      (𝟙 ((leftKan j ⋙ leftKan k).obj X)) = leftKanUnit k ((leftKan j).obj X) := by
    rw [leftKanHomEquiv_apply, leftKanHomToRestriction]
    exact (congrArg (fun t => leftKanUnit k ((leftKan j).obj X) ≫ t)
      ((restriction k).map_id ((leftKan j ⋙ leftKan k).obj X))).trans (Category.comp_id _)
  rw [composedAdjunction_homEquiv, hk,
    leftKanHomEquiv_apply, leftKanHomToRestriction] at hu
  exact hu.symm.trans (Category.assoc _ _ _)

omit [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight (j.comp V k) c)
      F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (c : C),
    HasCoequalizer
      (Enriched.weightedCoend.leftMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight (j.comp V k) c) F.toEnrichedFunctor)] in
/-- The composed counit retains both original counits and the inverse restriction comparison. -/
theorem composedAdjunction_counit (Y : EnrichedFunctorCat V C) :
    (composedAdjunction j k).counit.app Y =
      (leftKan j ⋙ leftKan k).map ((restrictionIso j k).inv.app Y) ≫
        (leftKan k).map ((leftKanRestrictionAdjunction j).counit.app ((restriction k).obj Y)) ≫
          (leftKanRestrictionAdjunction k).counit.app Y := by
  have hc := (composedAdjunction j k).homEquiv_counit
    ((restriction (j.comp V k)).obj Y) Y (𝟙 ((restriction (j.comp V k)).obj Y))
  have he : (composedAdjunction j k).counit.app Y =
      ((composedAdjunction j k).homEquiv ((restriction (j.comp V k)).obj Y) Y).symm
        (𝟙 ((restriction (j.comp V k)).obj Y)) := by
    simpa only [Functor.map_id, Category.id_comp] using hc.symm
  have hj :
      (leftKanHomEquiv j ((restriction (j.comp V k)).obj Y) ((restriction k).obj Y)).symm
        ((restrictionIso j k).inv.app Y) =
      (leftKan j).map ((restrictionIso j k).inv.app Y) ≫
        (leftKanRestrictionAdjunction j).counit.app ((restriction k).obj Y) := by
    rw [← leftKanRestrictionAdjunction_homEquiv]
    exact (leftKanRestrictionAdjunction j).homEquiv_counit _ _ _
  have hk :
      (leftKanHomEquiv k ((leftKan j).obj ((restriction (j.comp V k)).obj Y)) Y).symm
        ((leftKanHomEquiv j ((restriction (j.comp V k)).obj Y) ((restriction k).obj Y)).symm
          ((restrictionIso j k).inv.app Y)) =
      (leftKan k).map
        ((leftKanHomEquiv j ((restriction (j.comp V k)).obj Y) ((restriction k).obj Y)).symm
          ((restrictionIso j k).inv.app Y)) ≫ (leftKanRestrictionAdjunction k).counit.app Y := by
    rw [← leftKanRestrictionAdjunction_homEquiv]
    exact (leftKanRestrictionAdjunction k).homEquiv_counit _ _ _
  rw [he, composedAdjunction_homEquiv_symm, Category.id_comp, hk, hj,
    Functor.map_comp, Category.assoc]
  rfl

/-- The original complete comparison value is stored at its full independently stated family type.
-/
def storedComparison : StoredComparisonType j k := comparison j k

/-- The stored comparison retains exactly the original weighted-coend/adjunction comparison. -/
theorem storedComparison_original : storedComparison j k = comparison j k := rfl

/-- A complete original Kan comparison package fixes the functor and adjunction data before map laws
are projected. -/
structure ComparisonData where
  /-- All six original prolongation and restriction functors. -/
  functors : FunctorData (V := V) (A := A) (B := B) (C := C)
  /-- The actual first weighted-coend restriction adjunction. -/
  adjunctionAB : functors.prolongationAB ⊣ functors.restrictionBA
  /-- The actual second weighted-coend restriction adjunction. -/
  adjunctionBC : functors.prolongationBC ⊣ functors.restrictionCB
  /-- The entire original restriction-composite comparison. -/
  restrictionComparison : functors.restrictionCB ⋙ functors.restrictionBA ≅ functors.restrictionCA
  /-- The full adjunction along the original composite index map. -/
  originalAdjunction : functors.prolongationAC ⊣ functors.restrictionCA
  /-- The full composite of the two original adjunctions. -/
  compositeAdjunction : functors.prolongationAB ⋙ functors.prolongationBC ⊣ functors.restrictionCA
  /-- The original prolongation-composite comparison isomorphism. -/
  comparison : functors.prolongationAC ≅ functors.prolongationAB ⋙ functors.prolongationBC
  homEquiv : ∀ (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : (functors.prolongationAB ⋙ functors.prolongationBC).obj X ⟶ Y),
    originalAdjunction.homEquiv X Y (comparison.hom.app X ≫ f) =
      compositeAdjunction.homEquiv X Y f
  homEquivSymm : ∀ (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V C)
    (f : X ⟶ functors.restrictionCA.obj Y),
    (originalAdjunction.homEquiv X Y).symm f =
      comparison.hom.app X ≫ (compositeAdjunction.homEquiv X Y).symm f
  unit : ∀ X : EnrichedFunctorCat V A,
    originalAdjunction.unit.app X ≫ functors.restrictionCA.map (comparison.hom.app X) =
      compositeAdjunction.unit.app X
  counit : ∀ Y : EnrichedFunctorCat V C,
    comparison.hom.app (functors.restrictionCA.obj Y) ≫ compositeAdjunction.counit.app Y =
      originalAdjunction.counit.app Y

  compositeUnit : ∀ X : EnrichedFunctorCat V A,
    compositeAdjunction.unit.app X =
      adjunctionAB.unit.app X ≫ functors.restrictionBA.map
        (adjunctionBC.unit.app (functors.prolongationAB.obj X)) ≫
          restrictionComparison.hom.app ((functors.prolongationAB ⋙ functors.prolongationBC).obj X)
  compositeCounit : ∀ Y : EnrichedFunctorCat V C,
    compositeAdjunction.counit.app Y =
      (functors.prolongationAB ⋙ functors.prolongationBC).map (restrictionComparison.inv.app Y) ≫
        functors.prolongationBC.map (adjunctionAB.counit.app (functors.restrictionCB.obj Y)) ≫
          adjunctionBC.counit.app Y

/-- The entire original coend, restriction, adjunction, map and comparison data is initialized in
one source context. -/
def comparisonData : ComparisonData (V := V) (A := A) (B := B) (C := C) where
  functors := functorData j k
  adjunctionAB := leftKanRestrictionAdjunction j
  adjunctionBC := leftKanRestrictionAdjunction k
  restrictionComparison := restrictionIso j k
  originalAdjunction := leftKanRestrictionAdjunction (j.comp V k)
  compositeAdjunction := composedAdjunction j k
  comparison := storedComparison j k
  homEquiv := by
    intro X Y f
    change (leftKanRestrictionAdjunction (j.comp V k)).homEquiv X Y
      ((comparison j k).hom.app X ≫ f) = (composedAdjunction j k).homEquiv X Y f
    rw [leftKanRestrictionAdjunction_homEquiv]
    exact comparison_homEquiv j k X Y f
  homEquivSymm := by
    intro X Y f
    change ((leftKanRestrictionAdjunction (j.comp V k)).homEquiv X Y).symm f =
      (comparison j k).hom.app X ≫ ((composedAdjunction j k).homEquiv X Y).symm f
    rw [leftKanRestrictionAdjunction_homEquiv]
    exact comparison_homEquiv_symm j k X Y f
  unit := comparison_unit j k
  counit := comparison_counit j k

  compositeUnit := by
    intro X
    change (composedAdjunction j k).unit.app X =
      (leftKanRestrictionAdjunction j).unit.app X ≫
        (restriction j).map ((leftKanRestrictionAdjunction k).unit.app ((leftKan j).obj X)) ≫
          (restrictionIso j k).hom.app ((leftKan j ⋙ leftKan k).obj X)
    rw [leftKanRestrictionAdjunction_unit, leftKanRestrictionAdjunction_unit]
    exact composedAdjunction_unit j k X
  compositeCounit := composedAdjunction_counit j k

/-- The complete data getter retains all original prolongation and restriction functors. -/
theorem comparisonData_functors : (comparisonData j k).functors = functorData j k := rfl

end CategoryTheory.EnrichedFunctorCat.LeftKanComposition
