/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison.FullMapFamilies

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]


/-- Both complete original coefficient comparison maps are stated before native source
specialization. -/
def MapsFormula : Prop :=
  ∀ (a : A) (X : V),
    (functorIso j a).hom.app X = hom j a X ∧ (functorIso j a).inv.app X = inv j a X

/-- The entire original free comparison satisfies both full map equations at every index and
coefficient. -/
theorem mapsFormula : MapsFormula j := by
  intro a X
  exact ⟨functorIso_hom_app j a X, functorIso_inv_app j a X⟩

/-- A full free-coefficient comparison package is typed before native coend maps are supplied. -/
structure Data where
  /-- The complete original weighted-coend left Kan functor. -/
  originalLan : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V B
  /-- The whole free-coefficient comparison at every original source index. -/
  comparison : ∀ a : A, Free.functor a ⋙ originalLan ≅ Free.functor (j.obj a)
  /-- Every original forward comparison map with its full coefficient. -/
  homMap : ∀ (a : A) (X : V), originalLan.obj (Free.object a X) ⟶ Free.object (j.obj a) X
  /-- Every original inverse comparison map with its full coefficient. -/
  invMap : ∀ (a : A) (X : V), Free.object (j.obj a) X ⟶ originalLan.obj (Free.object a X)
  homEquation : ∀ (a : A) (X : V), (comparison a).hom.app X = homMap a X
  invEquation : ∀ (a : A) (X : V), (comparison a).inv.app X = invMap a X

  homSource : ∀ {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V),
    originalLan.map (Free.sourceMap e X) ≫ homMap a X =
      homMap a' X ≫ Free.sourceMap (e ≫ j.map a a') X
  invSource : ∀ {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V),
    Free.sourceMap (e ≫ j.map a a') X ≫ invMap a X =
      invMap a' X ≫ originalLan.map (Free.sourceMap e X)

/-- The original complete free Kan comparison and both actual map families are initialized together.
-/
def data : Data j where
  originalLan := leftKan j
  comparison := functorIso j
  homMap := hom j
  invMap := inv j
  homEquation := functorIso_hom_app j
  invEquation := functorIso_inv_app j
  homSource := hom_source j
  invSource := inv_source j

/-- Initialize the complete original Kan/free package with the supplied full coend
certificates, before specializing any coefficient or index. -/
def dataOfCoends
    (relations : ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor))
    (objects : ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor))
    (balance : ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
        (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)) : Data j := by
  letI := relations
  letI := objects
  letI := balance
  exact data j

/-- The full typed package retains the entire original Kan functor value. -/
theorem data_originalLan : (data j).originalLan = leftKan j := rfl

/-- The full typed package retains the entire original coefficient comparison family. -/
theorem data_comparison : (data j).comparison = functorIso j := rfl

end CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison.FullMapFamilies
