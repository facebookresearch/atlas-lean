/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RawLocality
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.IndexedFreeMappingData
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyInjectiveComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence

/-!
# Localizing families under designation of simplicial spaces

The raw and designated mapping ends identify the same precomposition arrow,
and the original injective and Reedy fibrations correspond under designation.
Consequently every original localizing family has the same local-fibrant
targets and all-target weak tests on the two carriers. No smallness condition
on the family index and no localized model is needed for this comparison.

For the literal Rezk spine and completeness family, these tests are precisely
the existing complete Segal spaces and `rezkWeakEquivalences`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.DesignatedLocality

private abbrev Raw := SimplicialPresheaf.{u} SimplexCategory

private abbrev designate : Raw.{u} ⥤ SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject

/-- Both endpoints and the original naturality square compare the actual precomposition maps. -/
private def precompArrowIso {A B : Raw.{u}} (f : A ⟶ B) (Z : Raw.{u}) :
    Arrow.mk (SimplicialPresheaf.innerHomPre f Z) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map (designate.map f).op).app
        (designate.obj Z)) :=
  Arrow.isoMk
    (IndexedFreeMapping.rawEndIso (designate.obj B) (designate.obj Z))
    (IndexedFreeMapping.rawEndIso (designate.obj A) (designate.obj Z))
    ((IndexedFreeMapping.rawEnd_naturality.1 (designate.map f) (designate.obj Z)).1).symm

/-- Realization weakness is unchanged by the actual comparison of precomposition arrows. -/
private theorem precomp_weak_iff {A B : Raw.{u}} (f : A ⟶ B) (Z : Raw.{u}) :
    SSet.realizationWeakEquivalences (SimplicialPresheaf.innerHomPre f Z) ↔
      SSet.realizationWeakEquivalences
        ((SimplicialSpace.innerHomFunctor.map (designate.map f).op).app
          (designate.obj Z)) :=
  SSet.realizationWeakEquivalences.arrow_mk_iso_iff (precompArrowIso f Z)

/-- The whole original injective lifting class agrees with the selected Reedy fibrations. -/
private theorem baseFibration_iff {A B : Raw.{u}} (p : A ⟶ B) :
    let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    InjectiveKan.injectiveFibrations SimplexCategory p ↔
      fibrations SimplicialSpace.{u} (designate.map p) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let Q := trivialCofibrations SimplicialSpace.{u}
  have hQ : Q.inverseImage designate = InjectiveKan.trivialMonomorphisms SimplexCategory := by
    ext A B f
    change (cofibrations SimplicialSpace.{u} (designate.map f) ∧
      weakEquivalences SimplicialSpace.{u} (designate.map f)) ↔ _
    rw [SimplicialSpace.ReedyModel.selectedReedy_injective_classes.1,
      SimplicialSpace.ReedyModel.selectedReedy_injective_classes.2.1]
    change (Mono (designate.map f) ∧
      ∀ n : SimplexCategoryᵒᵖ, SSet.realizationWeakEquivalences (f.app n)) ↔
      (Mono f ∧ ∀ n : SimplexCategoryᵒᵖ, SSet.realizationWeakEquivalences (f.app n))
    exact and_congr (SimplicialSpace.mono_forget_map_iff (designate.map f)).symm Iff.rfl
  change (InjectiveKan.trivialMonomorphisms SimplexCategory).rlp p ↔ _
  rw [← hQ, ← trivialCofibrations_rlp SimplicialSpace.{u}]
  have hRlp : (Q.inverseImage designate).rlp = Q.rlp.inverseImage designate :=
    (inverseImage_rlp_of_equivalence SimplicialSpace.equivalenceSimplicialObject.symm Q).symm
  exact Iff.of_eq (congrArg (fun P : MorphismProperty Raw.{u} => P p) hRlp)

/-- Original injective fibrancy is exactly Reedy fibrancy of the same designated diagram. -/
private theorem baseFibrant_iff (Z : Raw.{u}) :
    IsFibrant Z ↔
      (let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
       IsFibrant (designate.obj Z)) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have hBase : IsFibrant Z ↔
      InjectiveKan.injectiveFibrations SimplexCategory (terminal.from Z) := by
    rw [isFibrant_iff, fibration_iff]
    change (InjectiveKan.data.{u} SimplexCategory).model.categoryWithFibrations.fibrations
      (terminal.from Z) ↔ _
    rw [(InjectiveKan.data.{u} SimplexCategory).fibrations_eq]
  let ht : IsTerminal (designate.obj (⊤_ Raw.{u})) :=
    terminalIsTerminal.isTerminalObj designate (⊤_ Raw.{u})
  have hDesignated : IsFibrant (designate.obj Z) ↔
      fibrations SimplicialSpace.{u} (designate.map (terminal.from Z)) := by
    rw [isFibrant_iff_of_isTerminal (designate.map (terminal.from Z)) ht,
      fibration_iff]
  exact hBase.trans ((baseFibration_iff (terminal.from Z)).trans hDesignated.symm)

/-- Designation preserves local-fibrant targets for every original localizing family. -/
theorem localFibrant_iff {I : Type i} (S : I → Arrow Raw.{u}) (Z : Raw.{u}) :
    InjectiveKan.isOriginalLocalFibrant S Z ↔
      (let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
       IsFibrant (designate.obj Z)) ∧
      ∀ a : I, SSet.realizationWeakEquivalences
        ((SimplicialSpace.innerHomFunctor.map (designate.map (S a).hom).op).app
          (designate.obj Z)) :=
  and_congr (baseFibrant_iff Z) (forall_congr' fun a => precomp_weak_iff (S a).hom Z)

/-- Every original arrow has the same all-local-target weak test after designation. -/
theorem localWeak_iff {I : Type i} (S : I → Arrow Raw.{u})
    {A B : Raw.{u}} (f : A ⟶ B) :
    InjectiveKan.originalLocalEquivalences S f ↔
      ∀ W : SimplicialSpace.{u},
        ((let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
          IsFibrant W) ∧
          ∀ a : I, SSet.realizationWeakEquivalences
            ((SimplicialSpace.innerHomFunctor.map (designate.map (S a).hom).op).app W)) →
        SSet.realizationWeakEquivalences
          ((SimplicialSpace.innerHomFunctor.map (designate.map f).op).app W) := by
  constructor
  · intro hf W hW
    have hLocal : InjectiveKan.isOriginalLocalFibrant S W.diagram :=
      (localFibrant_iff S W.diagram).mpr hW
    exact (precomp_weak_iff f W.diagram).mp (hf W.diagram hLocal)
  · intro hf Z hZ
    exact (precomp_weak_iff f Z).mpr
      (hf (designate.obj Z) ((localFibrant_iff S Z).mp hZ))

end SimplicialPresheaf.DesignatedLocality

namespace SimplicialPresheaf.OriginalRezkLocalizer

/-- The exact original simplex-index local targets are the existing complete Segal spaces. -/
theorem coefficientLocalFibrant_iff_completeSegalSpaces
    (Z : SimplicialPresheaf.{u} SimplexCategory) :
    InjectiveKan.isOriginalLocalFibrant SSet.Rezk.localizingMap.{u} Z ↔
      SimplicialSpace.completeSegalSpaces (SimplicialSpace.ofSimplicialObject.obj Z) :=
  DesignatedLocality.localFibrant_iff SSet.Rezk.localizingMap.{u} Z

/-- EVERY original coefficient arrow has exactly the named all-CSS Rezk weak predicate. -/
theorem coefficientLocalWeak_iff_rezkWeak
    {A B : SimplicialPresheaf.{u} SimplexCategory} (f : A ⟶ B) :
    InjectiveKan.originalLocalEquivalences SSet.Rezk.localizingMap.{u} f ↔
      SimplicialSpace.rezkWeakEquivalences (SimplicialSpace.ofSimplicialObject.map f) :=
  DesignatedLocality.localWeak_iff SSet.Rezk.localizingMap.{u} f

end SimplicialPresheaf.OriginalRezkLocalizer
