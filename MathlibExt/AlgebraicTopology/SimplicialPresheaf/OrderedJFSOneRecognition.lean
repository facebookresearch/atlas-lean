/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Complete external assembly proof attempt; no CPP/readiness/acceptance is asserted.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneCoordinateData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneEndComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneGlobalFibrancy
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneIntrinsicSemantics
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.IndexedFreeMappingData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalizationClassComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Recognition of the one-coordinate localized models

The normalized and full one-coordinate localizing families recognize intrinsic completeness
and complete Segal spaces through the designated site equivalence. Their weak equivalences on
arbitrary arrows coincide with scalar Rezk weak equivalences, and both chosen localized models
have the corresponding inverse-image classes and are Quillen equivalent to the Rezk model and
to each other.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner
attribute [local instance] SimplicialPresheaf.hasEnd
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.OrderedJFS
open InjectiveKan

-- The original intrinsic definition is imported from its actual owner, never redefined.
private def rawArrowSourceIso {D : Type*} [Category D] [Small.{u} D] [LocallySmall.{u} D]
    {s t : Arrow (SimplicialPresheaf.{u} D)} (e : s ≅ t)
    (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (innerHomPre s.hom Z) ≅ Arrow.mk (innerHomPre t.hom Z) :=
  Arrow.isoMk
    ((innerHomFunctor.mapIso ((Arrow.rightFunc.mapIso e).op)).app Z).symm
    ((innerHomFunctor.mapIso ((Arrow.leftFunc.mapIso e).op)).app Z).symm
    (by
      change innerHomPre e.inv.right Z ≫ innerHomPre t.hom Z =
        innerHomPre s.hom Z ≫ innerHomPre e.inv.left Z
      rw [innerHomPre_comp, innerHomPre_comp, e.inv.w])

private def rawChosenArrow {A B : SimplicialPresheaf.{u} SimplexCategory}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} SimplexCategory) :
    Arrow.mk (innerHomPre f Z) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map
        (SimplicialSpace.ofSimplicialObject.map f).op).app
          (SimplicialSpace.ofSimplicialObject.obj Z)) :=
  Arrow.isoMk
    (IndexedFreeMapping.rawEndIso
      (SimplicialSpace.ofSimplicialObject.obj B) (SimplicialSpace.ofSimplicialObject.obj Z))
    (IndexedFreeMapping.rawEndIso
      (SimplicialSpace.ofSimplicialObject.obj A) (SimplicialSpace.ofSimplicialObject.obj Z))
    ((IndexedFreeMapping.rawEnd_naturality.1
      (SimplicialSpace.ofSimplicialObject.map f)
      (SimplicialSpace.ofSimplicialObject.obj Z)).1).symm

private theorem normalizedTest_iff (g : Generator 1) (X : Original.{u} 1) :
    SSet.realizationWeakEquivalences (innerHomPre (originalFamily.{u} 1 g).hom X) ↔
      SSet.realizationWeakEquivalences
        (SimplicialSpace.FiniteCompletenessMapping.restriction
          (oneDesignatedEquivalence.{u}.functor.obj X)
          (oneFiniteFamily.{u} (oneNormalizedIndexEquiv g)).hom) := by
  let e := oneMappingPrecompArrowIso (originalFamily.{u} 1 g).hom X ≪≫
    rawArrowSourceIso (oneNormalizedArrowIso.{u} g)
      (oneOriginalEquivalence.{u}.functor.obj X) ≪≫
    rawChosenArrow (oneFiniteFamily.{u} (oneNormalizedIndexEquiv g)).hom
      (oneOriginalEquivalence.{u}.functor.obj X)
  exact SSet.realizationWeakEquivalences.arrow_mk_iso_iff e

private theorem normalizedAllTests_iff (X : Original.{u} 1) :
    isRawLocal (originalFamily.{u} 1) X ↔
      ∀ i : SSet.Rezk.LocalizingIndex, SSet.realizationWeakEquivalences
        (SimplicialSpace.FiniteCompletenessMapping.restriction
          (oneDesignatedEquivalence.{u}.functor.obj X) (oneFiniteFamily.{u} i).hom) := by
  constructor
  · intro h i
    obtain ⟨g, rfl⟩ := oneNormalizedIndexEquiv.surjective i
    exact (normalizedTest_iff g X).mp (h g)
  · intro h g
    exact (normalizedTest_iff g X).mpr (h (oneNormalizedIndexEquiv g))

private theorem finiteScalarFields_iff (W : SimplicialSpace.{u}) :
    (let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
     IsFibrant W ∧ ∀ i : SSet.Rezk.LocalizingIndex, SSet.realizationWeakEquivalences
       (SimplicialSpace.FiniteCompletenessMapping.restriction W (oneFiniteFamily.{u} i).hom)) ↔
      SimplicialSpace.FiniteCompletenessHorel.finiteCompleteSegalSpaces W := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  constructor
  · rintro ⟨hRF, hTests⟩
    refine ⟨⟨hRF, ?_⟩, ?_⟩
    · intro n hn
      exact hTests (.inl ⟨n, hn⟩)
    · exact hTests (.inr PUnit.unit)
  · rintro ⟨hSegal, hKappa⟩
    refine ⟨hSegal.1, ?_⟩
    intro i
    rcases i with n | k
    · exact hSegal.2 n.1 n.2
    · exact hKappa

private theorem normalizedLocalF_iff_CSS (X : Original.{u} 1) :
    isOriginalLocalFibrant (originalFamily.{u} 1) X ↔
      SimplicialSpace.completeSegalSpaces (oneDesignatedEquivalence.{u}.functor.obj X) := by
  change (IsFibrant X ∧ isRawLocal (originalFamily.{u} 1) X) ↔ _
  have hRF := one_globalInjectiveFibrant_iff X
  have hTests := normalizedAllTests_iff X
  exact ((and_congr hRF hTests).trans
    (finiteScalarFields_iff (oneDesignatedEquivalence.{u}.functor.obj X))).trans
      (SimplicialSpace.FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete
        (oneDesignatedEquivalence.{u}.functor.obj X)).symm

private theorem fullNormalizedLocalF_iff (X : Original.{u} 1) :
    isOriginalLocalFibrant (fullOriginalFamily.{u} 1) X ↔
      isOriginalLocalFibrant (originalFamily.{u} 1) X := by
  constructor
  · rintro ⟨hRF, hTests⟩
    exact ⟨hRF, fun g => by
      simpa only [originalFamily_toFull] using hTests (normalizedToFull g)⟩
  · rintro ⟨hRF, hTests⟩
    refine ⟨hRF, ?_⟩
    intro g
    rcases oneFullRedundancy.{u} g with ⟨n, ⟨e⟩⟩ | hIso
    · let common := oneMappingPrecompArrowIso (fullOriginalFamily.{u} 1 g).hom X ≪≫
        rawArrowSourceIso e (oneOriginalEquivalence.{u}.functor.obj X) ≪≫
        (oneMappingPrecompArrowIso (originalFamily.{u} 1 n).hom X).symm
      exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff common).mpr (hTests n)
    · let : IsIso (fullOriginalFamily.{u} 1 g).hom := hIso
      let : IsIso (innerHomPre (fullOriginalFamily.{u} 1 g).hom X) :=
        inferInstanceAs (IsIso ((innerHomFunctor.flip.obj X).map
          (fullOriginalFamily.{u} 1 g).hom.op))
      exact SSet.realizationWeakEquivalences.of_isIso _

/-- BOTH original normalized/full local-fibrant predicates have the complete original intrinsic
meaning, with genuine GLOBAL RF and literal RF+Segal Horel kappa tests derived internally. -/
theorem one_locality_recognition (X : Original.{u} 1) :
    (isOriginalLocalFibrant (originalFamily.{u} 1) X ↔ oneIntrinsicComplete X) ∧
    (isOriginalLocalFibrant (fullOriginalFamily.{u} 1) X ↔ oneIntrinsicComplete X) ∧
    (isOriginalLocalFibrant (originalFamily.{u} 1) X ↔
      SimplicialSpace.completeSegalSpaces (oneDesignatedEquivalence.{u}.functor.obj X)) := by
  have hc := normalizedLocalF_iff_CSS X
  have hi := oneIntrinsicComplete_iff_completeSegalSpaces X
  have hn := hc.trans hi.symm
  exact ⟨hn, (fullNormalizedLocalF_iff X).trans hn, hc⟩

private def originalChosenArrow {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    Arrow.mk (innerHomPre f Z) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map
        (oneDesignatedEquivalence.{u}.functor.map f).op).app
          (oneDesignatedEquivalence.{u}.functor.obj Z)) :=
  oneMappingPrecompArrowIso f Z ≪≫
    rawChosenArrow (oneOriginalEquivalence.{u}.functor.map f)
      (oneOriginalEquivalence.{u}.functor.obj Z)

private theorem CSS_of_actualIso {W V : SimplicialSpace.{u}} (e : W ≅ V)
    (hV : SimplicialSpace.completeSegalSpaces V) : SimplicialSpace.completeSegalSpaces W := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  let : IsFibrant V := (SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces V).mpr hV
  let : Fibration e.hom := inferInstance
  exact (SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces W).mp
    (HomotopicalAlgebra.isFibrant_of_fibration e.hom)

private def chosenTargetArrowIso {A B W V : SimplicialSpace.{u}}
    (f : A ⟶ B) (e : W ≅ V) :
    Arrow.mk ((SimplicialSpace.innerHomFunctor.map f.op).app W) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map f.op).app V) :=
  Arrow.isoMk
    ((SimplicialSpace.innerHomFunctor.obj (op B)).mapIso e)
    ((SimplicialSpace.innerHomFunctor.obj (op A)).mapIso e)
    ((SimplicialSpace.innerHomFunctor.map f.op).naturality e.hom)

private theorem normalizedWeak_iff {A B : Original.{u} 1} (f : A ⟶ B) :
    originalLocalEquivalences (originalFamily.{u} 1) f ↔
      SimplicialSpace.rezkWeakEquivalences (oneDesignatedEquivalence.{u}.functor.map f) := by
  constructor
  · intro h W hW
    let X := oneDesignatedEquivalence.{u}.inverse.obj W
    let e := oneDesignatedEquivalence.{u}.counitIso.app W
    have hX : isOriginalLocalFibrant (originalFamily.{u} 1) X :=
      (normalizedLocalF_iff_CSS X).mpr (CSS_of_actualIso e hW)
    have hChosen := (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (originalChosenArrow f X)).mp (h X hX)
    exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (chosenTargetArrowIso (oneDesignatedEquivalence.{u}.functor.map f) e)).mp hChosen
  · intro h X hX
    exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (originalChosenArrow f X)).mpr
      (h (oneDesignatedEquivalence.{u}.functor.obj X) ((normalizedLocalF_iff_CSS X).mp hX))

/-- EVERY original arrow has both original all-target weak predicates equal to genuine
scalar Rezk weakness under the actual Phi1; no Mono or endpoint-fibrancy premise. -/
theorem one_localWeak_iff {A B : Original.{u} 1} (f : A ⟶ B) :
    (originalLocalEquivalences (originalFamily.{u} 1) f ↔
      SimplicialSpace.rezkWeakEquivalences (oneDesignatedEquivalence.{u}.functor.map f)) ∧
    (originalLocalEquivalences (fullOriginalFamily.{u} 1) f ↔
      SimplicialSpace.rezkWeakEquivalences (oneDesignatedEquivalence.{u}.functor.map f)) := by
  have hn := normalizedWeak_iff f
  have hClasses := originalLocalEquivalences_eq_of_localFibrant_iff
    (fullOriginalFamily.{u} 1) (originalFamily.{u} 1) fullNormalizedLocalF_iff
  exact ⟨hn, by rw [hClasses]; exact hn⟩

private theorem monoPhi_iff {A B : Original.{u} 1} (f : A ⟶ B) :
    Mono f ↔ Mono (oneDesignatedEquivalence.{u}.functor.map f) := by
  constructor
  · intro h
    let : Mono f := h
    infer_instance
  · intro h
    exact oneDesignatedEquivalence.{u}.functor.mono_of_mono_map h

private theorem normalizedTrivial_forward {A B : Original.{u} 1} (f : A ⟶ B)
    (hf : localTrivialMonomorphisms (originalFamily.{u} 1) f) :
    (monomorphisms SimplicialSpace.{u} ⊓ SimplicialSpace.rezkWeakEquivalences)
      (oneDesignatedEquivalence.{u}.functor.map f) :=
  ⟨(monoPhi_iff f).mp hf.1, (normalizedWeak_iff f).mp hf.2⟩

private theorem normalizedTrivial_inverse {A B : SimplicialSpace.{u}} (i : A ⟶ B)
    (hi : (monomorphisms SimplicialSpace.{u} ⊓ SimplicialSpace.rezkWeakEquivalences) i) :
    localTrivialMonomorphisms (originalFamily.{u} 1)
      (oneDesignatedEquivalence.{u}.inverse.map i) := by
  let E := oneDesignatedEquivalence.{u}
  let : Mono i := hi.1
  refine ⟨monomorphisms.infer_property _, ?_⟩
  apply (normalizedWeak_iff (E.inverse.map i)).mpr
  let e : Arrow.mk (E.functor.map (E.inverse.map i)) ≅ Arrow.mk i :=
    Arrow.isoMk (E.counitIso.app A) (E.counitIso.app B)
      (E.counitIso.hom.naturality i).symm
  exact (SimplicialSpace.rezkWeakEquivalences.arrow_mk_iso_iff e).mpr hi.2

private theorem normalizedGlobalRLP_iff {A B : Original.{u} 1} (p : A ⟶ B) :
    (localTrivialMonomorphisms (originalFamily.{u} 1)).rlp p ↔
      (monomorphisms SimplicialSpace.{u} ⊓ SimplicialSpace.rezkWeakEquivalences).rlp
        (oneDesignatedEquivalence.{u}.functor.map p) := by
  let E := oneDesignatedEquivalence.{u}
  constructor
  · intro hp U V i hi
    have hl : HasLiftingProperty (E.inverse.map i) p := hp _ (normalizedTrivial_inverse i hi)
    exact (E.symm.toAdjunction.hasLiftingProperty_iff i p).mp hl
  · intro hp U V i hi
    exact (E.functor.hasLiftingProperty_iff_of_isEquivalence i p).mp
      (hp _ (normalizedTrivial_forward i hi))

private theorem normalizedChosenClasses :
    let N := originalLocalSmithModel (originalFamily.{u} 1)
    let R := SimplicialSpace.RezkModel.modelCategory.{u}
    let E := oneDesignatedEquivalence.{u}
    N.categoryWithCofibrations.cofibrations =
        R.categoryWithCofibrations.cofibrations.inverseImage E.functor ∧
    N.categoryWithWeakEquivalences.weakEquivalences =
        R.categoryWithWeakEquivalences.weakEquivalences.inverseImage E.functor ∧
    N.categoryWithFibrations.fibrations =
        R.categoryWithFibrations.fibrations.inverseImage E.functor := by
  let q := originalLocalSmithData (originalFamily.{u} 1)
  let E := oneDesignatedEquivalence.{u}
  let R := SimplicialSpace.RezkModel.modelCategory.{u}
  refine ⟨?_, ?_, ?_⟩
  · rw [q.cofibrations_eq, SimplicialSpace.RezkModel.modelCategory_cofibrations]
    ext A B f
    exact monoPhi_iff f
  · rw [q.weakEquivalences_eq, SimplicialSpace.RezkModel.modelCategory_weakEquivalences]
    ext A B f
    exact normalizedWeak_iff f
  · rw [q.fibrations_eq, SimplicialSpace.RezkModel.modelCategory_fibrations]
    ext A B p
    exact normalizedGlobalRLP_iff p

private theorem normalizedPhiQE :
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
      (originalLocalSmithModel (originalFamily.{u} 1))
      SimplicialSpace.RezkModel.modelCategory.{u}
      oneDesignatedEquivalence.{u}.functor oneDesignatedEquivalence.{u}.inverse
      oneDesignatedEquivalence.{u}.toAdjunction := by
  let q := originalLocalSmithData (originalFamily.{u} 1)
  let N := q.model
  let R := SimplicialSpace.RezkModel.modelCategory.{u}
  let E := oneDesignatedEquivalence.{u}
  have hC := normalizedChosenClasses.{u}.1
  have hW := normalizedChosenClasses.{u}.2.1
  refine @CategoryTheory.Adjunction.IsQuillenEquivalence.mk
    (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
    N R E.functor E.inverse E.toAdjunction ?_ ?_
  · refine @CategoryTheory.Adjunction.IsQuillenAdjunction.mk
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
      N R E.functor E.inverse E.toAdjunction ?_ ?_
    · intro A B f hf
      change N.categoryWithCofibrations.cofibrations f at hf
      change R.categoryWithCofibrations.cofibrations (E.functor.map f)
      rwa [hC] at hf
    · intro A B f hf
      change N.categoryWithCofibrations.cofibrations f ∧
        N.categoryWithWeakEquivalences.weakEquivalences f at hf
      change R.categoryWithCofibrations.cofibrations (E.functor.map f) ∧
        R.categoryWithWeakEquivalences.weakEquivalences (E.functor.map f)
      rwa [hC, hW] at hf
  · intro A Z _ _ f
    let g := E.toAdjunction.homEquiv A Z f
    have hfac : E.functor.map g ≫ E.counitIso.hom.app Z = f := by
      change (E.toAdjunction.homEquiv A Z).symm g = f
      exact (E.toAdjunction.homEquiv A Z).symm_apply_apply f
    change R.categoryWithWeakEquivalences.weakEquivalences f ↔
      N.categoryWithWeakEquivalences.weakEquivalences g
    rw [SimplicialSpace.RezkModel.modelCategory_weakEquivalences, q.weakEquivalences_eq]
    calc
      SimplicialSpace.rezkWeakEquivalences f ↔
          SimplicialSpace.rezkWeakEquivalences (E.functor.map g ≫ E.counitIso.hom.app Z) := by
        rw [hfac]
      _ ↔ SimplicialSpace.rezkWeakEquivalences (E.functor.map g) :=
        SimplicialSpace.rezkWeakEquivalences.cancel_right_of_respectsIso _ _
      _ ↔ originalLocalEquivalences (originalFamily.{u} 1) g := (normalizedWeak_iff g).symm

private theorem fullChosenClasses :
    let F := originalLocalSmithModel (fullOriginalFamily.{u} 1)
    let R := SimplicialSpace.RezkModel.modelCategory.{u}
    let E := oneDesignatedEquivalence.{u}
    F.categoryWithCofibrations.cofibrations =
        R.categoryWithCofibrations.cofibrations.inverseImage E.functor ∧
    F.categoryWithWeakEquivalences.weakEquivalences =
        R.categoryWithWeakEquivalences.weakEquivalences.inverseImage E.functor ∧
    F.categoryWithFibrations.fibrations =
        R.categoryWithFibrations.fibrations.inverseImage E.functor := by
  have hc := originalLocalModelClasses_eq_of_localFibrant_iff
    (originalFamily.{u} 1) (fullOriginalFamily.{u} 1)
    (fun X => (fullNormalizedLocalF_iff X).symm)
  have hn := normalizedChosenClasses.{u}
  exact ⟨hc.1.symm.trans hn.1, hc.2.1.symm.trans hn.2.1, hc.2.2.symm.trans hn.2.2⟩

private theorem fullPhiQE :
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
      (originalLocalSmithModel (fullOriginalFamily.{u} 1))
      SimplicialSpace.RezkModel.modelCategory.{u}
      oneDesignatedEquivalence.{u}.functor oneDesignatedEquivalence.{u}.inverse
      oneDesignatedEquivalence.{u}.toAdjunction := by
  let N := originalLocalSmithModel (originalFamily.{u} 1)
  let F := originalLocalSmithModel (fullOriginalFamily.{u} 1)
  let R := SimplicialSpace.RezkModel.modelCategory.{u}
  let E := oneDesignatedEquivalence.{u}
  have hId : @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance (Original.{u} 1) inferInstance F N
      (Functor.id _) (Functor.id _) (Adjunction.id (C := Original.{u} 1)) :=
    originalLocalIdentity_isQuillenEquivalence_of_localFibrant_iff
      (fullOriginalFamily.{u} 1) (originalFamily.{u} 1) fullNormalizedLocalF_iff
  have hN := normalizedPhiQE.{u}
  have hComposite := @CategoryTheory.Adjunction.IsQuillenEquivalence.comp
    (Original.{u} 1) inferInstance (Original.{u} 1) inferInstance F N
    (Functor.id _) (Functor.id _) (Adjunction.id (C := Original.{u} 1))
    SimplicialSpace.{u} inferInstance R E.functor E.inverse E.toAdjunction hId hN
  have hC := fullChosenClasses.{u}.1
  have hW := fullChosenClasses.{u}.2.1
  refine @CategoryTheory.Adjunction.IsQuillenEquivalence.mk
    (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
    F R E.functor E.inverse E.toAdjunction ?_ ?_
  · refine @CategoryTheory.Adjunction.IsQuillenAdjunction.mk
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance
      F R E.functor E.inverse E.toAdjunction ?_ ?_
    · intro A B f hf
      change F.categoryWithCofibrations.cofibrations f at hf
      change R.categoryWithCofibrations.cofibrations (E.functor.map f)
      rwa [hC] at hf
    · intro A B f hf
      change F.categoryWithCofibrations.cofibrations f ∧
        F.categoryWithWeakEquivalences.weakEquivalences f at hf
      change R.categoryWithCofibrations.cofibrations (E.functor.map f) ∧
        R.categoryWithWeakEquivalences.weakEquivalences (E.functor.map f)
      rwa [hC, hW] at hf
  · intro A Z _ _ f
    have h := hComposite.homEquiv_weakEquivalence_iff f
    have he : ((Adjunction.id (C := Original.{u} 1)).comp E.toAdjunction).homEquiv A Z f =
        E.toAdjunction.homEquiv A Z f := by
      simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
      rfl
    change R.categoryWithWeakEquivalences.weakEquivalences f ↔
      F.categoryWithWeakEquivalences.weakEquivalences (E.toAdjunction.homEquiv A Z f)
    rw [he] at h
    exact h

/-- The complete original chosen N/F/R statement: all SIX inverse-image class getters,
both actual Phi1 carrier QEs and the full/normalized identity QE, with every model selected
internally and no equality of records/cardinals/factors or returned outcome hypothesis. -/
theorem one_model_classes_and_equivalence :
    let N := originalLocalSmithModel (originalFamily.{u} 1)
    let F := originalLocalSmithModel (fullOriginalFamily.{u} 1)
    let R := SimplicialSpace.RezkModel.modelCategory.{u}
    let E := oneDesignatedEquivalence.{u}
    N.categoryWithCofibrations.cofibrations =
        R.categoryWithCofibrations.cofibrations.inverseImage E.functor ∧
    N.categoryWithWeakEquivalences.weakEquivalences =
        R.categoryWithWeakEquivalences.weakEquivalences.inverseImage E.functor ∧
    N.categoryWithFibrations.fibrations =
        R.categoryWithFibrations.fibrations.inverseImage E.functor ∧
    F.categoryWithCofibrations.cofibrations =
        R.categoryWithCofibrations.cofibrations.inverseImage E.functor ∧
    F.categoryWithWeakEquivalences.weakEquivalences =
        R.categoryWithWeakEquivalences.weakEquivalences.inverseImage E.functor ∧
    F.categoryWithFibrations.fibrations =
        R.categoryWithFibrations.fibrations.inverseImage E.functor ∧
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance N R
      E.functor E.inverse E.toAdjunction ∧
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance SimplicialSpace.{u} inferInstance F R
      E.functor E.inverse E.toAdjunction ∧
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (Original.{u} 1) inferInstance (Original.{u} 1) inferInstance N F
      (Functor.id _) (Functor.id _) (Adjunction.id (C := Original.{u} 1)) := by
  have hn := normalizedChosenClasses.{u}
  have hf := fullChosenClasses.{u}
  exact ⟨hn.1, hn.2.1, hn.2.2, hf.1, hf.2.1, hf.2.2,
    normalizedPhiQE.{u}, fullPhiQE.{u},
    originalLocalIdentity_isQuillenEquivalence_of_localFibrant_iff
      (originalFamily.{u} 1) (fullOriginalFamily.{u} 1)
      (fun X => (fullNormalizedLocalF_iff X).symm)⟩

end SimplicialPresheaf.OrderedJFS
