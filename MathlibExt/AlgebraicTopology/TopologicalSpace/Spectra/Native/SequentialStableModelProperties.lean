/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableModels
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalRawPiHomotopyPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalContinuousSourceApproximation
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberIntegerNaturality
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePiLocalizationDetection
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Properness and integer homotopy of the original sequential stable model

The model is the existing native sequential model on the original enriched
carrier, with the same realized cardinal and caller bottom. Its weak class
is identified with the already constructed all-integer homotopy class.

Original projective cofibrations have the actual native based homotopy
extension property. The original raw homotopy pushout theorem proves
left properness. For a caller pullback along a level fibration, pasting
its square with the original zero-fiber square leaves the entire fiber
unchanged. The original integer fiber sequences and connecting naturality
then prove right properness by the group Five Lemma.

These are the sequential case of MMSS Theorem 9.2 and Lemma 9.10; the
all-integer criterion uses the prespectrum case of Proposition 8.7.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiLocalizationDetectionGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerNaturality
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.Spectra.NativeStableModels.SequentialStableModelProperties

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev family := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The weak class of the existing stable model is the full original integer homotopy class. -/
theorem weakEquivalences_eq_integerPiStar :
    sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      integerPiStarEquivalences.{u, v} := by
  change NativeK.omegaTests family = integerPiStarEquivalences
  exact (NativeK.localTestEquivalences_eq_omegaTests family).symm.trans
    nativeLocalTestEquivalences_eq_originalIntegerPiStar

/-- Every integer degree of the original group functor detects the same stable arrow. -/
theorem weakEquivalences_iff_integerPi
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f ↔
      ∀ q : ℤ, IsIso ((integerStablePiFunctor q).map f) := by
  rw [weakEquivalences_eq_integerPiStar]
  exact integerPiStarEquivalences_iff f

/-- The original integer homotopy projection detects the weak class of the same stable model. -/
theorem weakEquivalences_iff_integerStableProjection_isIso
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f ↔
      IsIso (integerStableProjection.map f) := by
  rw [weakEquivalences_eq_integerPiStar]
  exact integerPiStarEquivalences_iff_integerStableProjection_isIso f

/-- An actual HEP pushout preserves the entire original integer weak-equivalence class. -/
theorem integerPiStar_of_isPushout
    {A X Z P : Carrier.{u, v}} {i : A ⟶ X} {f : A ⟶ Z}
    {f' : X ⟶ P} {j : Z ⟶ P} (sq : IsPushout i f f' j)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hf : integerPiStarEquivalences f) : integerPiStarEquivalences f' := by
  let : integerPiStarEquivalences.{u, v}.ContainsIdentities :=
    integerPiStarEquivalences_containsIdentities
  exact PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    i (𝟙 A) (𝟙 X) i i f f' j IsPushout.of_id_snd sq hi hi
    (𝟙 A) (𝟙 X) f f'
    (by simp only [Category.id_comp, Category.comp_id])
    (by simp only [Category.id_comp])
    (by simp only [Category.id_comp]) sq.w.symm
    (integerPiStarEquivalences.id_mem A) (integerPiStarEquivalences.id_mem X) hf

omit B in
/-- Pasting a caller pullback preserves the whole actual fiber over the same original zero. -/
private def mappedFiberConeIsLimit
    {A B' X Y : Carrier.{u, v}} {p' : A ⟶ B'} {f' : A ⟶ X}
    {f : B' ⟶ Y} {p : X ⟶ Y} (sq : IsPullback p' f' f p)
    (c : PullbackCone p' (zeroTo B')) (hc : IsLimit c) :
    IsLimit (chosenMapCone (A := Index)
      (Arrow.homMk f' f sq.w.symm : Arrow.mk p' ⟶ Arrow.mk p) c) := by
  have hs : IsPullback c.fst c.snd p' (zeroTo B') := IsPullback.of_isLimit hc
  have ht : IsPullback (c.fst ≫ f') c.snd p (zeroTo Y) := by
    simpa only [zeroTo_naturality] using hs.paste_horiz sq.flip
  exact ht.isLimit

omit B in
/-- Base change along an original level fibration preserves every integer homotopy degree. -/
theorem integerPiStar_of_isPullback
    {A B' X Y : Carrier.{u, v}} {p' : A ⟶ B'} {f' : A ⟶ X}
    {f : B' ⟶ Y} {p : X ⟶ Y} (sq : IsPullback p' f' f p)
    (hp : ∀ n : ℕ, fibrations PointedCGWH.{u, v} (PointedCGWH.SequentialSpectrum.levelMap p n))
    (hf : integerPiStarEquivalences f) : integerPiStarEquivalences f' := by
  have hp' : ∀ n : ℕ,
      fibrations PointedCGWH.{u, v} (PointedCGWH.SequentialSpectrum.levelMap p' n) := by
    intro n
    exact (fibrations PointedCGWH.{u, v}).of_isPullback
      (sq.map (PointedCGWH.SequentialSpectrum.evaluation n)).flip (hp n)
  let a : Arrow.mk p' ⟶ Arrow.mk p := Arrow.homMk f' f sq.w.symm
  let c : PullbackCone p' (zeroTo B') := fiberCone p'
  let hc : IsLimit c := fiberConeIsLimit p'
  let d : PullbackCone p (zeroTo Y) := chosenMapCone a c
  let hd : IsLimit d := mappedFiberConeIsLimit sq c hc
  apply (integerPiStarEquivalences_iff f').mpr
  intro q
  let Q := integerStablePiFunctor q
  let Qplus := integerStablePiFunctor (q + 1)
  let Qminus := integerStablePiFunctor (q - 1)
  let _ : IsIso (Qplus.map a.right) := (integerPiStarEquivalences_iff f).mp hf (q + 1)
  let _ : IsIso (Q.map a.right) := (integerPiStarEquivalences_iff f).mp hf q
  let _ : IsIso (Q.map (chosenFiberMap a c d hd)) := by
    change IsIso (Q.map (hd.lift d))
    rw [hd.lift_self, Q.map_id]
    infer_instance
  let _ : IsIso (Qminus.map (chosenFiberMap a c d hd)) := by
    change IsIso (Qminus.map (hd.lift d))
    rw [hd.lift_self, Qminus.map_id]
    infer_instance
  exact CategoryTheory.originalGrpCat_fiveLemma
    (connectingPlusOne p' c hc hp' q) (Q.map c.fst) (Q.map p') (connecting p' c hc hp' q)
    (connectingPlusOne p d hd hp q) (Q.map d.fst) (Q.map p) (connecting p d hd hp q)
    (Qplus.map a.right) (Q.map (chosenFiberMap a c d hd)) (Q.map a.left)
    (Q.map a.right) (Qminus.map (chosenFiberMap a c d hd))
    (connectingPlusOne_naturality p' p hp' hp a c hc d hd q)
    ((Q.map_comp _ _).symm.trans
      ((Q.congr_map (chosenFiberMap_fst a c d hd)).trans (Q.map_comp _ _)))
    ((Q.map_comp _ _).symm.trans ((Q.congr_map a.w).trans (Q.map_comp _ _)))
    (connecting_naturality p' p hp' hp a c hc d hd q)
    (exact_at_fiber p' c hc hp' q) (exact_at_total p' c hc hp' q)
    (exact_at_base_degree p' c hc hp' q)
    (exact_at_fiber p d hd hp q) (exact_at_total p d hd hp q)
    (exact_at_base_degree p d hd hp q)

/-- The caller's original HEP pushout preserves the stable weak class of the same model. -/
theorem weakEquivalences_of_isPushout
    {A X Z P : Carrier.{u, v}} {i : A ⟶ X} {f : A ⟶ Z}
    {f' : X ⟶ P} {j : Z ⟶ P} (sq : IsPushout i f f' j)
    (hi : sequentialModelCategory.{u, v}.categoryWithCofibrations.cofibrations i)
    (hf : sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f) :
    sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f' := by
  rw [weakEquivalences_eq_integerPiStar] at hf ⊢
  apply integerPiStar_of_isPushout sq _ hf
  exact OriginalContinuousSourceApproximation.originalNativeILeft_le_HEP i hi

/-- The caller's original pullback along a stable fibration preserves the same stable weak class. -/
theorem weakEquivalences_of_isPullback
    {A B' X Y : Carrier.{u, v}} {p' : A ⟶ B'} {f' : A ⟶ X}
    {f : B' ⟶ Y} {p : X ⟶ Y} (sq : IsPullback p' f' f p)
    (hp : sequentialModelCategory.{u, v}.categoryWithFibrations.fibrations p)
    (hf : sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f) :
    sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences f' := by
  rw [weakEquivalences_eq_integerPiStar] at hf ⊢
  apply integerPiStar_of_isPullback sq _ hf
  have hLevel : fibrations Carrier.{u, v} p := NativeK.right_le_fibrations family p hp
  rw [HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq] at hLevel
  have hEval := (EvaluationTransfer.evaluationProperty_iff _ _ p).mp hLevel
  exact fun n => hEval
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)

/-- The existing sequential stable model is left proper on arbitrary original endpoints. -/
theorem sequentialModel_isLeftProper :
    let : ModelCategory Carrier.{u, v} := sequentialModelCategory
    IsLeftProper Carrier.{u, v} := by
  let : ModelCategory Carrier.{u, v} := sequentialModelCategory
  refine ⟨?_⟩
  constructor
  intro A X i hi
  constructor
  intro Z P j f' f sq hf
  exact weakEquivalences_of_isPushout sq hi hf

/-- The existing sequential stable model is right proper on arbitrary original endpoints. -/
theorem sequentialModel_isRightProper :
    let : ModelCategory Carrier.{u, v} := sequentialModelCategory
    IsRightProper Carrier.{u, v} := by
  let : ModelCategory Carrier.{u, v} := sequentialModelCategory
  refine ⟨?_⟩
  constructor
  intro X Y p hp
  constructor
  intro B' A p' f' f sq hf
  exact weakEquivalences_of_isPullback sq hp hf

/-- Both properness laws refer to the single existing original sequential stable model. -/
theorem sequentialModel_isProper :
    let : ModelCategory Carrier.{u, v} := sequentialModelCategory
    IsLeftProper Carrier.{u, v} ∧ IsRightProper Carrier.{u, v} :=
  ⟨sequentialModel_isLeftProper, sequentialModel_isRightProper⟩


/-- The homotopy category of the same original constructed sequential stable model. -/
abbrev StableHomotopyCategory :=
  let : ModelCategory Carrier.{u, v} := sequentialModelCategory
  HomotopyCategory Carrier.{u, v}

/-- The original canonical projection for that same actual stable model. -/
abbrev stableProjection : Carrier.{u, v} ⥤ StableHomotopyCategory.{u, v} :=
  let : ModelCategory Carrier.{u, v} := sequentialModelCategory
  toHomotopyCategory Carrier.{u, v}

private instance stableProjection_isIntegerLocalization :
    stableProjection.{u, v}.IsLocalization integerPiStarEquivalences := by
  let W : MorphismProperty Carrier.{u, v} :=
    sequentialModelCategory.categoryWithWeakEquivalences.weakEquivalences
  change W.Q.IsLocalization integerPiStarEquivalences
  rw [← weakEquivalences_eq_integerPiStar]
  infer_instance

private instance integerProjection_isIntegerLocalization :
    integerStableProjection.{u, v}.IsLocalization integerPiStarEquivalences := by
  unfold integerStableProjection
  infer_instance

/-- Localization uniqueness identifies the actual model Ho with the original integer Ho. -/
def integerHoEquivalence :
    StableHomotopyCategory.{u, v} ≌ IntegerStableHomotopyCategory.{u, v} :=
  Localization.uniq stableProjection integerStableProjection integerPiStarEquivalences

/-- The entire original source projection is retained through the actual Ho comparison. -/
def integerHoProjectionIso :
    stableProjection.{u, v} ⋙ integerHoEquivalence.functor ≅ integerStableProjection :=
  Localization.compUniqFunctor stableProjection integerStableProjection integerPiStarEquivalences

omit B in
/-- The existing integer Ho functor retains every complete original source group map. -/
private def integerProjectionPiIso (q : ℤ) :
    integerStableProjection.{u, v} ⋙ integerStablePiStableFunctor q ≅ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => Iso.refl ((integerStablePiFunctor q).obj X)) (fun {X Y} f => by
    change (integerStablePiStableFunctor q).map (integerStableProjection.map f) ≫
        𝟙 ((integerStablePiFunctor q).obj Y) =
      𝟙 ((integerStablePiFunctor q).obj X) ≫ (integerStablePiFunctor q).map f
    exact (Category.comp_id ((integerStablePiStableFunctor q).map
      (integerStableProjection.map f))).trans
        ((integerStablePiStableFunctor_map q f).trans
          (Category.id_comp ((integerStablePiFunctor q).map f)).symm))

/-- Every original integer homotopy functor descends to the actual constructed model's Ho. -/
def integerPiHoFunctor (q : ℤ) : StableHomotopyCategory.{u, v} ⥤ GrpCat.{v} :=
  integerHoEquivalence.functor ⋙ integerStablePiStableFunctor q

/-- The full descended functor agrees naturally with every original source group and map. -/
def integerPiHoSourceIso (q : ℤ) :
    stableProjection.{u, v} ⋙ integerPiHoFunctor q ≅ integerStablePiFunctor q :=
  (Functor.associator stableProjection integerHoEquivalence.functor
    (integerStablePiStableFunctor q)).symm ≪≫
    Functor.isoWhiskerRight integerHoProjectionIso (integerStablePiStableFunctor q) ≪≫
      integerProjectionPiIso q

/-- All original integer functors jointly detect every arrow of the actual stable model Ho. -/
theorem integerPiHoFunctor_jointly_reflects_isomorphisms
    {X Y : StableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    (∀ q : ℤ, IsIso ((integerPiHoFunctor q).map f)) ↔ IsIso f :=
  (integerStablePiStableFunctor_jointly_reflects_isomorphisms
    (integerHoEquivalence.functor.map f)).trans
      (isIso_iff_of_reflects_iso f integerHoEquivalence.functor)

end PointedCGWH.Spectra.NativeStableModels.SequentialStableModelProperties
