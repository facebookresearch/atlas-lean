/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.OriginalFactors
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.NativeStableIndexComparisons
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalRawPiHEPPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOmegaMappingOrdinalClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialStableModelProperties
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeScalarUnreplacedOmegaPreservation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOmegaCoproductComponentClosure
import MathlibExt.CategoryTheory.Enriched.Ordinary.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Unique
import MathlibExt.CategoryTheory.Enriched.FreeStabilizationScalar

/-!
# The original orthogonal integer replacement squares

The I approximation keeps its actual weak counit and both inverse group maps.
The canonical comparison to the K replacement of that approximation is the
inverse I-counit group map followed by the actual K-unit group map. Every
original integer and both original endpoints remain in its naturality square.

The actual K output is Omega without assumptions on the original endpoints.
Consequently its original integer tests detect the original Omega weak class.
Integer invertibility of the K unit, and therefore the unrestricted integer
criterion on the original arrow, remain separate assertions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
universe w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.OriginalIntegerCharacterization

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev Q := NativeStableModels.cofibrantReplacement (B := B)
private abbrev R := NativeStableModels.fibrantReplacement (B := B)
private abbrev ε := NativeStableModels.qCounit (B := B)
private abbrev η := NativeStableModels.rUnit (B := B)
private abbrev P (q : ℤ) := OrthogonalIntegerHomotopy.integerPiFunctor.{u, v} q
private abbrev qIso (q : ℤ) := NativeStableCofiberIntegerMaps.qCounitIntegerNatIso
  (B := B) (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q

/-- Both entire endpoints of the original I-counit square give its integer Arrow isomorphism. -/
def qCounitIntegerArrowIso (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((P q).map (Q.map f)) ≅ Arrow.mk ((P q).map f) :=
  Arrow.isoMk ((qIso q).app X) ((qIso q).app Y) ((qIso q).hom.naturality f).symm

/-- Every original integer map is invertible exactly when its actual I approximation is. -/
theorem qMap_integerPi_isIso_iff (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    IsIso ((P q).map (Q.map f)) ↔ IsIso ((P q).map f) :=
  (MorphismProperty.isomorphisms GrpCat.{v}).arrow_mk_iso_iff (qCounitIntegerArrowIso q f)

/-- Both transfer directions keep every integer of the same original I replacement square. -/
theorem qMap_integerPiStar_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (Q.map f) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences f := by
  rw [OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff,
    OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff]
  exact forall_congr' (fun q => qMap_integerPi_isIso_iff q f)

/-- The original weak I counits transfer all Omega tests in both directions on arbitrary arrows. -/
theorem qMap_omegaTests_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily (Q.map f) ↔ NativeK.omegaTests orthogonalFamily f := by
  let W := NativeK.omegaTests (B := B) orthogonalFamily
  have hX : W (ε.app X) := NativeK.levelWeak_le_omegaTests orthogonalFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) (A := O.{u, v}) X)
  have hY : W (ε.app Y) := NativeK.levelWeak_le_omegaTests orthogonalFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) (A := O.{u, v}) Y)
  have hn : Q.map f ≫ ε.app Y = ε.app X ≫ f := ε.naturality f
  constructor
  · intro hf
    have h := W.comp_mem _ _ hf hY
    rw [hn] at h
    exact W.of_precomp _ _ hX h
  · intro hf
    have h := W.comp_mem _ _ hX hf
    rw [← hn] at h
    exact W.of_postcomp _ _ hY h

/-- Every integer retains both original K-unit endpoint maps and the whole original input arrow. -/
theorem rUnit_integerPi_naturality (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    (P q).map f ≫ (P q).map (η.app Y) =
      (P q).map (η.app X) ≫ (P q).map (R.map f) := by
  have h := (P q).congr_map (η.naturality f)
  simpa only [Functor.map_comp, Functor.id_map] using h

/-- The actual original-to-RQ group comparison is the inverse I counit followed by the K unit. -/
def integerReplacementComparison (q : ℤ) : P q ⟶ (Q ⋙ R) ⋙ P q :=
  (qIso q).inv ≫
    (Functor.isoWhiskerRight (Functor.rightUnitor Q).symm (P q)).hom ≫
      Functor.whiskerRight (Functor.whiskerLeft Q η) (P q)

/-- The full comparison retains the actual original I inverse and original K inclusion. -/
theorem integerReplacementComparison_app (q : ℤ) (X : C.{u, v}) :
    (integerReplacementComparison q).app X =
      (qIso q).inv.app X ≫ (P q).map (η.app (Q.obj X)) := by
  change (qIso q).inv.app X ≫ (P q).map (𝟙 (Q.obj X)) ≫ (P q).map (η.app (Q.obj X)) = _
  exact (congrArg
    (fun a => (qIso q).inv.app X ≫ a ≫ (P q).map (η.app (Q.obj X)))
    ((P q).map_id (Q.obj X))).trans
      (congrArg (fun a => (qIso q).inv.app X ≫ a) (Category.id_comp _))

/-- Its whole source/target square retains the original map and the actual R(Q f) map. -/
theorem integerReplacementComparison_naturality (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    (P q).map f ≫ (integerReplacementComparison q).app Y =
      (integerReplacementComparison q).app X ≫ (P q).map (R.map (Q.map f)) :=
  (integerReplacementComparison q).naturality f

/-- The actual R(Q f) arrow has the same original Omega tests through both replacement squares. -/
theorem rqMap_omegaTests_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily (R.map (Q.map f)) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (IndexKan.NativeStableIndexComparisons.orthogonalOriginalR_map_omegaTests_iff (Q.map f)).trans
    (qMap_omegaTests_iff f)

/-- Level weakness of the actual R(Q f) tests the original arrow with arbitrary endpoints. -/
theorem rqMap_levelWeak_iff_omegaTests {X Y : C.{u, v}} (f : X ⟶ Y) :
    weakEquivalences C.{u, v} (R.map (Q.map f)) ↔ NativeK.omegaTests orthogonalFamily f :=
  (NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily (R.map (Q.map f))
    (NativeStableModels.fibrantReplacement_isOmega (Q.obj X))
    (NativeStableModels.fibrantReplacement_isOmega (Q.obj Y))).symm.trans (rqMap_omegaTests_iff f)

/-- Every original integer of the actual R(Q f) detects the original all-target Omega class. -/
theorem rqMap_integerPiStar_iff_omegaTests {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (R.map (Q.map f)) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (OrthogonalIntegerHomotopy.integerPiStar_iff_levelWeak_of_isOmega (R.map (Q.map f))
    (NativeStableModels.fibrantReplacement_isOmega (Q.obj X))
    (NativeStableModels.fibrantReplacement_isOmega (Q.obj Y))).trans (rqMap_levelWeak_iff_omegaTests f)

/-- Applying the original K functor to the original I counit gives an actual level weak comparison. -/
theorem rMap_qCounit_levelWeak (X : C.{u, v}) :
    weakEquivalences C.{u, v} (R.map (ε.app X)) :=
  (NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily (R.map (ε.app X))
    (NativeStableModels.fibrantReplacement_isOmega (Q.obj X))
    (NativeStableModels.fibrantReplacement_isOmega X)).mp
      ((IndexKan.NativeStableIndexComparisons.orthogonalOriginalR_map_omegaTests_iff (ε.app X)).mpr
        (NativeK.levelWeak_le_omegaTests orthogonalFamily _
          (Replacement.cofibrantReplacementCounit_mem_weakEquivalences
            (B := B) (A := O.{u, v}) X)))

/-- Both original R-counit endpoints identify the integer arrows of R(Q f) and R(f). -/
def rQCounitIntegerArrowIso (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((P q).map (R.map (Q.map f))) ≅ Arrow.mk ((P q).map (R.map f)) := by
  let eX := NativeStableCofiberIntegerMaps.integerPiLevelWeakIso
    (B := B) (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q
    (R.map (ε.app X)) (rMap_qCounit_levelWeak X)
  let eY := NativeStableCofiberIntegerMaps.integerPiLevelWeakIso
    (B := B) (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q
    (R.map (ε.app Y)) (rMap_qCounit_levelWeak Y)
  refine Arrow.isoMk eX eY ?_
  have hn : Q.map f ≫ ε.app Y = ε.app X ≫ f := ε.naturality f
  change (P q).map (R.map (ε.app X)) ≫ (P q).map (R.map f) =
    (P q).map (R.map (Q.map f)) ≫ (P q).map (R.map (ε.app Y))
  have hR : R.map (ε.app X) ≫ R.map f = R.map (Q.map f) ≫ R.map (ε.app Y) :=
    (R.map_comp _ _).symm.trans ((R.congr_map hn.symm).trans (R.map_comp _ _))
  exact ((P q).map_comp _ _).symm.trans (((P q).congr_map hR).trans ((P q).map_comp _ _))

/-- The actual R(Q f) and R(f) arrows have equivalent tests in every unchanged integer degree. -/
theorem rQMap_integerPi_isIso_iff (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    IsIso ((P q).map (R.map (Q.map f))) ↔ IsIso ((P q).map (R.map f)) :=
  (MorphismProperty.isomorphisms GrpCat.{v}).arrow_mk_iso_iff (rQCounitIntegerArrowIso q f)

/-- Both complete integer classes transfer through the actual K image of the I counit square. -/
theorem rQMap_integerPiStar_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (R.map (Q.map f)) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences (R.map f) := by
  rw [OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff,
    OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff]
  exact forall_congr' (fun q => rQMap_integerPi_isIso_iff q f)

/-- The canonical RQ comparison followed by the original R-counit comparison is the original K unit. -/
theorem integerReplacementComparison_rQCounit (q : ℤ) (X : C.{u, v}) :
    (integerReplacementComparison q).app X ≫ (P q).map (R.map (ε.app X)) =
      (P q).map (η.app X) := by
  have hUnit := (rUnit_integerPi_naturality q (ε.app X)).symm
  have hQ : (qIso q).inv.app X ≫ (P q).map (ε.app X) = 𝟙 ((P q).obj X) :=
    ((qIso q).app X).inv_hom_id
  calc
    _ = ((qIso q).inv.app X ≫ (P q).map (η.app (Q.obj X))) ≫ (P q).map (R.map (ε.app X)) :=
      congrArg (fun g => g ≫ (P q).map (R.map (ε.app X))) (integerReplacementComparison_app q X)
    _ = (qIso q).inv.app X ≫ ((P q).map (η.app (Q.obj X)) ≫ (P q).map (R.map (ε.app X))) :=
      Category.assoc _ _ _
    _ = (qIso q).inv.app X ≫ ((P q).map (ε.app X) ≫ (P q).map (η.app X)) :=
      congrArg (fun g => (qIso q).inv.app X ≫ g) hUnit
    _ = ((qIso q).inv.app X ≫ (P q).map (ε.app X)) ≫ (P q).map (η.app X) :=
      (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun g => g ≫ (P q).map (η.app X)) hQ).trans (Category.id_comp _)

section IntegerHEPCellClosure

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  (integerPiStarEquivalences_containsIdentities integerPiStarEquivalences_hasTwoOutOfThreeProperty)

private abbrev U := OrthogonalIntegerHomotopy.underlyingSequential.{u, v}
private abbrev seqFamily := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [Small.{v} J]

/-- Every original continuous HEP/integer chain keeps its own integer-weak bottom-to-colimit map. -/
theorem originalHEPOrdinal_integerPiStar
    (F : J ⥤ C.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (c.ι.app ⊥) := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  let _ : HasColimitsOfShape J PointedCGWH.{u, v} :=
    hasColimitsOfShape_of_essentiallySmall.{v} J PointedCGWH.{u, v}
  let G := F ⋙ U
  let _ : G.IsWellOrderContinuous :=
    { nonempty_isColimit := fun j hj => ⟨by
        let _ : HasColimitsOfShape (Set.Iio j) PointedCGWH.{u, v} :=
          hasColimitsOfShape_of_essentiallySmall.{v} (Set.Iio j) PointedCGWH.{u, v}
        let _ : PreservesColimit ((Set.principalSegIio j).monotone.functor ⋙ F) U :=
          originalRestriction_preservesColimit sequentialOrthogonalOperatorIndexFunctor
            ((Set.principalSegIio j).monotone.functor ⋙ F)
        exact isColimitOfPreserves U (F.isColimitOfIsWellOrderContinuous j hj)⟩ }
  have hSeq := NativeStableModels.SequentialStableModelProperties.weakEquivalences_eq_integerPiStar.{u, v}
    (B := B)
  change NativeK.omegaTests seqFamily =
    PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences at hSeq
  have hG (j : J) (hj : ¬IsMax j) :
      PointedCGWH.EnrichedBasedHomotopyExtension.property (G.map (homOfLE (Order.le_succ j))) :=
    OrthogonalIntegerHomotopy.underlyingSequential_HEP _ (hF j hj)
  have hGW (j : J) (hj : ¬IsMax j) : NativeK.omegaTests seqFamily
      (G.map (homOfLE (Order.le_succ j))) := by
    rw [hSeq]
    exact (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying _).mp (hW j hj)
  have hEnd := OriginalOmegaMappingOrdinalClosure.originalHEPOrdinal_small_omegaTests
    seqFamily G hG hGW (U.mapCocone c)
    (OrthogonalIntegerHomotopy.underlyingSequentialCoconeIsColimit c hc)
  change NativeK.omegaTests seqFamily (U.map (c.ι.app ⊥)) at hEnd
  rw [hSeq] at hEnd
  exact (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying _).mpr hEnd

/-- A full original HEP/integer transfinite witness gives integer weakness of its original final arrow. -/
theorem originalTransfiniteWitness_integerPiStar {X Y : C.{u, v}} {f : X ⟶ Y}
    (d : (PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓
      OrthogonalIntegerHomotopy.integerPiStarEquivalences).TransfiniteCompositionOfShape J f) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences f := by
  let c : Cocone d.F := { pt := Y, ι := d.incl }
  have hEnd := originalHEPOrdinal_integerPiStar d.F
    (fun j hj => (d.map_mem j hj).1) (fun j hj => (d.map_mem j hj).2) c d.isColimit
  let W := OrthogonalIntegerHomotopy.integerPiStarEquivalences.{u, v}
  let _ : W.ContainsIdentities := by
    unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
    let _ := integerPiStarEquivalences_containsIdentities.{u, v}
    infer_instance
  let _ : W.IsStableUnderComposition := by
    unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
    let _ := integerPiStarEquivalences_hasTwoOutOfThreeProperty.{u, v}
    infer_instance
  let _ : W.RespectsIso := by
    unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
      PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
    infer_instance
  have hIso : W d.isoBot.inv := W.of_isIso _
  exact d.fac ▸ W.comp_mem _ _ hIso hEnd

/-- The original HEP/integer class is closed under every original permitted small ordinal shape. -/
instance originalHEPInteger_isStableUnderTransfiniteComposition :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (PointedCGWH.EnrichedBasedHomotopyExtension.property (I := O.{u, v}) ⊓
        OrthogonalIntegerHomotopy.integerPiStarEquivalences.{u, v}) J where
  le := by
    intro X Y f hf
    obtain ⟨d⟩ := hf
    exact ⟨MorphismProperty.transfiniteCompositionsOfShape_le _ J _
      (d.ofLE inf_le_left).mem, originalTransfiniteWitness_integerPiStar d⟩

end IntegerHEPCellClosure

/-- Every original integer-weak map with cofibrant components stays integer weak under a cofibrant scalar. -/
theorem tensorMap_integerPiStar_of_componentCofibrant
    (M : PointedCGWH.{u, v}) [IsCofibrant M] {X Y : C.{u, v}} (f : X ⟶ Y)
    (hX : ∀ a : O.{u, v}, IsCofibrant (X.toEnrichedFunctor.obj a))
    (hY : ∀ a : O.{u, v}, IsCofibrant (Y.toEnrichedFunctor.obj a))
    (hf : OrthogonalIntegerHomotopy.integerPiStarEquivalences f) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences ((EnrichedFunctorCat.tensorLeft M).map f) := by
  have hSeq := NativeStableModels.SequentialStableModelProperties.weakEquivalences_eq_integerPiStar.{u, v}
    (B := B)
  change NativeK.omegaTests seqFamily =
    PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences at hSeq
  have hPi : PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
      (U.map f) := (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying f).mp hf
  have hOmega : NativeK.omegaTests seqFamily (U.map f) := hSeq.symm ▸ hPi
  have hTensor := NativeK.tensorMap_omegaTests_of_componentCofibrant
    seqFamily PointedCGWH.Spectra.Sequential.hom_isCofibrant M (U.map f)
    (fun a => hX (sequentialOrthogonalOperatorIndexFunctor.obj a))
    (fun a => hY (sequentialOrthogonalOperatorIndexFunctor.obj a)) hOmega
  rw [hSeq] at hTensor
  let e := originalRestrictionScalarNatIso sequentialOrthogonalOperatorIndexFunctor M
  let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft M).map (U.map f)) ≅
      Arrow.mk (U.map ((EnrichedFunctorCat.tensorLeft M).map f)) :=
    Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
  let W := PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
  let _ : W.RespectsIso := by
    unfold W
      PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
    infer_instance
  exact (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying _).mpr
    ((W.arrow_mk_iso_iff a).mp hTensor)

section IntegerCoproductClosure

variable {J : Type w} [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]
  [HasProductsOfShape J PointedCGWH.{u, v}]

private def coproductRestrictionArrowIso
    {X Y : J → C.{u, v}} (f : ∀ j, X j ⟶ Y j) :
    Arrow.mk (Limits.Sigma.map (fun j => U.map (f j))) ≅ Arrow.mk (U.map (Limits.Sigma.map f)) := by
  let _ : PreservesColimit (Discrete.functor X) U :=
    originalRestriction_preservesColimit sequentialOrthogonalOperatorIndexFunctor _
  let _ : PreservesColimit (Discrete.functor Y) U :=
    originalRestriction_preservesColimit sequentialOrthogonalOperatorIndexFunctor _
  let eX := (PreservesCoproduct.iso U X).symm
  let eY := (PreservesCoproduct.iso U Y).symm
  refine Arrow.isoMk eX eY ?_
  change sigmaComparison U X ≫ U.map (Limits.Sigma.map f) =
    Limits.Sigma.map (fun j => U.map (f j)) ≫ sigmaComparison U Y
  apply Limits.Sigma.hom_ext
  intro j
  calc
    _ = U.map (Limits.Sigma.ι X j) ≫ U.map (Limits.Sigma.map f) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun g => g ≫ U.map (Limits.Sigma.map f)) (ι_comp_sigmaComparison U X j))
    _ = U.map (Limits.Sigma.ι X j ≫ Limits.Sigma.map f) := (U.map_comp _ _).symm
    _ = U.map (f j ≫ Limits.Sigma.ι Y j) := U.congr_map (Limits.Sigma.ι_map f j)
    _ = U.map (f j) ≫ U.map (Limits.Sigma.ι Y j) := U.map_comp _ _
    _ = U.map (f j) ≫ (Limits.Sigma.ι (fun j => U.obj (Y j)) j ≫ sigmaComparison U Y) :=
      congrArg (fun g => U.map (f j) ≫ g) (ι_comp_sigmaComparison U Y j).symm
    _ = (U.map (f j) ≫ Limits.Sigma.ι (fun j => U.obj (Y j)) j) ≫ sigmaComparison U Y :=
      (Category.assoc _ _ _).symm
    _ = (Limits.Sigma.ι (fun j => U.obj (X j)) j ≫
        Limits.Sigma.map (fun j => U.map (f j))) ≫ sigmaComparison U Y :=
      congrArg (fun g => g ≫ sigmaComparison U Y) (Limits.Sigma.ι_map (fun j => U.map (f j)) j).symm
    _ = _ := Category.assoc _ _ _

/-- The actual original coproduct map preserves integer weakness on all component-cofibrant endpoints. -/
theorem sigmaMap_integerPiStar_of_componentCofibrant
    {X Y : J → C.{u, v}} (f : ∀ j, X j ⟶ Y j)
    (hX : ∀ j a, IsCofibrant ((X j).toEnrichedFunctor.obj a))
    (hY : ∀ j a, IsCofibrant ((Y j).toEnrichedFunctor.obj a))
    (hf : ∀ j, OrthogonalIntegerHomotopy.integerPiStarEquivalences (f j)) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (Limits.Sigma.map f) := by
  have hSeq := NativeStableModels.SequentialStableModelProperties.weakEquivalences_eq_integerPiStar.{u, v}
    (B := B)
  change NativeK.omegaTests seqFamily =
    PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences at hSeq
  have hOmega (j : J) : NativeK.omegaTests seqFamily (U.map (f j)) :=
    hSeq.symm ▸ (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying (f j)).mp (hf j)
  have hSigma := NativeOmegaCoproductComponentClosure.sigmaMap_omegaTests_of_componentCofibrant
    seqFamily PointedCGWH.Spectra.Sequential.hom_isCofibrant (fun j => U.map (f j))
    (fun j a => hX j (sequentialOrthogonalOperatorIndexFunctor.obj a))
    (fun j a => hY j (sequentialOrthogonalOperatorIndexFunctor.obj a)) hOmega
  rw [hSeq] at hSigma
  let W := PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
  let _ : W.RespectsIso := by
    unfold W
      PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
    infer_instance
  exact (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying _).mpr
    ((W.arrow_mk_iso_iff (coproductRestrictionArrowIso f)).mp hSigma)

end IntegerCoproductClosure

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  (integerPiStarEquivalences_containsIdentities integerPiStarEquivalences_hasTwoOutOfThreeProperty)

/-- The full original scalar pushout product of an integer-weak cofibration is integer weak. -/
theorem scalarPushoutProduct_integerPiStar
    {A D : PointedCGWH.{u, v}} [IsCofibrant A] [IsCofibrant D] (i : A ⟶ D)
    {X Y : C.{u, v}} (u : X ⟶ Y) (hu : cofibrations C.{u, v} u)
    (hX : ∀ a : O.{u, v}, IsCofibrant (X.toEnrichedFunctor.obj a))
    (hY : ∀ a : O.{u, v}, IsCofibrant (Y.toEnrichedFunctor.obj a))
    (hPi : OrthogonalIntegerHomotopy.integerPiStarEquivalences u)
    (sq : EnrichedFunctorCat.ScalarLeibniz.tensorBifunctor.PushoutObjObj i u) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences sq.ι := by
  let W := OrthogonalIntegerHomotopy.integerPiStarEquivalences.{u, v}
  let _ : W.ContainsIdentities := by
    unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
    let _ := integerPiStarEquivalences_containsIdentities.{u, v}
    infer_instance
  let _ : W.HasTwoOutOfThreeProperty := by
    unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
    let _ := integerPiStarEquivalences_hasTwoOutOfThreeProperty.{u, v}
    infer_instance
  let AU := (EnrichedFunctorCat.tensorLeft A).map u
  let DU := (EnrichedFunctorCat.tensorLeft D).map u
  let AX := (EnrichedFunctorCat.tensorLeft A).obj X
  let DX := (EnrichedFunctorCat.tensorLeft D).obj X
  let j : AX ⟶ DX := (EnrichedFunctorCat.ScalarLeibniz.tensorBifunctor.map i).app X
  have hA : W AU := tensorMap_integerPiStar_of_componentCofibrant A u hX hY hPi
  have hD : W DU := tensorMap_integerPiStar_of_componentCofibrant D u hX hY hPi
  have hACof : cofibrations C.{u, v} AU :=
    (ScalarCompatibility.scalar_isQuillen (A := O.{u, v}) A).preservesCofibrations u hu
  have hAHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property AU := by
    rw [HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq] at hACof
    exact OriginalContinuousSourceApproximation.originalNativeILeft_le_HEP _ hACof
  have hIdHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (𝟙 AX) :=
    PointedCGWH.EnrichedBasedHomotopyExtension.property.id_mem AX
  have hInl : W sq.inl :=
    OrthogonalIntegerHomotopy.originalOrthogonalRawPiHEPpushoutGluing
      (𝟙 AX) j j (𝟙 DX) AU j sq.inr sq.inl
      IsPushout.of_id_fst sq.isPushout.flip hIdHEP hAHEP
      (𝟙 AX) AU (𝟙 DX) sq.inl
      (by simp only [Category.id_comp])
      (by simp only [Category.id_comp, Category.comp_id])
      sq.isPushout.w.symm (by simp only [Category.id_comp])
      (W.id_mem AX) hA (W.id_mem DX)
  have hFac : sq.inl ≫ sq.ι = DU := sq.inl_ι
  exact W.of_precomp sq.inl sq.ι hInl (hFac.symm ▸ hD)

section OriginalKIntegerCells

private abbrev WInteger := OrthogonalIntegerHomotopy.integerPiStarEquivalences.{u, v}
private abbrev HEPInteger :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property (I := O.{u, v}) ⊓ WInteger.{u, v}

omit B in
private instance originalInteger_containsIdentities : WInteger.{u, v}.ContainsIdentities := by
  unfold WInteger OrthogonalIntegerHomotopy.integerPiStarEquivalences
  let _ := integerPiStarEquivalences_containsIdentities.{u, v}
  infer_instance

omit B in
private instance originalInteger_twoOutOfThree : WInteger.{u, v}.HasTwoOutOfThreeProperty := by
  unfold WInteger OrthogonalIntegerHomotopy.integerPiStarEquivalences
  let _ := integerPiStarEquivalences_hasTwoOutOfThreeProperty.{u, v}
  infer_instance

omit B in
private instance originalInteger_retracts : WInteger.{u, v}.IsStableUnderRetracts where
  of_retract d hg := by
    apply (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff _).mpr
    intro q
    exact (MorphismProperty.isomorphisms GrpCat.{v}).of_retract (d.map (P q))
      ((OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff _).mp hg q)

/-- The original HEP attaching arrow carries all integer tests through the caller's actual pushout. -/
theorem hepPushout_integerPiStar
    {A X Z T : C.{u, v}} (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ T) (kZ : Z ⟶ T)
    (sq : IsPushout i z kX kZ)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hPi : OrthogonalIntegerHomotopy.integerPiStarEquivalences i) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences kZ :=
  OrthogonalIntegerHomotopy.originalOrthogonalRawPiHEPpushoutGluing
    (𝟙 A) z z (𝟙 Z) i z kX kZ IsPushout.of_id_fst sq
    (PointedCGWH.EnrichedBasedHomotopyExtension.property.id_mem A) hi
    (𝟙 A) i (𝟙 Z) kZ
    (by simp only [Category.id_comp])
    (by simp only [Category.id_comp, Category.comp_id])
    sq.w (by simp only [Category.id_comp])
    (WInteger.id_mem A) hPi (WInteger.id_mem Z)

/-- The same full HEP/integer class is stable under every original cobase square. -/
instance originalHEPInteger_isStableUnderCobaseChange :
    HEPInteger.{u, v}.IsStableUnderCobaseChange where
  of_isPushout sq hi :=
    ⟨MorphismProperty.of_isPushout sq hi.1,
      hepPushout_integerPiStar _ _ _ _ sq.flip hi.1 hi.2⟩

omit B in
/-- The actual mapping-cylinder factors give the unchanged original stabilization map in every degree. -/
theorem originalCylinder_integerPi_fac (q : ℤ) (l : ℕ × ℕ) :
    (P q).map (NativeK.cylinderSource orthogonalFamily.{u, v} l) ≫
        (P q).map (NativeK.cylinderRetraction orthogonalFamily.{u, v} l) =
      (P q).map (NativeK.stabilization orthogonalFamily.{u, v} l) :=
  ((P q).map_comp _ _).symm.trans ((P q).congr_map (NativeK.cylinder_fac orthogonalFamily.{u, v} l))

/-- An integer-weak original stabilization seed makes its actual cylinder source integer weak. -/
theorem originalCylinder_integerPiStar_of_stabilization
    (l : ℕ × ℕ)
    (hl : OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.cylinderSource orthogonalFamily.{u, v} l) := by
  have hRet : WInteger (NativeK.cylinderRetraction orthogonalFamily.{u, v} l) :=
    OrthogonalIntegerHomotopy.levelWeak_le_integerPiStarEquivalences _
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp
        (NativeK.cylinderRetraction_weak orthogonalFamily.{u, v} l))
  have hComp : WInteger (NativeK.cylinderSource orthogonalFamily.{u, v} l ≫
      NativeK.cylinderRetraction orthogonalFamily.{u, v} l) :=
    (NativeK.cylinder_fac orthogonalFamily.{u, v} l).symm ▸ hl
  exact WInteger.of_postcomp (NativeK.cylinderSource orthogonalFamily.{u, v} l)
    (NativeK.cylinderRetraction orthogonalFamily.{u, v} l) hRet hComp

omit B in
/-- Both literal K-corner equations retain the original boundary, cylinder and scalar arrows. -/
theorem originalGeneratorSquare_fac (l : ℕ × ℕ) (m : ℕ) :
    (NativeK.generatorSquare orthogonalFamily.{u, v} l m).inl ≫
        NativeK.generatorMap orthogonalFamily.{u, v} l m =
      (EnrichedFunctorCat.tensorLeft (Arrow.mk (NativeK.boundaryMap.{u, v} m)).right).map
        (NativeK.cylinderSource orthogonalFamily.{u, v} l) ∧
    (NativeK.generatorSquare orthogonalFamily.{u, v} l m).inr ≫
        NativeK.generatorMap orthogonalFamily.{u, v} l m =
      (EnrichedFunctorCat.ScalarLeibniz.tensorBifunctor.map (NativeK.boundaryMap.{u, v} m)).app
        (NativeK.cylinder orthogonalFamily.{u, v} l) :=
  ⟨(NativeK.generatorSquare orthogonalFamily.{u, v} l m).inl_ι,
    (NativeK.generatorSquare orthogonalFamily.{u, v} l m).inr_ι⟩

/-- The actual native scalar boundary/cylinder generator is integer weak from its stabilization seed. -/
theorem originalGenerator_integerPiStar_of_stabilization
    (l : ℕ × ℕ) (m : ℕ)
    (hl : OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.generatorMap orthogonalFamily.{u, v} l m) := by
  let i := NativeK.boundaryMap.{u, v} m
  have hBoundary := NativeK.pointedBoundary_endpoints i
    (.map (CGWH.boundary_mem_realizedBoundaryInclusions m))
  let _ : IsCofibrant (Arrow.mk i).left := hBoundary.1
  let _ : IsCofibrant (Arrow.mk i).right := hBoundary.2
  let X : C.{u, v} := (Arrow.mk (NativeK.stabilization orthogonalFamily.{u, v} l)).left
  let Y : C.{u, v} := NativeK.cylinder orthogonalFamily.{u, v} l
  let _ : IsCofibrant X := NativeK.stabilization_source_cofibrant orthogonalFamily.{u, v} l
  let _ : IsCofibrant Y := NativeK.cylinder_cofibrant orthogonalFamily.{u, v} l
  let po := NativeK.generatorSquare orthogonalFamily.{u, v} l m
  let oldPo := Functor.PushoutObjObj.transport (by rfl) po
  have h : WInteger oldPo.ι := scalarPushoutProduct_integerPiStar (B := B)
    (A := (Arrow.mk i).left) (D := (Arrow.mk i).right) i
    (NativeK.cylinderSource orthogonalFamily.{u, v} l)
    ((HomotopicalAlgebra.cofibration_iff _).mp (NativeK.cylinderSource_cofibration orthogonalFamily.{u, v} l))
    (NativeCofibrantComponents.component_isCofibrant NativeStable.orthogonalHom_isCofibrant X)
    (NativeCofibrantComponents.component_isCofibrant NativeStable.orthogonalHom_isCofibrant Y)
    (originalCylinder_integerPiStar_of_stabilization l hl) oldPo
  have hSame : oldPo.ι = po.ι := eq_of_heq (Functor.PushoutObjObj.transport_arrow_heq (by rfl) po)
  rwa [hSame] at h

/-- Every literal horn and correlated K generator is integer weak from the actual stabilization seeds. -/
theorem originalK_generators_integerPiStar_of_stabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    NativeStableModels.originalK.{u, v} ≤ OrthogonalIntegerHomotopy.integerPiStarEquivalences := by
  change (NativeK.levelJ (I := O.{u, v}) ⊔ NativeK.additionalGenerators orthogonalFamily.{u, v}) ≤
    WInteger
  apply sup_le
  · intro X Y f hJ
    have h := (NativeK.levelJ (I := O.{u, v})).le_llp_rlp f hJ
    rw [← HomotopicalAlgebra.EnrichedProjective.Native.trivialCofibrations_eq] at h
    exact OrthogonalIntegerHomotopy.levelWeak_le_integerPiStarEquivalences f h.2
  · change MorphismProperty.ofHoms
      (fun lm : (ℕ × ℕ) × ℕ => NativeK.generatorMap orthogonalFamily.{u, v} lm.1 lm.2) ≤ WInteger
    exact (MorphismProperty.ofHoms_le_iff _ WInteger).mpr
      (fun lm => @originalGenerator_integerPiStar_of_stabilization.{u, v} B lm.1 lm.2 (hSeeds lm.1))

section CoproductCofans

variable {J : Type w} [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]

omit B in
/-- The two actual colimit cofans retain all original endpoint and input-map equations as an Arrow iso. -/
def originalCoproductIntegerArrowIso
    (D₁ D₂ : Discrete J ⥤ C.{u, v}) (c : Cocone D₁) (hc : IsColimit c)
    (d : Cocone D₂) (hd : IsColimit d) (f : D₁ ⟶ D₂) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = f.app j ≫ d.ι.app j) :
    Arrow.mk (Limits.Sigma.map (fun j => f.app (Discrete.mk j))) ≅ Arrow.mk p := by
  refine Arrow.isoMk
    ((Sigma.isoColimit D₁) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit D₁) hc)
    ((Sigma.isoColimit D₂) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit D₂) hd) ?_
  apply Limits.Sigma.hom_ext
  intro j
  simp [hp, Category.assoc]

variable [HasProductsOfShape J PointedCGWH.{u, v}]

/-- All integer tests pass to the caller's full cofan map with its actual original inclusions. -/
theorem originalCofans_integerPiStar
    (D₁ D₂ : Discrete J ⥤ C.{u, v}) (c : Cocone D₁) (hc : IsColimit c)
    (d : Cocone D₂) (hd : IsColimit d) (f : D₁ ⟶ D₂) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = f.app j ≫ d.ι.app j)
    (hX : ∀ j a, IsCofibrant ((D₁.obj (Discrete.mk j)).toEnrichedFunctor.obj a))
    (hY : ∀ j a, IsCofibrant ((D₂.obj (Discrete.mk j)).toEnrichedFunctor.obj a))
    (hf : ∀ j, OrthogonalIntegerHomotopy.integerPiStarEquivalences (f.app (Discrete.mk j))) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences p :=
  (WInteger.arrow_mk_iso_iff (originalCoproductIntegerArrowIso D₁ D₂ c hc d hd f p hp)).mp
    (sigmaMap_integerPiStar_of_componentCofibrant (fun j => f.app (Discrete.mk j)) hX hY hf)

end CoproductCofans

section OriginalKAssembly

open scoped CGWH.limits

variable {J : Type w} [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]
  [HasProductsOfShape J PointedCGWH.{u, v}]

/-- Every original K-family cofan map is integer weak from the actual stabilization seeds. -/
theorem originalKCofans_integerPiStar_of_stabilizationSeeds
    (D₁ D₂ : Discrete J ⥤ C.{u, v}) (c : Cocone D₁) (hc : IsColimit c)
    (d : Cocone D₂) (hd : IsColimit d) (f : D₁ ⟶ D₂) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = f.app j ≫ d.ι.app j)
    (hf : ∀ j, NativeStableModels.originalK (f.app (Discrete.mk j)))
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences p := by
  apply originalCofans_integerPiStar (B := B) D₁ D₂ c hc d hd f p hp
  · intro j a
    let _ : IsCofibrant (D₁.obj (Discrete.mk j)) :=
      (NativeK.generatorEndpoints (B := B) orthogonalFamily.{u, v} _ (hf j)).1
    exact NativeCofibrantComponents.component_isCofibrant (B := B)
      NativeStable.orthogonalHom_isCofibrant _ a
  · intro j a
    let _ : IsCofibrant (D₂.obj (Discrete.mk j)) :=
      (NativeK.generatorEndpoints (B := B) orthogonalFamily.{u, v} _ (hf j)).2
    exact NativeCofibrantComponents.component_isCofibrant (B := B)
      NativeStable.orthogonalHom_isCofibrant _ a
  · intro j
    exact originalK_generators_integerPiStar_of_stabilizationSeeds (B := B) hSeeds _ (hf j)

omit [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]
  [HasProductsOfShape J PointedCGWH.{u, v}] in
/-- Every full original K coproduct, with its actual cofan maps, lies in HEP and the integer class. -/
theorem originalK_coproducts_le_HEPInteger_of_stabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    MorphismProperty.coproducts.{v} NativeStableModels.originalK.{u, v} ≤ HEPInteger.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  intro X Y p hp
  have hCof : cofibrations C.{u, v} p :=
    NativeK.left_le_cofibrations (B := B) orthogonalFamily.{u, v} p
      (NativeStableModels.originalK.coproducts_le_llp_rlp p hp)
  have hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property p := by
    rw [HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq] at hCof
    exact OriginalContinuousSourceApproximation.originalNativeILeft_le_HEP _ hCof
  refine ⟨hHEP, ?_⟩
  rw [MorphismProperty.coproducts_iff] at hp
  obtain ⟨J', hp⟩ := hp
  cases hp with
  | mk D₁ D₂ c d hc hd f hf =>
    apply originalKCofans_integerPiStar_of_stabilizationSeeds (B := B)
      D₁ D₂ c hc d hd f _ _ (fun j => hf (Discrete.mk j)) hSeeds
    intro j
    exact hc.fac (Cocone.mk d.pt (f ≫ d.ι)) j

omit [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]
  [HasProductsOfShape J PointedCGWH.{u, v}] in
/-- Actual original K-cell coproducts, pushouts, ordinal witnesses and retracts preserve all integers. -/
theorem originalKLeft_integerPiStar_of_stabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) :
    NativeStableModels.originalK.{u, v}.rlp.llp ≤ OrthogonalIntegerHomotopy.integerPiStarEquivalences := by
  have hCop := originalK_coproducts_le_HEPInteger_of_stabilizationSeeds (B := B) hSeeds
  have hPush : (MorphismProperty.coproducts.{v} NativeStableModels.originalK.{u, v}).pushouts ≤
      HEPInteger.{u, v} := by
    rintro X Y p ⟨A, D, i, z, kD, hi, sq⟩
    exact MorphismProperty.of_isPushout sq (hCop i hi)
  intro X Y f hf
  rw [NativeStableModels.originalKLeft_eq_retractCells] at hf
  obtain ⟨Z, T, g, d, hg⟩ := hf
  obtain ⟨c⟩ := hg
  have hCell : HEPInteger.{u, v} g :=
    MorphismProperty.transfiniteCompositionsOfShape_le HEPInteger
      realizedGeneratorCardinal.{v}.ord.ToType g (c.ofLE hPush).mem
  exact WInteger.of_retract d hCell.2

omit [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]
  [HasProductsOfShape J PointedCGWH.{u, v}] in
/-- The literal original K unit is integer weak by its own original cell algorithm and stabilization seeds. -/
theorem originalKUnit_integerPiStar_of_stabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) (X : C.{u, v}) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences (η.app X) :=
  originalKLeft_integerPiStar_of_stabilizationSeeds (B := B) hSeeds _
    (NativeK.omegaReplacementUnit_mem_left (B := B) orthogonalFamily.{u, v} X)

end OriginalKAssembly

section OriginalScalarSphereRecognition

open MonoidalCategory CategoryTheory.MonoidalCategory.TensorPower

omit B in
private def originalScalarCoefficientArrowIso
    {M N : PointedCGWH.{u, v}} (e : M ≅ N) {X Y : C.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((EnrichedFunctorCat.tensorLeft M).map f) ≅
      Arrow.mk ((EnrichedFunctorCat.tensorLeft N).map f) := by
  let t := (EnrichedFunctorCat.ScalarLeibniz.tensorBifunctor (A := O.{u, v})).mapIso e
  exact Arrow.isoMk (t.app X) (t.app Y) (t.hom.naturality f).symm

omit B in
/-- The actual one-sphere scalar preserves and reflects every original integer map on arbitrary endpoints. -/
theorem sphereOneTensor_integerPiStar_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
        ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne.{u, v}).map f) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences f := by
  let e := originalRestrictionScalarNatIso sequentialOrthogonalOperatorIndexFunctor
    PointedCGWH.sphereOne.{u, v}
  let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne.{u, v}).map (U.map f)) ≅
      Arrow.mk (U.map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne.{u, v}).map f)) :=
    Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
  let W := PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
  let _ : W.RespectsIso := by
    unfold W
      PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry.integerPiStarEquivalences
    infer_instance
  rw [OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying,
    OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff_underlying]
  exact (W.arrow_mk_iso_iff a).symm.trans
    (PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry.suspension_integerPiStarEquivalences_iff
      (U.map f))

omit B in
private theorem originalSpherePowerTensor_integerPiStar_iff
    (n : ℕ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
        ((EnrichedFunctorCat.tensorLeft (tensorPowObj PointedCGWH.sphereOne.{u, v} n)).map f) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences f := by
  induction n generalizing X Y with
  | zero =>
    let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft (𝟙_ PointedCGWH.{u, v})).map f) ≅ Arrow.mk f :=
      Arrow.isoMk (scalarUnitIso X) (scalarUnitIso Y) (scalarUnitIso_naturality f).symm
    exact WInteger.arrow_mk_iso_iff a
  | succ n ih =>
    let M := tensorPowObj PointedCGWH.sphereOne.{u, v} n
    let N := PointedCGWH.sphereOne.{u, v}
    let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft (M ⊗ N)).map f) ≅
        Arrow.mk ((EnrichedFunctorCat.tensorLeft M).map ((EnrichedFunctorCat.tensorLeft N).map f)) :=
      Arrow.isoMk (scalarAssociatorIso M N X) (scalarAssociatorIso M N Y)
        (scalarAssociatorIso_naturality M N f).symm
    exact (WInteger.arrow_mk_iso_iff a).trans
      ((ih ((EnrichedFunctorCat.tensorLeft N).map f)).trans (sphereOneTensor_integerPiStar_iff f))

omit B in
/-- Every original representation sphere scalar preserves and reflects the full unrestricted integer class. -/
theorem orthogonalSphereTensor_integerPiStar_iff
    (n : ℕ) {X Y : C.{u, v}} (f : X ⟶ Y) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
        ((EnrichedFunctorCat.tensorLeft (PointedCGWH.orthogonalSphere.{u, v} n)).map f) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences f :=
  (WInteger.arrow_mk_iso_iff
    (originalScalarCoefficientArrowIso (CategoryTheory.Spectra.originalSpherePowerComparisonIso.{u, v} n) f)).symm.trans
      (originalSpherePowerTensor_integerPiStar_iff n f)

end OriginalScalarSphereRecognition

section OriginalIntegerUnitIsomorphisms

/-- The entire original K-unit group family is an actual NatIso from the original stabilization seeds. -/
def originalKUnitIntegerNatIsoOfStabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) (q : ℤ) : P q ≅ R ⋙ P q := by
  let _ : ∀ X : C.{u, v}, IsIso ((P q).map (η.app X)) := fun X =>
    (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff _).mp
      (originalKUnit_integerPiStar_of_stabilizationSeeds (B := B) hSeeds X) q
  exact NatIso.ofComponents (fun X => asIso ((P q).map (η.app X)))
    (fun f => rUnit_integerPi_naturality q f)

/-- Both original unit endpoints retain the whole original arrow and its actual original K image. -/
def originalKUnitIntegerArrowIsoOfStabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) (q : ℤ)
    {X Y : C.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((P q).map f) ≅ Arrow.mk ((P q).map (R.map f)) := by
  let e := originalKUnitIntegerNatIsoOfStabilizationSeeds (B := B) hSeeds q
  exact Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm

/-- The full original inverse-I-counit/K-unit comparison is an actual NatIso from those same seeds. -/
def integerReplacementComparisonIsoOfStabilizationSeeds
    (hSeeds : ∀ l : ℕ × ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization orthogonalFamily.{u, v} l)) (q : ℤ) : P q ≅ (Q ⋙ R) ⋙ P q := by
  let e := originalKUnitIntegerNatIsoOfStabilizationSeeds (B := B) hSeeds q
  refine NatIso.ofComponents (fun X => ((qIso q).app X).symm ≪≫ e.app (Q.obj X)) ?_
  intro X Y f
  have h := integerReplacementComparison_naturality q f
  rw [integerReplacementComparison_app q X, integerReplacementComparison_app q Y] at h
  exact h

end OriginalIntegerUnitIsomorphisms

section OriginalFreeIndexTransport

universe uV vV uI vI uA
open MonoidalCategory
open scoped MonoidalClosed

namespace FreeIndexTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]
  {A : Type uA} [EnrichedCategory V A] (j : EnrichedFunctor V I A)

omit B in
/-- The actual original index isomorphism acts naturally at every enriched source diagram. -/
def evaluationIndexNatIso {a b : I} (e : a ≅ b) :
    evaluation (V := V) (j.obj a) ≅ evaluation (V := V) (j.obj b) :=
  NatIso.ofComponents
    (fun X => ((restriction j).obj X).toEnrichedFunctor.toOrdinaryFunctor.mapIso e)
    (fun q => by
      have h := (ordinaryNatTrans ((restriction j).map q)).naturality e.hom
      simpa only [ordinaryNatTrans_app, restrictionMap_component, Functor.mapIso_hom,
        evaluation_map, EnrichedFunctor.toOrdinaryFunctor_obj] using h.symm)

omit B in
/-- The original free/evaluation adjunctions transport the whole actual source index isomorphism. -/
def freeIndexIso {a b : I} (e : a ≅ b) (K : V) :
    Free.object (j.obj a) K ≅ Free.object (j.obj b) K :=
  ((Free.adjunction (j.obj a)).ofNatIsoRight (evaluationIndexNatIso j e)).leftAdjointUniq
    (Free.adjunction (j.obj b)) |>.app K

omit B in
/-- The actual free-index map is evaluated through the original unit and original inverse index map. -/
theorem freeIndexIso_evaluate {a b : I} (e : a ≅ b) (K : V) :
    Free.evaluate (j.obj a) K (Free.object (j.obj b) K) (freeIndexIso j e K).hom =
      (Free.adjunction (j.obj b)).unit.app K ≫
        (evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((Free.adjunction (j.obj a)).ofNatIsoRight (evaluationIndexNatIso j e))
    (Free.adjunction (j.obj b)) K
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Free.adjunction_homEquiv] at h
  change Free.evaluate (j.obj a) K (Free.object (j.obj b) K) (freeIndexIso j e K).hom ≫
    (evaluationIndexNatIso j e).hom.app (Free.object (j.obj b) K) = _ at h
  let t : K ⟶ (evaluation (j.obj a)).obj (Free.object (j.obj b) K) :=
    Free.evaluate (j.obj a) K (Free.object (j.obj b) K) (freeIndexIso j e K).hom
  have ht : t ≫ (evaluationIndexNatIso j e).hom.app (Free.object (j.obj b) K) =
      (Free.adjunction (j.obj b)).unit.app K := h
  change t = _
  calc
    t = t ≫ 𝟙 ((evaluation (j.obj a)).obj (Free.object (j.obj b) K)) :=
      (Category.comp_id t).symm
    _ = t ≫ ((evaluationIndexNatIso j e).hom.app (Free.object (j.obj b) K) ≫
        (evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K)) :=
      congrArg (fun z => t ≫ z)
        ((evaluationIndexNatIso j e).hom_inv_id_app (Free.object (j.obj b) K)).symm
    _ = (t ≫ (evaluationIndexNatIso j e).hom.app (Free.object (j.obj b) K)) ≫
        (evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun q => q ≫ (evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K)) ht

omit B in
/-- Every original free-source map retains the complete index transport and its actual target action. -/
theorem freeIndexIso_precompose_evaluate {a b : I} (e : a ≅ b) (K : V)
    (X : EnrichedFunctorCat V A) (f : Free.object (j.obj b) K ⟶ X) :
    Free.evaluate (j.obj a) K X ((freeIndexIso j e K).hom ≫ f) =
      Free.evaluate (j.obj b) K X f ≫ (evaluationIndexNatIso j e).inv.app X := by
  have hPost := Free.evaluate_postcomp (j.obj a) K (freeIndexIso j e K).hom f
  have hIndex := freeIndexIso_evaluate j e K
  have hNaturality := (evaluationIndexNatIso j e).inv.naturality f
  have hUnit := (Free.adjunction (j.obj b)).homEquiv_unit (f := f)
  rw [Free.adjunction_homEquiv] at hUnit
  change Free.evaluate (j.obj b) K X f =
    (Free.adjunction (j.obj b)).unit.app K ≫ (evaluation (j.obj b)).map f at hUnit
  calc
    _ = Free.evaluate (j.obj a) K (Free.object (j.obj b) K) (freeIndexIso j e K).hom ≫
        (evaluation (j.obj a)).map f := hPost
    _ = ((Free.adjunction (j.obj b)).unit.app K ≫
        (evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K)) ≫
        (evaluation (j.obj a)).map f :=
      congrArg (fun z => z ≫ (evaluation (j.obj a)).map f) hIndex
    _ = (Free.adjunction (j.obj b)).unit.app K ≫
        ((evaluationIndexNatIso j e).inv.app (Free.object (j.obj b) K) ≫
          (evaluation (j.obj a)).map f) := Category.assoc _ _ _
    _ = (Free.adjunction (j.obj b)).unit.app K ≫
        ((evaluation (j.obj b)).map f ≫ (evaluationIndexNatIso j e).inv.app X) :=
      congrArg (fun z => (Free.adjunction (j.obj b)).unit.app K ≫ z) hNaturality.symm
    _ = ((Free.adjunction (j.obj b)).unit.app K ≫ (evaluation (j.obj b)).map f) ≫
        (evaluationIndexNatIso j e).inv.app X := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ (evaluationIndexNatIso j e).inv.app X) hUnit.symm


end FreeIndexTransport

end OriginalFreeIndexTransport

section OriginalScalarGammaFactorization

open MonoidalCategory BraidedCategory CategoryTheory.Spectra
open CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed

namespace ScalarGammaFactorization

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  OrthogonalIndex.enrichedCategory MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

omit B in
private theorem nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  infer_instance

attribute [local instance] nativeColimits

omit B in
/-- The actual coefficient uses the original ambient right index unitor. -/
def originalUnitSourceCoefficient (n : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ⟶
      (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
        OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
  coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} (0 : OrthogonalIndex) n n (ρ_ n).hom

omit B in
/-- The full regular unit-source Gamma keeps that entire original coefficient. -/
def originalUnitSourceStabilization (n : ℕ) :
    Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) ⟶
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v}) :=
  CurrentFree.stabilization (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)
    (originalUnitSourceCoefficient n)

omit B in
/-- Every literal original stabilization label keeps both scalar/free maps and original sphere product. -/
theorem originalScalarGammaTriangle (n k : ℕ) :
    (EnrichedFunctorCat.tensorLeft (PointedCGWH.orthogonalSphere.{u, v} n)).map
        (NativeK.stabilization Actual.orthogonalFamily.{u, v} (n, k)) ≫
      (Free.scalarFreeIso (PointedCGWH.orthogonalSphere.{u, v} n) (𝟙_ PointedCGWH.{u, v})
        (OrthogonalOperatorIndex.ofIndex.{u, v} n)).hom ≫
      Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
      originalUnitSourceStabilization.{u, v} n =
    (Free.scalarFreeIso (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} k)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))).hom ≫
      Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n k).inv ≫
      originalUnitSourceStabilization.{u, v} (n + k) := by
  have hNu : OrthogonalOperatorIndex.nu.{u, v} n k =
      coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n (n + k) k (β_ k n).hom := rfl
  have hComp : (originalUnitSourceCoefficient.{u, v} n ⊗ₘ
      OrthogonalOperatorIndex.nu.{u, v} n k) ≫
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
        (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k)) =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n k).inv ≫
        originalUnitSourceCoefficient.{u, v} (n + k) := by
    unfold originalUnitSourceCoefficient
    rw [hNu, OrthogonalOperatorIndex.comp_eq]
    exact coefficientUnit_comp OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
      orthogonalSphereBraidedData.{u, v} n k
  have h := CurrentFree.scalarStabilization_comp_coefficient (V := PointedCGWH.{u, v})
    (A := OrthogonalOperatorIndex.{u, v}) (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))
    (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} k)
    (PointedCGWH.orthogonalSphere.{u, v} (n + k))
    (originalUnitSourceCoefficient.{u, v} n) (OrthogonalOperatorIndex.nu.{u, v} n k)
    (originalUnitSourceCoefficient.{u, v} (n + k))
    (PointedCGWH.orthogonalSphereTensorIso.{u, v} n k).inv hComp
  simpa only [originalUnitSourceStabilization, NativeK.stabilization,
    Actual.orthogonalFamily, Category.assoc, EnrichedFunctorCat.tensorLeft] using h


end ScalarGammaFactorization

end OriginalScalarGammaFactorization

section OriginalFreeUnitAction

universe uV vV
open MonoidalCategory
open scoped MonoidalClosed
set_option backward.isDefEq.respectTransparency.types false
namespace FreeUnitAction


variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {K H G J : V}

omit B in
/-- The exact original free-unit evaluation word is the original coefficient Hom composition. -/
theorem freeUnitTargetCoefficient (D : K ⟶ H) (p : (𝟙_ V) ⟶ G) (c : H ⊗ G ⟶ J) :
    D ≫ (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫ ((𝟙_ V) ⊗ H) ◁ p ≫
        (α_ (𝟙_ V) H G).hom ≫ (𝟙_ V) ◁ c =
      (ρ_ K).inv ≫ (D ⊗ₘ p) ≫ c ≫ (λ_ J).inv := by
  have hn : (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv =
      (ρ_ H).inv ≫ ((λ_ H).inv ▷ (𝟙_ V)) :=
    rightUnitor_inv_naturality (λ_ H).inv
  have he : ((λ_ H).inv ▷ (𝟙_ V)) ≫ ((𝟙_ V) ⊗ H) ◁ p =
      H ◁ p ≫ ((λ_ H).inv ▷ G) := (whisker_exchange (λ_ H).inv p).symm
  have hp : ((λ_ H).inv ▷ G) ≫ (α_ (𝟙_ V) H G).hom ≫ (λ_ (H ⊗ G)).hom =
      𝟙 (H ⊗ G) := by monoidal
  have hd : D ≫ (ρ_ H).inv = (ρ_ K).inv ≫ (D ▷ (𝟙_ V)) :=
    rightUnitor_inv_naturality D
  apply (cancel_mono (λ_ J).hom).mp
  calc
    _ = D ≫ (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫ ((𝟙_ V) ⊗ H) ◁ p ≫
        (α_ (𝟙_ V) H G).hom ≫ (λ_ (H ⊗ G)).hom ≫ c := by
      simpa only [Category.assoc] using congrArg
        (fun z => D ≫ (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫
          ((𝟙_ V) ⊗ H) ◁ p ≫ (α_ (𝟙_ V) H G).hom ≫ z) (leftUnitor_naturality c)
    _ = D ≫ (ρ_ H).inv ≫ ((λ_ H).inv ▷ (𝟙_ V)) ≫ ((𝟙_ V) ⊗ H) ◁ p ≫
        (α_ (𝟙_ V) H G).hom ≫ (λ_ (H ⊗ G)).hom ≫ c := by
      simpa only [Category.assoc] using congrArg
        (fun z => D ≫ z ≫ ((𝟙_ V) ⊗ H) ◁ p ≫ (α_ (𝟙_ V) H G).hom ≫
          (λ_ (H ⊗ G)).hom ≫ c) hn
    _ = D ≫ (ρ_ H).inv ≫ H ◁ p ≫ ((λ_ H).inv ▷ G) ≫
        (α_ (𝟙_ V) H G).hom ≫ (λ_ (H ⊗ G)).hom ≫ c := by
      simpa only [Category.assoc] using congrArg
        (fun z => D ≫ (ρ_ H).inv ≫ z ≫ (α_ (𝟙_ V) H G).hom ≫
          (λ_ (H ⊗ G)).hom ≫ c) he
    _ = D ≫ (ρ_ H).inv ≫ H ◁ p ≫ c := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun z => D ≫ (ρ_ H).inv ≫ H ◁ p ≫ z ≫ c) hp
    _ = (ρ_ K).inv ≫ (D ▷ (𝟙_ V)) ≫ H ◁ p ≫ c := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ H ◁ p ≫ c) hd
    _ = (ρ_ K).inv ≫ (D ⊗ₘ p) ≫ c := by simp only [tensorHom_def, Category.assoc]
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

universe uI vI uA

variable [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]
  {A : Type uA} [EnrichedCategory V A]

open CategoryTheory.EnrichedFunctorCat

omit B in
/-- The entire original index action on the free unit keeps its complete enriched Hom point. -/
theorem freeUnitIndexMap (j : EnrichedFunctor V I A) (a : A) {b c : I} (g : b ⟶ c) :
    ((restriction j).obj (Free.object a (𝟙_ V))).toEnrichedFunctor.toOrdinaryFunctor.map g =
      (ρ_ ((𝟙_ V) ⊗ (a ⟶[V] j.obj b))).inv ≫
        ((𝟙_ V) ⊗ (a ⟶[V] j.obj b)) ◁ (eHomEquiv V g ≫ j.map b c) ≫
        (α_ (𝟙_ V) (a ⟶[V] j.obj b) (j.obj b ⟶[V] j.obj c)).hom ≫
        (𝟙_ V) ◁ eComp V a (j.obj b) (j.obj c) := by
  change (eHomEquiv V).symm
    (eHomEquiv V g ≫ j.map b c ≫ (Free.object a (𝟙_ V)).toEnrichedFunctor.map (j.obj b) (j.obj c)) = _
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  dsimp only [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  simp only [Free.action, whiskerLeft_comp, Category.assoc]

omit B in
/-- An original free-unit evaluation followed by the original index action is actual coefficient composition. -/
theorem freeUnitCoefficientIndexTransport (j : EnrichedFunctor V I A) (a : A)
    {b c : I} (g : b ⟶ c) (K : V) (D : K ⟶ (a ⟶[V] j.obj b)) :
    D ≫ (λ_ (a ⟶[V] j.obj b)).inv ≫
        ((restriction j).obj (Free.object a (𝟙_ V))).toEnrichedFunctor.toOrdinaryFunctor.map g =
      ((ρ_ K).inv ≫ (D ⊗ₘ (eHomEquiv V g ≫ j.map b c)) ≫ eComp V a (j.obj b) (j.obj c)) ≫
        (λ_ (a ⟶[V] j.obj c)).inv := by
  rw [freeUnitIndexMap]
  simpa only [Category.assoc] using
    freeUnitTargetCoefficient D (eHomEquiv V g ≫ j.map b c) (eComp V a (j.obj b) (j.obj c))


end FreeUnitAction

end OriginalFreeUnitAction


section OriginalUnitGammaSource

open MonoidalCategory BraidedCategory CategoryTheory.Spectra
open CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed
set_option backward.isDefEq.respectTransparency.types false
namespace UnitGammaSource


attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  OrthogonalIndex.enrichedCategory MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

omit B in
private instance nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  infer_instance

private abbrev O := OrthogonalOperatorIndex.{u, v}
private abbrev j : EnrichedFunctor PointedCGWH.{u, v} OrthogonalIndex O.{u, v} :=
  indexUnitFunctor OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

omit B in
private theorem j_obj (b : OrthogonalIndex) :
    j.{u, v}.obj b = OrthogonalOperatorIndex.ofIndex.{u, v} b := rfl

omit B in
private theorem unitTensor_index (n : OrthogonalIndex) :
    (𝟙_ OrthogonalIndex) ⊗ n = 0 + n := rfl

omit B in
private theorem j_map (b c : OrthogonalIndex) :
    j.{u, v}.map b c = indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} b c := rfl

private abbrev freeZero :=
  Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v})

private def leftUnitIndexIso (n : ℕ) : (0 + n : OrthogonalIndex) ≅ (n : OrthogonalIndex) :=
  λ_ (n : OrthogonalIndex)

omit B in
/-- The complete original free-zero target index action uses the actual index left unitor. -/
def unitTargetIndexMap (n : ℕ) :
    freeZero.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n)) ⟶
      freeZero.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
  ((restriction j.{u, v}).obj freeZero.{u, v}).toEnrichedFunctor.toOrdinaryFunctor.map
    (λ_ (n : OrthogonalIndex)).hom

omit B in
/-- The actual original index left unitor transports the full original free source. -/
def unitSourceFreeIso (n : ℕ) :
    Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n) ≅
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
        (PointedCGWH.orthogonalSphere.{u, v} n) :=
  FreeIndexTransport.freeIndexIso (V := PointedCGWH.{u, v})
    (I := OrthogonalIndex) (A := O.{u, v}) (a := n) (b := 0 + n) j.{u, v} (leftUnitIndexIso n).symm
    (PointedCGWH.orthogonalSphere.{u, v} n)

omit B in
private theorem evaluationIndex_inverse_original (n : ℕ) :
    (FreeIndexTransport.evaluationIndexNatIso (a := n) (b := 0 + n)
      j.{u, v} (leftUnitIndexIso n).symm).inv.app
        freeZero.{u, v} = unitTargetIndexMap.{u, v} n := rfl

omit B in
/-- The original zero-source coefficient followed by the actual left index unitor is the regular coefficient. -/
theorem unitSourceCoefficient_transport (n : ℕ) :
    (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
        (OrthogonalOperatorIndex.nu.{u, v} 0 n ⊗ₘ
          (eHomEquiv PointedCGWH.{u, v} (λ_ (n : OrthogonalIndex)).hom ≫
            j.{u, v}.map (0 + n) n)) ≫
        eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
          (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
          (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      ScalarGammaFactorization.originalUnitSourceCoefficient.{u, v} n := by
  have hNu : OrthogonalOperatorIndex.nu.{u, v} 0 n =
      coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} 0 (0 + n) n
        (β_ (n : OrthogonalIndex) (0 : OrthogonalIndex)).hom := rfl
  have h := coefficientHom_postcompose OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    (0 : OrthogonalIndex) (0 + n) n n (β_ (n : OrthogonalIndex) (0 : OrthogonalIndex)).hom
    (λ_ (n : OrthogonalIndex)).hom
  have hb : (β_ (n : OrthogonalIndex) (0 : OrthogonalIndex)).hom ≫
      (λ_ (n : OrthogonalIndex)).hom = (ρ_ (n : OrthogonalIndex)).hom := by
    change (β_ (n : OrthogonalIndex) (𝟙_ OrthogonalIndex)).hom ≫
      (λ_ (n : OrthogonalIndex)).hom = _
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hb] at h
  rw [j_map, hNu, OrthogonalOperatorIndex.comp_eq]
  unfold ScalarGammaFactorization.originalUnitSourceCoefficient
  simp only [orthogonalSphereFunctor_obj] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
omit B in
/-- The actual ordinary index action on the entire original free-zero unit reads the regular coefficient. -/
theorem unitSource_stabilization_evaluate_transport (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
        (PointedCGWH.orthogonalSphere.{u, v} n)
        (Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v}))
        (Actual.orthogonalStabilization.{u, v} 0 n) ≫
        unitTargetIndexMap.{u, v} n =
      ScalarGammaFactorization.originalUnitSourceCoefficient.{u, v} n ≫
        (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
          OrthogonalOperatorIndex.ofIndex.{u, v} n)).inv := by
  have hEval : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      (Actual.orthogonalStabilization.{u, v} 0 n) = OrthogonalOperatorIndex.nu.{u, v} 0 n ≫
      (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
        OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))).inv :=
    CurrentFree.stabilization_evaluate (V := PointedCGWH.{u, v}) (A := O.{u, v})
    (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
    (PointedCGWH.orthogonalSphere.{u, v} n) (OrthogonalOperatorIndex.nu.{u, v} 0 n)
  have hTransport := FreeUnitAction.freeUnitCoefficientIndexTransport j.{u, v}
    (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (λ_ (n : OrthogonalIndex)).hom
    (PointedCGWH.orthogonalSphere.{u, v} n) (OrthogonalOperatorIndex.nu.{u, v} 0 n)
  simp only [EnrichedFunctor.toOrdinaryFunctor_obj, j_obj, unitTensor_index] at hTransport
  change OrthogonalOperatorIndex.nu.{u, v} 0 n ≫
    (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
      OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))).inv ≫
      unitTargetIndexMap.{u, v} n =
    ((ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
      (OrthogonalOperatorIndex.nu.{u, v} 0 n ⊗ₘ
        (eHomEquiv PointedCGWH.{u, v} (λ_ (n : OrthogonalIndex)).hom ≫ j.{u, v}.map (0 + n) n)) ≫
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n)) (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫
      (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
        OrthogonalOperatorIndex.ofIndex.{u, v} n)).inv at hTransport
  rw [unitSourceCoefficient_transport] at hTransport
  calc
    _ = (OrthogonalOperatorIndex.nu.{u, v} 0 n ≫
        (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
          OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))).inv) ≫ unitTargetIndexMap.{u, v} n :=
      congrArg (fun z : PointedCGWH.orthogonalSphere.{u, v} n ⟶
        freeZero.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n)) =>
          z ≫ unitTargetIndexMap.{u, v} n) hEval
    _ = OrthogonalOperatorIndex.nu.{u, v} 0 n ≫
        (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
          OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))).inv ≫ unitTargetIndexMap.{u, v} n :=
      Category.assoc _ _ _
    _ = _ := hTransport

set_option backward.isDefEq.respectTransparency true in
omit B in
/-- The full original free-source Iso gives the actual original zero-source stabilization evaluation. -/
theorem unitSource_precompose_evaluate (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      ((unitSourceFreeIso.{u, v} n).hom ≫ Actual.orthogonalStabilization.{u, v} 0 n) =
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      (Actual.orthogonalStabilization.{u, v} 0 n) ≫ unitTargetIndexMap.{u, v} n := by
  unfold unitSourceFreeIso
  have h := FreeIndexTransport.freeIndexIso_precompose_evaluate
    (V := PointedCGWH.{u, v}) (I := OrthogonalIndex) (A := O.{u, v})
    (a := n) (b := 0 + n) j.{u, v} (leftUnitIndexIso n).symm
    (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
    (Actual.orthogonalStabilization.{u, v} 0 n)
  rw [evaluationIndex_inverse_original] at h
  simpa only [j_obj, EnrichedFunctorCat.evaluation_obj, Free.object_obj] using h

set_option backward.isDefEq.respectTransparency true in
omit B in
/-- Both full original source maps identify the regular coefficient stabilization with the literal original Gamma. -/
theorem unitSource_stabilization_original (n : ℕ) :
    ScalarGammaFactorization.originalUnitSourceStabilization.{u, v} n =
      (unitSourceFreeIso.{u, v} n).hom ≫ Actual.orthogonalStabilization.{u, v} 0 n := by
  apply (Free.homEquiv (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}).injective
  change Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      (ScalarGammaFactorization.originalUnitSourceStabilization.{u, v} n) =
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      ((unitSourceFreeIso.{u, v} n).hom ≫ Actual.orthogonalStabilization.{u, v} 0 n)
  have hOriginal : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) freeZero.{u, v}
      (ScalarGammaFactorization.originalUnitSourceStabilization.{u, v} n) =
      ScalarGammaFactorization.originalUnitSourceCoefficient.{u, v} n ≫
      (λ_ (OrthogonalOperatorIndex.ofIndex.{u, v} 0 ⟶[PointedCGWH.{u, v}]
        OrthogonalOperatorIndex.ofIndex.{u, v} n)).inv :=
    CurrentFree.stabilization_evaluate (V := PointedCGWH.{u, v}) (A := O.{u, v})
      (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n)
      (ScalarGammaFactorization.originalUnitSourceCoefficient.{u, v} n)
  have hPre := unitSource_precompose_evaluate.{u, v} n
  have hTransport := unitSource_stabilization_evaluate_transport.{u, v} n
  exact hOriginal.trans (hPre.trans hTransport).symm


end UnitGammaSource

end OriginalUnitGammaSource


section OriginalBareGammaSeedClosure

open MonoidalCategory CategoryTheory.Spectra
namespace BareGammaSeedClosure


private abbrev C := OrthogonalCarrier.{u, v}
private abbrev W := OrthogonalIntegerHomotopy.integerPiStarEquivalences.{u, v}
private abbrev P (q : ℤ) := OrthogonalIntegerHomotopy.integerPiFunctor.{u, v} q

omit B in
private instance intIdentities : W.{u, v}.ContainsIdentities := by
  unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
  let _ := integerPiStarEquivalences_containsIdentities.{u, v}
  infer_instance

omit B in
private instance intTwoOfThree : W.{u, v}.HasTwoOutOfThreeProperty := by
  unfold W OrthogonalIntegerHomotopy.integerPiStarEquivalences
  let _ := integerPiStarEquivalences_hasTwoOutOfThreeProperty.{u, v}
  infer_instance

omit B in
private theorem integer_isoHom {X Y : C.{u, v}} (e : X ≅ Y) : W e.hom := by
  apply (OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff _).mpr
  intro q
  infer_instance

omit B in
/-- The literal bare Gamma seeds give the regular Gamma through the actual original source Iso. -/
theorem originalUnitSourceStabilization_integerPiStar_of_bareGammaSeeds
    (hGamma : ∀ n : ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (Actual.orthogonalStabilization.{u, v} 0 n)) (n : ℕ) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (ScalarGammaFactorization.originalUnitSourceStabilization.{u, v} n) := by
  rw [UnitGammaSource.unitSource_stabilization_original]
  exact W.comp_mem _ _ (integer_isoHom (UnitGammaSource.unitSourceFreeIso.{u, v} n)) (hGamma n)

omit B in
/-- The bare original Gamma seeds give every literal original stabilization label by the actual scalar triangle. -/
theorem originalStabilizations_integerPiStar_of_bareGammaSeeds
    (hGamma : ∀ n : ℕ, OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (Actual.orthogonalStabilization.{u, v} 0 n)) (l : ℕ × ℕ) :
    OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (NativeK.stabilization Actual.orthogonalFamily.{u, v} l) := by
  rcases l with ⟨n, k⟩
  have hn := originalUnitSourceStabilization_integerPiStar_of_bareGammaSeeds hGamma n
  have hnk := originalUnitSourceStabilization_integerPiStar_of_bareGammaSeeds hGamma (n + k)
  have hUnitCoeff : W (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom) := by
    exact integer_isoHom ((Free.functor (V := PointedCGWH.{u, v})
      (A := OrthogonalOperatorIndex.{u, v}) (OrthogonalOperatorIndex.ofIndex.{u, v} n)).mapIso
        (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)))
  have hSphereCoeff : W (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n k).inv) := by
    exact integer_isoHom ((Free.functor (V := PointedCGWH.{u, v})
      (A := OrthogonalOperatorIndex.{u, v}) (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))).mapIso
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n k).symm)
  have hTail := W.comp_mem _ _
    (integer_isoHom (Free.scalarFreeIso (PointedCGWH.orthogonalSphere.{u, v} n)
      (𝟙_ PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
    (W.comp_mem _ _ hUnitCoeff hn)
  have hRight := W.comp_mem _ _
    (integer_isoHom (Free.scalarFreeIso (PointedCGWH.orthogonalSphere.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} (n + k))))
    (W.comp_mem _ _ hSphereCoeff hnk)
  have hFac := ScalarGammaFactorization.originalScalarGammaTriangle.{u, v} n k
  have hScalar := W.of_postcomp _ _ hTail (hFac.symm ▸ hRight)
  exact (orthogonalSphereTensor_integerPiStar_iff n _).mp hScalar


end BareGammaSeedClosure

end OriginalBareGammaSeedClosure

end OriginalKIntegerCells

end PointedCGWH.Spectra.Orthogonal.OriginalIntegerCharacterization
