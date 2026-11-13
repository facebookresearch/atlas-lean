/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveUnitComponentOrbit
import Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting












namespace StatMech.FrontierD

noncomputable section

local instance positiveUnitComponentResidualRoutingDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p



structure SixVertexPositiveUnitComponentResidualWitness
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) where
  k : Nat
  base : SixVertexPositiveUnitComponentOrbitBase T middle k
  positive : BooleanLayer
    (SixVertexDisagreementComponent base.first base.second) (k + 1)
  source_eq : base.source positive hmiddle_pos hmiddle_lt =
    (sixVertexHorizontalActualDeficitConfigurationPair source).1


def sixVertexPositiveUnitComponentResidualSource
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  Nonempty (SixVertexPositiveUnitComponentResidualWitness source)



theorem SixVertexPositiveUnitComponentResidualWitness.degreeTwo
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade}
    (witness : SixVertexPositiveUnitComponentResidualWitness source) :
    SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1 := by
  rw [← witness.source_eq]
  exact witness.base.source_degreeTwo witness.positive
    hmiddle_pos hmiddle_lt



abbrev SixVertexPositiveUnitComponentResidualSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade //
    sixVertexPositiveUnitComponentResidualSource source ∧
      ¬ sixVertexHorizontalDegreeTwoHighCharge source}



abbrev SixVertexPositiveUnitComponentResidualGeometricSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade //
    ¬ sixVertexPositiveUnitComponentResidualSource source ∧
      ¬ sixVertexHorizontalDegreeTwoHighCharge source}






inductive SixVertexPositiveUnitComponentResidualGeometricSourceKind
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) : Type
  | nonDegreeTwo
      (notDegreeTwo : ¬ SixVertexLocallyDegreeTwo
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
  | nonNormalizedUnitCharge
      (degreeTwo : SixVertexLocallyDegreeTwo
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
      (unitCharge : sixVertexHorizontalDegreeTwoUnitCharge source.1)





noncomputable def
    sixVertexPositiveUnitComponentResidualGeometricSourceKind
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualGeometricSourceKind source := by
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source.1
  by_cases hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1
  · exact .nonNormalizedUnitCharge hdegree
      (sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge source.1
        hdegree source.2.2)
  · exact .nonDegreeTwo hdegree



noncomputable def sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :
    SixVertexHorizontalDegreeTwoHallSource T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexConfigurationPhysicalSource T middle
        hmiddle_pos hmiddle_lt where
  toFun source :=
    (sixVertexHorizontalActualDeficitConfigurationPair source).1
  inj' := by
    intro first second heq
    apply sixVertexHorizontalActualDeficitConfigurationPair_injective
    apply Subtype.ext
    exact heq


noncomputable def sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexConfigurationPhysicalTarget T middle where
  toFun target :=
    (sixVertexHorizontalActualSurplusConfigurationPair target).1
  inj' := by
    intro first second heq
    apply sixVertexHorizontalActualSurplusConfigurationPair_injective
    apply Subtype.ext
    exact heq




structure SixVertexPositiveUnitComponentResidualOrbitCover
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  physical : SixVertexPositiveUnitComponentOrbitCover T middle
    hmiddle_pos hmiddle_lt
    (SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
  sourcePhysical : ∀ source,
    physical.sourcePhysical source =
      sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade source.1
  targetLift : (Σ index, (physical.data index).TargetLayer) ↪
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  targetLift_physical : ∀ index target,
    sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade
        (targetLift ⟨index, target⟩) =
      physical.targetEmbedding ⟨index, target⟩



def SixVertexPositiveUnitComponentResidualTargetCoverage
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (physical : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt
      (SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade)) : Prop :=
  ∀ index target, ∃ lifted : SixVertexHorizontalDegreeTwoHallTarget
      T middle hmiddle_pos hmiddle_lt grade,
    sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade lifted =
      physical.targetEmbedding ⟨index, target⟩



theorem positiveUnitComponentResidualTargetLift_nonempty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (physical : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt
      (SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade))
    (hcoverage :
      SixVertexPositiveUnitComponentResidualTargetCoverage physical) :
    Nonempty
      {lift : (Σ index, (physical.data index).TargetLayer) ↪
          SixVertexHorizontalDegreeTwoHallTarget T middle
            hmiddle_pos hmiddle_lt grade //
        ∀ index target,
          sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
              T middle hmiddle_pos hmiddle_lt grade
              (lift ⟨index, target⟩) =
            physical.targetEmbedding ⟨index, target⟩} := by
  choose lift hlift using hcoverage
  let embedding : (Σ index, (physical.data index).TargetLayer) ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade :=
    { toFun := fun target => lift target.1 target.2
      inj' := by
        intro first second heq
        apply physical.targetEmbedding.injective
        rw [← hlift first.1 first.2, ← hlift second.1 second.2]
        exact congrArg
          (sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
            T middle hmiddle_pos hmiddle_lt grade) heq }
  exact ⟨⟨embedding, hlift⟩⟩



noncomputable def SixVertexPositiveUnitComponentResidualOrbitCover.ofTargetCoverage
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (physical : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt
      (SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade))
    (sourcePhysical : ∀ source,
      physical.sourcePhysical source =
        sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
          T middle hmiddle_pos hmiddle_lt grade source.1)
    (hcoverage :
      SixVertexPositiveUnitComponentResidualTargetCoverage physical) :
    SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade := by
  let lift := Classical.choice
    (positiveUnitComponentResidualTargetLift_nonempty physical hcoverage)
  exact
    { physical := physical
      sourcePhysical := sourcePhysical
      targetLift := lift.1
      targetLift_physical := lift.2 }

namespace SixVertexPositiveUnitComponentResidualOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


noncomputable def targetCoordinate
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade ↪
      Σ index, (cover.physical.data index).TargetLayer :=
  cover.physical.sourceCover.toEmbedding |>.trans
    ({
      toFun := fun source =>
        ⟨source.1,
          cover.physical.toAtlas.localMatching source.1 source.2⟩
      inj' := by
        rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ heq
        have hindex : firstIndex = secondIndex := congrArg Sigma.fst heq
        subst secondIndex
        have hfiber :
            cover.physical.toAtlas.localMatching firstIndex first =
              cover.physical.toAtlas.localMatching firstIndex second :=
          eq_of_heq (Sigma.mk.inj heq).2
        have hsource :=
          (cover.physical.toAtlas.localMatching firstIndex).injective hfiber
        cases hsource
        rfl } :
      (Σ index, (cover.physical.data index).SourceLayer) ↪
        Σ index, (cover.physical.data index).TargetLayer)


noncomputable def matching
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade :=
  cover.targetCoordinate.trans cover.targetLift



theorem matching_physical
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade (cover.matching source) =
      cover.physical.matching source := by
  let covered := cover.physical.sourceCover source
  change sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
      T middle hmiddle_pos hmiddle_lt grade
        (cover.targetLift
          ⟨covered.1,
            cover.physical.toAtlas.localMatching covered.1 covered.2⟩) =
    cover.physical.targetEmbedding
      ⟨covered.1,
        cover.physical.toAtlas.localMatching covered.1 covered.2⟩
  exact cover.targetLift_physical _ _


theorem matching_supported
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (cover.matching source) := by
  change sixVertexPairAtMostTwoCycleFineRelated
    ((sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1,
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
    ((sixVertexHorizontalActualSurplusConfigurationPair
        (cover.matching source)).1.1.1,
      (sixVertexHorizontalActualSurplusConfigurationPair
        (cover.matching source)).1.2.1)
  have hrelated := cover.physical.matching_fineRelated source
  rw [cover.sourcePhysical source] at hrelated
  rw [← cover.matching_physical source] at hrelated
  exact hrelated

end SixVertexPositiveUnitComponentResidualOrbitCover





noncomputable def sixVertexHorizontalHallSourceCanonicalLoop
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade := by
  let physical := sixVertexHorizontalActualDeficitConfigurationPair source
  let firstPairing : SixVertexCompatibleLoopPairing physical.1.1.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.1.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.1.1 physical.1.1.2.1⟩
  let secondPairing : SixVertexCompatibleLoopPairing physical.1.2.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.2.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.2.1 physical.1.2.2.1⟩
  refine ⟨⟨physical.1, firstPairing, secondPairing⟩, ?_⟩
  rw [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
  exact physical.2

@[simp] theorem sixVertexHorizontalHallSourceCanonicalLoop_pair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    (sixVertexHorizontalHallSourceCanonicalLoop source).1.1 =
      (sixVertexHorizontalActualDeficitConfigurationPair source).1 :=
  rfl


noncomputable def sixVertexHorizontalHallTargetCanonicalLoop
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade := by
  let physical := sixVertexHorizontalActualSurplusConfigurationPair target
  let firstPairing : SixVertexCompatibleLoopPairing physical.1.1.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.1.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.1.1 physical.1.1.2.1⟩
  let secondPairing : SixVertexCompatibleLoopPairing physical.1.2.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.2.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.2.1 physical.1.2.2.1⟩
  refine ⟨⟨physical.1, firstPairing, secondPairing⟩, ?_⟩
  rw [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
  exact physical.2

@[simp] theorem sixVertexHorizontalHallTargetCanonicalLoop_pair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    (sixVertexHorizontalHallTargetCanonicalLoop target).1.1 =
      (sixVertexHorizontalActualSurplusConfigurationPair target).1 :=
  rfl



noncomputable def sixVertexHorizontalHallHighSourceCanonicalLoop
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade :=
  ⟨sixVertexHorizontalHallSourceCanonicalLoop source.1, by
    simpa [sixVertexHorizontalDegreeTwoLoopHighCharge,
      sixVertexHorizontalDegreeTwoHighCharge] using source.2⟩




inductive SixVertexHorizontalResidualGeometricCertificate
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Type
  | fullMask
      (certificate : SixVertexHorizontalDegreeTwoLoopFullUnitMask source)
  | resolvedCross
      (cross : FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1))
  | fineRelated
      (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
      (related : SixVertexConfigurationPairTwoCycleFineRelated source.1.1
        target.1.1)

namespace SixVertexHorizontalResidualGeometricCertificate

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
    hmiddle_pos hmiddle_lt grade}




noncomputable def ofUnitStrand
    (hdegree : SixVertexLocallyDegreeTwo
      source.1.1.1.1 source.1.1.2.1)
    (seed : SixVertexOrientedDisagreementDart
      source.1.1.1.1 source.1.1.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord
      source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed).sum = 1) :
    SixVertexHorizontalResidualGeometricCertificate source := by
  let mask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed).mask
  have hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees source.1.1.1.1 source.1.1.2.1 edge :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed
  have hbalanced : SixVertexBalancedFlipMask source.1.1.1.1 mask :=
    sixVertexBalancedFlipMask_of_ice_flip source.1.1.1.2.1
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed)
  have hfull : SixVertexFullDisagreementMask
      source.1.1.1.1 source.1.1.2.1 mask :=
    hbalanced.fullDisagreementMask_of_degreeTwo hdegree hsupport
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      source.1.1.1.1 source.1.1.2.1 = 1 := by
    calc
      sixVertexTorusMaskSeamTransfer mask source.1.1.1.1 source.1.1.2.1 =
          sixVertexTorusFlipSeamDelta mask source.1.1.1.1 :=
        sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees hsupport
      _ = (sixVertexDegreeTwoStrandSeamWord source.1.1.1.2.1
          source.1.1.2.2.1 hdegree seed).sum :=
        sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum
          source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed
      _ = 1 := hunit
  refine SixVertexHorizontalResidualGeometricCertificate.fullMask ?_
  refine ⟨mask, ?_, ?_⟩
  · simpa only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows] using hfull
  · simpa only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows] using htransfer


noncomputable def loopTarget
    (certificate : SixVertexHorizontalResidualGeometricCertificate source) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  match certificate with
  | .fullMask full =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source
        (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source full)
  | .resolvedCross cross =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source
        (sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source cross)
  | .fineRelated target _ => target


theorem loopTarget_supported
    (certificate : SixVertexHorizontalResidualGeometricCertificate source) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      certificate.loopTarget.1.1 := by
  cases certificate with
  | fullMask full =>
      exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
        (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source full)
  | resolvedCross cross =>
      exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
        (sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source cross)
  | fineRelated target related => exact related

end SixVertexHorizontalResidualGeometricCertificate



structure SixVertexHorizontalResidualGeometricSurplusRepair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) where
  certificate : SixVertexHorizontalResidualGeometricCertificate
    (sixVertexHorizontalHallSourceCanonicalLoop source)
  target : SixVertexHorizontalDegreeTwoHallTarget T middle
    hmiddle_pos hmiddle_lt grade
  target_physical :
    (sixVertexHorizontalActualSurplusConfigurationPair target).1 =
      certificate.loopTarget.1.1

namespace SixVertexHorizontalResidualGeometricSurplusRepair





noncomputable def ofCertificateSourceWeightZero
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (sixVertexHorizontalPairCompletionProfile T
        (certificate.loopTarget.1.1.1.1.horizontal,
          certificate.loopTarget.1.1.2.1.horizontal)) = 0) :
    SixVertexHorizontalResidualGeometricSurplusRepair source := by
  let configuration :
      {pair : SixVertexMarkedSectorConfiguration T middle ×
          SixVertexMarkedSectorConfiguration T middle //
        sixVertexConfigurationPairBigrade pair = grade} :=
    ⟨certificate.loopTarget.1.1, by
      rw [← sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
      exact certificate.loopTarget.2⟩
  have hrange :=
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
      configuration hzero
  let target := Classical.choose hrange
  have htarget := Classical.choose_spec hrange
  exact
    { certificate := certificate
      target := target
      target_physical := congrArg Subtype.val htarget }



noncomputable def ofCertificateLeftIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source :=
  ofCertificateSourceWeightZero source certificate
    (sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (certificate.loopTarget.1.1.1.1.horizontal,
        certificate.loopTarget.1.1.2.1.horizontal) hleft)



noncomputable def ofCertificateRightIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hright : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      certificate.loopTarget.1.1.2.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source :=
  ofCertificateSourceWeightZero source certificate
    (sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (certificate.loopTarget.1.1.1.1.horizontal,
        certificate.loopTarget.1.1.2.1.horizontal) hright)




noncomputable def ofUnitStrandIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.1)
    (seed : SixVertexOrientedDisagreementDart
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.2.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.2.1
      hdegree seed).sum = 1)
    (hincompatible :
      let certificate :=
        SixVertexHorizontalResidualGeometricCertificate.ofUnitStrand
          hdegree seed hunit
      IsEmpty (SixVertexHorizontalSectorCompletion T
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          certificate.loopTarget.1.1.1.1.horizontal) ∨
        IsEmpty (SixVertexHorizontalSectorCompletion T
          (sixVertexHorizontalUpperSector middle hmiddle_lt)
          certificate.loopTarget.1.1.2.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source := by
  let certificate :=
    SixVertexHorizontalResidualGeometricCertificate.ofUnitStrand
      hdegree seed hunit
  change IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal) ∨
    IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      certificate.loopTarget.1.1.2.1.horizontal) at hincompatible
  by_cases hleft : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal)
  · exact ofCertificateLeftIncompatible source certificate hleft
  · exact ofCertificateRightIncompatible source certificate
      (hincompatible.resolve_left hleft)




noncomputable def ofFineRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade)
    (related : sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source target) :
    SixVertexHorizontalResidualGeometricSurplusRepair source where
  certificate := .fineRelated
    (sixVertexHorizontalHallTargetCanonicalLoop target)
    (by
      change SixVertexConfigurationPairTwoCycleFineRelated
        (sixVertexHorizontalActualDeficitConfigurationPair source).1
        (sixVertexHorizontalActualSurplusConfigurationPair target).1
      exact related)
  target := target
  target_physical := rfl

end SixVertexHorizontalResidualGeometricSurplusRepair



theorem SixVertexHorizontalResidualGeometricSurplusRepair.supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade}
    (repair : SixVertexHorizontalResidualGeometricSurplusRepair source) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source repair.target := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair source).1
    (sixVertexHorizontalActualSurplusConfigurationPair repair.target).1
  rw [repair.target_physical]
  simpa using repair.certificate.loopTarget_supported



noncomputable def sixVertexHorizontalResidualHighBaseKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
        (sixVertexHorizontalHallHighSourceCanonicalLoop source))) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored
        (sixVertexHorizontalHallSourceCanonicalLoop source.1).1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration
      (sixVertexHorizontalHallSourceCanonicalLoop source.1).1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree
        (sixVertexHorizontalHallHighSourceCanonicalLoop source))
      single.toFineRoutedKey)


noncomputable def sixVertexHorizontalResidualHighBranchKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
        (sixVertexHorizontalHallHighSourceCanonicalLoop source)))
    (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored
        (sixVertexHorizontalHallSourceCanonicalLoop source.1).1) :=
  (sixVertexHorizontalResidualHighBaseKey source single).paired
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo
      (sixVertexHorizontalHallSourceCanonicalLoop source.1)) branch



structure SixVertexHorizontalResidualHighGeometricSurplusRepair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) where
  single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
    (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
      (sixVertexHorizontalHallHighSourceCanonicalLoop source))
  target_arrows_ne :
    let key := sixVertexHorizontalResidualHighBaseKey source single
    (key.splice.target false).arrows ≠ (key.splice.target true).arrows
  target : Bool → SixVertexHorizontalDegreeTwoHallTarget T middle
    hmiddle_pos hmiddle_lt grade
  target_physical : ∀ branch,
    (sixVertexHorizontalActualSurplusConfigurationPair (target branch)).1 =
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget
        (sixVertexHorizontalHallSourceCanonicalLoop source.1)
        (sixVertexHorizontalResidualHighBranchKey source single branch)).1.1

namespace SixVertexHorizontalResidualHighGeometricSurplusRepair

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
    hmiddle_pos hmiddle_lt grade}



theorem target_supported
    (repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source)
    (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (repair.target branch) := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      (repair.target branch)).1
  rw [repair.target_physical]
  simpa using sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported
    (sixVertexHorizontalHallSourceCanonicalLoop source.1)
    (sixVertexHorizontalResidualHighBranchKey source repair.single branch)



theorem target_distinct
    (repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source) :
    repair.target false ≠ repair.target true := by
  intro heq
  apply repair.target_arrows_ne
  have hpair := congrArg
    (fun target =>
      (sixVertexHorizontalActualSurplusConfigurationPair target).1) heq
  change
    (sixVertexHorizontalActualSurplusConfigurationPair
        (repair.target false)).1 =
      (sixVertexHorizontalActualSurplusConfigurationPair
        (repair.target true)).1 at hpair
  rw [repair.target_physical false,
    repair.target_physical true] at hpair
  have hphysical := congrArg
    (fun pair : SixVertexConfigurationPhysicalTarget T middle => pair.1.1)
    hpair
  have hbranch :
      ((sixVertexHorizontalResidualHighBranchKey source repair.single false).splice.target
        false).arrows =
      ((sixVertexHorizontalResidualHighBranchKey source repair.single true).splice.target
        false).arrows := by
    simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
      sixVertexLoopDecoratedSpliceUnitTarget_colored] using hphysical
  simpa [sixVertexHorizontalResidualHighBranchKey,
    FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using hbranch

end SixVertexHorizontalResidualHighGeometricSurplusRepair





structure SixVertexPositiveUnitComponentResidualMixedRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  unit : SixVertexPositiveUnitComponentResidualOrbitCover T middle
    hmiddle_pos hmiddle_lt grade
  geometric : ∀ source :
    SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade,
    SixVertexHorizontalResidualGeometricSurplusRepair source.1
  high : ∀ source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
    hmiddle_pos hmiddle_lt grade,
    SixVertexHorizontalResidualHighGeometricSurplusRepair source
  decoder : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade →
    Option (SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_unit : ∀ unitSource,
    decoder (unit.matching unitSource) = some unitSource.1
  decode_geometric : ∀ source,
    decoder (geometric source).target = some source.1
  decode_paired : ∀ highSource branch,
    decoder ((high highSource).target branch) = some highSource.1

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}



noncomputable def paired
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade :=
  (routing.high source).target branch

theorem paired_distinct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    routing.paired source false ≠ routing.paired source true :=
  (routing.high source).target_distinct

theorem paired_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1
        (routing.paired source branch) :=
  (routing.high source).target_supported branch



theorem paired_output_recovers_occurrence
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool)
    (first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (heq : routing.paired first branch = routing.paired second branch) :
    sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second := by
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_paired first branch,
    routing.decode_paired second branch] at hdecoded
  have hsource : first = second := by
    apply Subtype.ext
    exact Option.some.inj hdecoded
  rw [hsource]

theorem paired_injective_with_occurrence
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool)
    (first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (_ : sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second)
    (heq : routing.paired first branch = routing.paired second branch) :
    first = second := by
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_paired first branch,
    routing.decode_paired second branch] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded



theorem geometric_injective
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective (fun source => (routing.geometric source).target) := by
  intro first second heq
  have hdecoded := congrArg routing.decoder heq
  rw [routing.decode_geometric first,
    routing.decode_geometric second] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded



theorem geometric_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1
        (routing.geometric source).target :=
  (routing.geometric source).supported



def nonHighToUnit
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (hrealizable : sixVertexPositiveUnitComponentResidualSource source.1) :
    SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade :=
  ⟨source.1, hrealizable, source.2⟩


def nonHighToGeometric
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (hnotRealizable : ¬
      sixVertexPositiveUnitComponentResidualSource source.1) :
    SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade :=
  ⟨source.1, hnotRealizable, source.2⟩



theorem unit_paired_disjoint
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (unitSource : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (highSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    routing.unit.matching unitSource ≠ routing.paired highSource branch := by
  intro heq
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_unit unitSource,
    routing.decode_paired highSource branch] at hdecoded
  have hsource : unitSource.1 = highSource.1 := Option.some.inj hdecoded
  exact unitSource.2.2 (hsource ▸ highSource.2)




noncomputable def direct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade :=
  if hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1 then
    routing.unit.matching (nonHighToUnit source hrealizable)
  else (routing.geometric
    (nonHighToGeometric source hrealizable)).target

theorem decode_direct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    routing.decoder (routing.direct source) = some source.1 := by
  by_cases hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1
  · rw [direct, dif_pos hrealizable]
    exact routing.decode_unit (nonHighToUnit source hrealizable)
  · rw [direct, dif_neg hrealizable]
    exact routing.decode_geometric
      (nonHighToGeometric source hrealizable)

theorem direct_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (routing.direct source) := by
  by_cases hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1
  · rw [direct, dif_pos hrealizable]
    exact routing.unit.matching_supported
      (nonHighToUnit source hrealizable)
  · rw [direct, dif_neg hrealizable]
    exact routing.geometric_supported
      (nonHighToGeometric source hrealizable)

theorem direct_injective
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.direct := by
  intro first second heq
  have hdecoded := congrArg routing.decoder heq
  rw [routing.decode_direct first, routing.decode_direct second] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded

theorem direct_paired_disjoint
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (directSource : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (pairedSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    routing.direct directSource ≠ routing.paired pairedSource branch := by
  intro heq
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_direct directSource,
    routing.decode_paired pairedSource branch] at hdecoded
  have hsource : directSource.1 = pairedSource.1 := Option.some.inj hdecoded
  exact directSource.2 (hsource ▸ pairedSource.2)



noncomputable def toHighChargeHallRouting
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade where
  direct := routing.direct
  direct_injective := routing.direct_injective
  direct_supported := routing.direct_supported
  paired := routing.paired
  paired_distinct := routing.paired_distinct
  paired_supported := routing.paired_supported
  paired_output_recovers_occurrence :=
    routing.paired_output_recovers_occurrence
  paired_injective_with_occurrence := routing.paired_injective_with_occurrence
  direct_paired_disjoint := routing.direct_paired_disjoint


noncomputable def toTokenComponents
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade :=
  routing.toHighChargeHallRouting.toTokenComponents

end SixVertexPositiveUnitComponentResidualMixedRouting



def SixVertexPositiveUnitComponentResidualMixedRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)


theorem offDiagonalTwoCycleMatching_of_positiveUnitComponentMixedRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexPositiveUnitComponentResidualMixedRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  apply offDiagonalTwoCycleMatching_of_tokenComponentRoutings
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  exact ⟨routing.toTokenComponents⟩


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_positiveUnitComponentMixedRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexPositiveUnitComponentResidualMixedRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_positiveUnitComponentMixedRoutings
        T middle hmiddle_pos hmiddle_lt hroutings)

end

end StatMech.FrontierD
