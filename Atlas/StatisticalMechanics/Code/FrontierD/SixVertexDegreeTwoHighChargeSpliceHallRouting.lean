/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
import Code.FrontierD.SixVertexFullMaskSpliceKey
import Code.FrontierD.SixVertexResolvedCrossRoutedKey
import Code.FrontierD.SixVertexSpliceKeyLayerSwap










namespace StatMech.FrontierD

noncomputable section

open Finset

local instance degreeTwoHighChargeSpliceHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p


noncomputable def sixVertexLoopDecoratedSpliceUnitTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source)) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  have hsectors := key.splice.target_middleSectors middle.val hmiddle_pos
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
    key.seamDelta_false key.seamDelta_true
  exact ⟨(⟨key.splice.target false |>.arrows,
      (key.splice.target false).iceRule, hsectors.1⟩,
    ⟨key.splice.target true |>.arrows,
      (key.splice.target true).iceRule, hsectors.2⟩),
    (key.splice.target false).toCompatible,
    (key.splice.target true).toCompatible⟩

@[simp] theorem sixVertexLoopDecoratedSpliceUnitTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos
          hmiddle_lt source key) = key.splice.target := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

theorem sixVertexLoopDecoratedSpliceUnitTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos
          hmiddle_lt source key) =
      sixVertexLoopDecoratedPairBigrade source := by
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedSpliceUnitTarget_colored]
  exact key.target_bigrade


noncomputable def sixVertexHorizontalDegreeTwoLoopSpliceTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  ⟨sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt
      source.1 key,
    (sixVertexLoopDecoratedSpliceUnitTarget_bigrade middle hmiddle_pos
      hmiddle_lt source.1 key).trans source.2⟩

@[simp] theorem sixVertexHorizontalDegreeTwoLoopSpliceTarget_val
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1 =
      sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt
        source.1 key := rfl



theorem sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1 := by
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1.1.1, source.1.1.2.1)
    ((sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1.1.1,
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1.2.1)
  have hrelated := key.target_twoCycleFine
  rw [← sixVertexLoopDecoratedSpliceUnitTarget_colored middle
    hmiddle_pos hmiddle_lt source.1 key] at hrelated
  simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
    sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows] using hrelated



theorem sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey.SourceSeamDifferenceTwo
      (sixVertexLoopDecoratedPairColored source.1) := by
  unfold FKColoredFineTwoCycleUnitTransferSpliceKey.SourceSeamDifferenceTwo
  rw [sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows]
  have hlower := source.1.1.1.2.2
  have hupper := source.1.1.2.2.2
  simp only [sixVertexHorizontalLowerSector,
    sixVertexHorizontalUpperSector] at hlower hupper
  omega



noncomputable def sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat)
    (single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
      SixVertexDegreeTwoSynchronizedSupportedSplitTarget
        (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source))
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration source.1.1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
      (single source).toFineRoutedKey)





structure SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  layers_ne : ∀ source,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    key.splice.target false ≠ key.splice.target true
  base_injective : Function.Injective (fun source =>
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
      (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
        T middle hmiddle_pos hmiddle_lt grade single source))

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets

noncomputable def key
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey T middle
    hmiddle_pos hmiddle_lt grade targets.single source

noncomputable def branchKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  (targets.key source).paired
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1) branch

theorem branchKey_true_target
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    (targets.branchKey source true).splice.target =
      fkColoredLoopPairingPairSwapLayers
        (targets.branchKey source false).splice.target := by
  simp [branchKey, FKColoredFineTwoCycleUnitTransferSpliceKey.paired]


theorem target_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source false) ≠
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source true) := by
  intro heq
  apply (targets.key source).paired_target_distinct
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1)
    (targets.layers_ne source)
  have hval := congrArg Subtype.val heq
  have hcolored := congrArg sixVertexLoopDecoratedPairColored hval
  simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
    sixVertexLoopDecoratedSpliceUnitTarget_colored] using hcolored



theorem target_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    Function.Injective (fun source :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source branch)) := by
  cases branch
  · simpa [branchKey, key,
      FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
      targets.base_injective
  · intro first second heq
    apply targets.base_injective
    apply Subtype.ext
    apply sixVertexLoopDecoratedPairColored_injective
    have hcolored := congrArg sixVertexLoopDecoratedPairColored
      (congrArg Subtype.val heq)
    have hbranch : (targets.branchKey first true).splice.target =
        (targets.branchKey second true).splice.target := by
      simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
        sixVertexLoopDecoratedSpliceUnitTarget_colored] using hcolored
    rw [targets.branchKey_true_target first,
      targets.branchKey_true_target second] at hbranch
    have horiginal := congrArg fkColoredLoopPairingPairSwapLayers hbranch
    simpa [branchKey, key,
      FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using horiginal



def PairedRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) : Prop :=
  ∃ branch, sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
    (targets.branchKey source branch) = target

noncomputable def pairedInverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      targets.PairedRelated source target}) : Bool :=
  Classical.choose source.2

theorem paired_inverse_spec
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      targets.PairedRelated source target}) :
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1.1
        (targets.branchKey source.1
          (targets.pairedInverseBranch target source)) = target :=
  Classical.choose_spec source.2



noncomputable def pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      targets.PairedRelated source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (targets.pairedInverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : targets.pairedInverseBranch target first =
        targets.pairedInverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    have htarget : first.1 = second.1 := by
      apply targets.target_injective
        (targets.pairedInverseBranch target first)
      calc
        sixVertexHorizontalDegreeTwoLoopSpliceTarget first.1.1
            (targets.branchKey first.1
              (targets.pairedInverseBranch target first)) = target :=
          targets.paired_inverse_spec target first
        _ = sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1.1
            (targets.branchKey second.1
              (targets.pairedInverseBranch target second)) :=
          (targets.paired_inverse_spec target second).symm
        _ = sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1.1
            (targets.branchKey second.1
              (targets.pairedInverseBranch target first)) := by rw [hbranch]
    exact htarget

set_option maxHeartbeats 800000 in
theorem paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (targets.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade //
        targets.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
            (targets.branchKey source (finTwoEquiv branch)),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exfalso
          exact targets.target_distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq)
        · exfalso
          exact targets.target_distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

set_option maxHeartbeats 800000 in
theorem paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    (Finset.univ.filter fun source =>
      targets.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (targets.pairedInverseCode target)
  simpa [Fintype.card_subtype] using hcard


theorem paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ targets.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree targets.PairedRelated 2 (by omega)
  · exact targets.paired_source_degree
  · exact targets.paired_inverse_degree



noncomputable def pairedMatching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade →
      SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  Classical.choose
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      targets.PairedRelated).mp targets.paired_hall)

theorem pairedMatching_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective targets.pairedMatching :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      targets.PairedRelated).mp targets.paired_hall)).1

theorem pairedMatching_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source) : targets.PairedRelated source
      (targets.pairedMatching source) :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      targets.PairedRelated).mp targets.paired_hall)).2 source



theorem pairedMatching_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1.1
      (targets.pairedMatching source).1.1 := by
  obtain ⟨branch, hbranch⟩ := targets.pairedMatching_related source
  rw [← hbranch]
  exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source.1
    (targets.branchKey source branch)

end SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets




structure SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  layers_ne : ∀ source,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    key.splice.target false ≠ key.splice.target true
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
  decode_target : ∀ source branch,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
      (key.paired
        (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1)
        branch)) = some source

namespace SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets



noncomputable def toSingleTargets
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade where
  single := decoded.single
  layers_ne := decoded.layers_ne
  base_injective := by
    intro first second heq
    have hdecode := congrArg decoded.decode heq
    have hfirst : decoded.decode
        (sixVertexHorizontalDegreeTwoLoopSpliceTarget first.1
          (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
            T middle hmiddle_pos hmiddle_lt grade decoded.single first)) =
        some first := by
      simpa [FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
        decoded.decode_target first false
    have hsecond : decoded.decode
        (sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1
          (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
            T middle hmiddle_pos hmiddle_lt grade decoded.single second)) =
        some second := by
      simpa [FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
        decoded.decode_target second false
    rw [hfirst, hsecond] at hdecode
    exact Option.some.inj hdecode

end SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets





structure SixVertexHorizontalDegreeTwoLoopSpliceReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighKey : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredFineTwoCycleUnitTransferSpliceKey
        (sixVertexLoopDecoratedPairColored source.1)
  nonHigh_injective : ∀ first
      (hfirst : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge first) second
      (hsecond : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge second),
    sixVertexHorizontalDegreeTwoLoopSpliceTarget first
        (nonHighKey first hfirst) =
      sixVertexHorizontalDegreeTwoLoopSpliceTarget second
        (nonHighKey second hsecond) →
    first = second
  high_nonHigh_disjoint : ∀
      (highSource : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade)
      (nonHighSource : SixVertexHorizontalDegreeTwoLoopHallSource T middle
        hmiddle_pos hmiddle_lt grade)
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge nonHighSource),
    high.pairedMatching highSource ≠
      sixVertexHorizontalDegreeTwoLoopSpliceTarget nonHighSource
        (nonHighKey nonHighSource hnon)

namespace SixVertexHorizontalDegreeTwoLoopSpliceReconnection


noncomputable def reconnect
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  if hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source then
    reconnection.high.pairedMatching ⟨source, hhigh⟩
  else
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (reconnection.nonHighKey source hhigh)

theorem reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (reconnection.reconnect source).1.1 := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source
  · rw [reconnect, dif_pos hhigh]
    exact reconnection.high.pairedMatching_supported ⟨source, hhigh⟩
  · rw [reconnect, dif_neg hhigh]
    exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
      (reconnection.nonHighKey source hhigh)

theorem reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoLoopHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoLoopHighCharge second
  · have hsub : (⟨first, hfirst⟩ :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade) = ⟨second, hsecond⟩ := by
      apply reconnection.high.pairedMatching_injective
      simpa [reconnect, hfirst, hsecond] using heq
    exact congrArg Subtype.val hsub
  · exfalso
    exact reconnection.high_nonHigh_disjoint ⟨first, hfirst⟩ second
      hsecond (by simpa [reconnect, hfirst, hsecond] using heq)
  · exfalso
    exact reconnection.high_nonHigh_disjoint ⟨second, hsecond⟩ first
      hfirst (by simpa [reconnect, hfirst, hsecond] using heq.symm)
  · apply reconnection.nonHigh_injective first hfirst second hsecond
    simpa [reconnect, hfirst, hsecond] using heq

noncomputable def reconnectEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallSource T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  ⟨reconnection.reconnect, reconnection.reconnect_injective⟩

end SixVertexHorizontalDegreeTwoLoopSpliceReconnection





structure SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  layers_ne : ∀ source,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    key.splice.target false ≠ key.splice.target true
  nonHighKey : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredFineTwoCycleUnitTransferSpliceKey
        (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_target : ∀ source branch,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
      (key.paired
        (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1)
        branch)) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (nonHighKey source hnon)) = some source

namespace SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection


noncomputable def highDecoded
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade where
  single := decoded.single
  layers_ne := decoded.layers_ne
  decode := fun target => (decoded.decode target).bind fun source =>
    if hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source then
      some ⟨source, hhigh⟩
    else none
  decode_target := by
    intro source branch
    dsimp only
    rw [decoded.decode_high_target source branch]
    simp [source.2]

noncomputable def high
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade :=
  decoded.highDecoded.toSingleTargets



theorem decode_high_matching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    decoded.decode (decoded.high.pairedMatching source) = some source.1 := by
  obtain ⟨branch, hbranch⟩ := decoded.high.pairedMatching_related source
  rw [← hbranch]
  exact decoded.decode_high_target source branch



noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := decoded.nonHighKey
  nonHigh_injective := by
    intro first hfirst second hsecond heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_nonHigh_target first hfirst,
      decoded.decode_nonHigh_target second hsecond] at hdecode
    exact Option.some.inj hdecode
  high_nonHigh_disjoint := by
    intro highSource nonHighSource hnon heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_high_matching highSource,
      decoded.decode_nonHigh_target nonHighSource hnon] at hdecode
    have hsource : highSource.1 = nonHighSource := Option.some.inj hdecode
    exact hnon (hsource ▸ highSource.2)

end SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection





structure SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighKey : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredFineTwoCycleUnitTransferSpliceKey
        (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_matching : ∀ source,
    decode (high.pairedMatching source) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (nonHighKey source hnon)) = some source

namespace SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder

noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := decoded.nonHighKey
  nonHigh_injective := by
    intro first hfirst second hsecond heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_nonHigh_target first hfirst,
      decoded.decode_nonHigh_target second hsecond] at hdecode
    exact Option.some.inj hdecode
  high_nonHigh_disjoint := by
    intro highSource nonHighSource hnon heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_high_matching highSource,
      decoded.decode_nonHigh_target nonHighSource hnon] at hdecode
    have hsource : highSource.1 = nonHighSource := Option.some.inj hdecode
    exact hnon (hsource ▸ highSource.2)

end SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder




noncomputable def sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    cross.toFineTwoCycleRoutedKey




structure SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighCross : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_matching : ∀ source,
    decode (high.pairedMatching source) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source
        (nonHighCross source hnon))) = some source

namespace SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder

noncomputable def toSelectedOutputDecoder
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder
        T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := fun source hnon =>
    sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source
      (decoded.nonHighCross source hnon)
  decode := decoded.decode
  decode_high_matching := decoded.decode_high_matching
  decode_nonHigh_target := decoded.decode_nonHigh_target

noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder
        T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade :=
  decoded.toSelectedOutputDecoder.toSpliceReconnection

end SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder



abbrev SixVertexHorizontalDegreeTwoLoopFullUnitMask
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask ∧
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1}

noncomputable def sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalDegreeTwoLoopFullUnitMask source) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1) :=
  sixVertexFullUnitMaskSpliceKey
    (sixVertexLoopDecoratedPairColored source.1) certificate.1
      certificate.2.1 certificate.2.2



structure SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighMask : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      SixVertexHorizontalDegreeTwoLoopFullUnitMask source
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_matching : ∀ source,
    decode (high.pairedMatching source) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source
        (nonHighMask source hnon))) = some source

namespace SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder

noncomputable def toSelectedOutputDecoder
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := fun source hnon =>
    sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source
      (decoded.nonHighMask source hnon)
  decode := decoded.decode
  decode_high_matching := decoded.decode_high_matching
  decode_nonHigh_target := decoded.decode_nonHigh_target

noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade :=
  decoded.toSelectedOutputDecoder.toSpliceReconnection

end SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder



noncomputable def
    SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection.toSelectedOutputDecoder
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := decoded.nonHighKey
  decode := decoded.decode
  decode_high_matching := decoded.decode_high_matching
  decode_nonHigh_target := decoded.decode_nonHigh_target

def SixVertexHorizontalDegreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopSpliceReconnection
    T middle hmiddle_pos hmiddle_lt grade)

theorem loopBigradeFibers_of_degreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
  intro grade
  obtain ⟨reconnection⟩ := hreconnections grade
  exact Fintype.card_le_of_embedding reconnection.reconnectEmbedding

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (loopBigradeFibers_of_degreeTwoLoopSpliceReconnections
        T middle hmiddle_pos hmiddle_lt hreconnections)

def SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade,
    Nonempty (SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)

theorem degreeTwoLoopSpliceReconnections_of_decoded
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopDecodedSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_decoded
        T middle hmiddle_pos hmiddle_lt hdecoded)

def SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
    T middle hmiddle_pos hmiddle_lt grade)

theorem degreeTwoLoopSpliceReconnections_of_selectedOutputDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoders
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoders
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_selectedOutputDecoders
        T middle hmiddle_pos hmiddle_lt hdecoded)

def SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
      T middle hmiddle_pos hmiddle_lt grade)

def SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoder
      T middle hmiddle_pos hmiddle_lt grade)

theorem degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem
    sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputResolvedCrossDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt hdecoded)

theorem degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputFullMaskDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt hdecoded)

end

end StatMech.FrontierD
