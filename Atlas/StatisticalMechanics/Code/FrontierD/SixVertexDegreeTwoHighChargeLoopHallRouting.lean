/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting
import Code.FrontierD.SixVertexResolvedLoopBigradeBridge
import Code.FrontierD.SixVertexRoutedUnitFineRelation
import Code.FrontierD.SixVertexRoutedKeySourceRebase

















open Finset

namespace StatMech.FrontierD

noncomputable section

local instance degreeTwoHighChargeLoopHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p



theorem sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (source : SixVertexLoopDecoratedPair T left right)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor (sixVertexLoopDecoratedPairColored source) slot =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1
          source.1.2.2.1 hdegree) slot := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> rfl



noncomputable def sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (source : SixVertexLoopDecoratedPair T left right)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1
        source.1.2.2.1 hdegree)) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source) :=
  key.rebase
    (sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned
      source hdegree)
    (by
      intro layer
      cases layer <;>
        simp only [sixVertexLoopDecoratedPairColored_false_arrows,
          sixVertexLoopDecoratedPairColored_true_arrows,
          sixVertexDegreeTwoAlignedColoredSource_arrows, Bool.false_eq_true,
          if_false, if_true])



theorem sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (source : SixVertexLoopDecoratedPair T left right)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1
        source.1.2.2.1 hdegree)) :
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration
      source hdegree key).splice.target = key.splice.target := by
  apply FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target

abbrev SixVertexHorizontalDegreeTwoLoopHallSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) //
    sixVertexLoopDecoratedPairBigrade source = grade}

abbrev SixVertexHorizontalDegreeTwoLoopHallTarget
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (grade : Nat × Nat) :=
  {target : SixVertexLoopDecoratedPair T middle middle //
    sixVertexLoopDecoratedPairBigrade target = grade}



def sixVertexHorizontalDegreeTwoLoopHighCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  let pair := source.1.1
  ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1 pair.2.1,
    ∃ component :
        (sixVertexDegreeTwoSynchronizedGraph pair.1.2.1 pair.2.2.1
          hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
        pair.1.2.1 pair.2.2.1 hdegree component

abbrev SixVertexHorizontalDegreeTwoLoopHighChargeSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade //
    sixVertexHorizontalDegreeTwoLoopHighCharge source}




noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeDegree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.1.2.1 :=
  Classical.choose source.2


noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeComponent
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    (sixVertexDegreeTwoSynchronizedGraph
      source.1.1.1.1.2.1 source.1.1.1.2.2.1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)).ConnectedComponent :=
  Classical.choose (Classical.choose_spec source.2)


theorem sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
      source.1.1.1.1.2.1 source.1.1.1.2.2.1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
      (sixVertexHorizontalDegreeTwoLoopHighChargeComponent source) :=
  Classical.choose_spec (Classical.choose_spec source.2)


noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeSeed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :=
  sixVertexDegreeTwoSynchronizedHighChargeSeed
    source.1.1.1.1.2.1 source.1.1.1.2.2.1
    (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
    (sixVertexHorizontalDegreeTwoLoopHighChargeComponent source)
    (sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge source)


noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).occurrenceEquiv



noncomputable def sixVertexHorizontalDegreeTwoLoopRoutedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade := by
  let profile := sixVertexHorizontalPairBoundedFineRowProfile
    ((sixVertexLoopDecoratedPairColored source.1 false).arrows.horizontal,
      (sixVertexLoopDecoratedPairColored source.1 true).arrows.horizontal)
  let fineSource : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile :=
    ⟨source.1, by
      simp only [profile, sixVertexLoopDecoratedPairColored_false_arrows,
        sixVertexLoopDecoratedPairColored_true_arrows]⟩
  let target := sixVertexLoopDecoratedRoutedUnitTarget middle
    hmiddle_pos hmiddle_lt source.1 key
  refine ⟨target, ?_⟩
  have hbig := sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade
    middle hmiddle_pos hmiddle_lt profile fineSource key
  exact hbig.trans source.2

@[simp] theorem sixVertexHorizontalDegreeTwoLoopRoutedTarget_val
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1 =
      sixVertexLoopDecoratedRoutedUnitTarget middle
        hmiddle_pos hmiddle_lt source.1 key := by
  rfl


theorem sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1 := by
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1.1.1, source.1.1.2.1)
    ((sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1.1.1,
      (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1.2.1)
  have hrelated := key.target_twoCycleFine
  rw [← sixVertexLoopDecoratedRoutedUnitTarget_colored middle
    hmiddle_pos hmiddle_lt source.1 key] at hrelated
  simpa only [sixVertexHorizontalDegreeTwoLoopRoutedTarget_val,
    sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows] using hrelated



noncomputable def sixVertexHorizontalDegreeTwoLoopSynchronizedRoutedKey
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat)
    (paired : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source))
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration source.1.1
    (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
    ((paired source).key branch)






structure SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  paired : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  source_recoverable : ∀ first firstBranch second secondBranch,
    sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1
        (sixVertexHorizontalDegreeTwoLoopSynchronizedRoutedKey T middle
          hmiddle_pos hmiddle_lt grade paired first firstBranch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1
        (sixVertexHorizontalDegreeTwoLoopSynchronizedRoutedKey T middle
          hmiddle_pos hmiddle_lt grade paired second secondBranch) →
    first = second

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets



noncomputable def routedKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  sixVertexHorizontalDegreeTwoLoopSynchronizedRoutedKey T middle
    hmiddle_pos hmiddle_lt grade targets.paired source branch


theorem routedKey_target
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    (targets.routedKey source branch).splice.target =
      ((targets.paired source).key branch).splice.target := by
  exact sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target
    source.1.1 (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
      ((targets.paired source).key branch)



theorem routedTarget_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source false) ≠
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source true) := by
  intro heq
  apply (targets.paired source).key_target_distinct
  have hval := congrArg Subtype.val heq
  have hdecorated :
      sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt
          source.1.1 (targets.routedKey source false) =
        sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt
          source.1.1 (targets.routedKey source true) := by
    simpa only [sixVertexHorizontalDegreeTwoLoopRoutedTarget_val] using hval
  have hcolored := congrArg sixVertexLoopDecoratedPairColored hdecorated
  rw [sixVertexLoopDecoratedRoutedUnitTarget_colored,
    sixVertexLoopDecoratedRoutedUnitTarget_colored,
    targets.routedKey_target source false,
    targets.routedKey_target source true] at hcolored
  exact hcolored



theorem routedTarget_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    Function.Injective (fun source :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade =>
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source branch)) := by
  intro first second heq
  exact targets.source_recoverable first branch second branch heq

end SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets




structure SixVertexHorizontalDegreeTwoLoopRoutedReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  key : ∀ source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade,
    Bool → FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)
  source_recoverable : ∀ first firstBranch second secondBranch,
    sixVertexHorizontalDegreeTwoLoopRoutedTarget first
        (key first firstBranch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second
        (key second secondBranch) →
    first = second
  high_distinct : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (key source.1 false) ≠
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (key source.1 true)



def SixVertexHorizontalDegreeTwoLoopRoutedReconnection.PairedRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) : Prop :=
  ∃ branch, sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
    (reconnection.key source.1 branch) = target

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_branch_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) (branch) :
    Function.Injective (fun source :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade =>
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (reconnection.key source.1 branch)) := by
  intro first second heq
  apply Subtype.ext
  exact reconnection.source_recoverable
    first.1 branch second.1 branch heq

noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedInverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target}) : Bool :=
  Classical.choose source.2

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_spec
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target}) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1.1
        (reconnection.key source.1.1
          (reconnection.pairedInverseBranch target source)) = target :=
  Classical.choose_spec source.2


theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.output_recovers_occurrence
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (branch) (first second : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade)
    (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1
        (reconnection.key first.1 branch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1
        (reconnection.key second.1 branch)) :
    sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv second := by
  have hsource : first = second := by
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 branch second.1 branch heq
  rw [hsource]



noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (reconnection.pairedInverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : reconnection.pairedInverseBranch target first =
        reconnection.pairedInverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply reconnection.paired_branch_injective
      (reconnection.pairedInverseBranch target first)
    calc
      sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1.1
          (reconnection.key first.1.1
            (reconnection.pairedInverseBranch target first)) = target :=
        reconnection.paired_inverse_spec target first
      _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1.1
          (reconnection.key second.1.1
            (reconnection.pairedInverseBranch target second)) :=
        (reconnection.paired_inverse_spec target second).symm
      _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1.1
          (reconnection.key second.1.1
            (reconnection.pairedInverseBranch target first)) := by rw [hbranch]

set_option maxHeartbeats 800000 in

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (reconnection.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade //
        reconnection.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (reconnection.key source.1 (finTwoEquiv branch)),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exfalso
          exact reconnection.high_distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq)
        · exfalso
          exact reconnection.high_distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

set_option maxHeartbeats 800000 in

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    (Finset.univ.filter fun source =>
      reconnection.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (reconnection.pairedInverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ reconnection.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree
    reconnection.PairedRelated 2 (by omega)
  · exact reconnection.paired_source_degree
  · exact reconnection.paired_inverse_degree


noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade →
      SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  Classical.choose
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      reconnection.PairedRelated).mp reconnection.paired_hall)

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.pairedMatching :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      reconnection.PairedRelated).mp reconnection.paired_hall)).1

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source) : reconnection.PairedRelated source
      (reconnection.pairedMatching source) :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      reconnection.PairedRelated).mp reconnection.paired_hall)).2 source



noncomputable def SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  if hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source then
    reconnection.pairedMatching ⟨source, hhigh⟩
  else
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source
      (reconnection.key source false)


theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (reconnection.reconnect source).1.1 := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨source, hhigh⟩
    rw [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      dif_pos hhigh, ← hbranch]
    exact sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported source
      (reconnection.key source branch)
  · rw [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      dif_neg hhigh]
    exact sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported source
      (reconnection.key source false)

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoLoopHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoLoopHighCharge second
  · have hsub : (⟨first, hfirst⟩ :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade) = ⟨second, hsecond⟩ := by
      apply reconnection.pairedMatching_injective
      simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val hsub
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨first, hfirst⟩
    have hout : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
        (reconnection.key first branch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second
        (reconnection.key second false) := by
      calc
        _ = reconnection.pairedMatching ⟨first, hfirst⟩ := hbranch
        _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second
            (reconnection.key second false) := by
          simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hfirst, hsecond] using heq
    have hs := reconnection.source_recoverable
      first branch second false hout
    exact False.elim (hsecond (hs ▸ hfirst))
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨second, hsecond⟩
    have hout : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
        (reconnection.key first false) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second
        (reconnection.key second branch) := by
      calc
        _ = reconnection.reconnect first := by
          simp [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hfirst]
        _ = reconnection.reconnect second := heq
        _ = reconnection.pairedMatching ⟨second, hsecond⟩ := by
          simp [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hsecond]
        _ = _ := hbranch.symm
    have hs := reconnection.source_recoverable
      first false second branch hout
    exact False.elim (hfirst (hs ▸ hsecond))
  · apply reconnection.source_recoverable first false second false
    simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      hfirst, hsecond] using heq



noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnectEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallSource T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  ⟨reconnection.reconnect, reconnection.reconnect_injective⟩

def SixVertexHorizontalDegreeTwoLoopRoutedReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopRoutedReconnection
    T middle hmiddle_pos hmiddle_lt grade)



theorem loopBigradeFibers_of_degreeTwoLoopRoutedReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
  intro grade
  obtain ⟨reconnection⟩ := hreconnections grade
  exact Fintype.card_le_of_embedding reconnection.reconnectEmbedding

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (loopBigradeFibers_of_degreeTwoLoopRoutedReconnections
        T middle hmiddle_pos hmiddle_lt hreconnections)

end

end StatMech.FrontierD
