/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall











namespace StatMech.FrontierD

noncomputable section


structure SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  key : ∀ source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade,
    Bool → FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade
  decode_target : ∀ source branch,
    decode (sixVertexHorizontalDegreeTwoLoopRoutedTarget source
      (key source branch)) = source
  family : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade → SixVertexAtMostTwoCycleFamily T
  repair : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (family source) true
  repair_layers_ne : ∀ source,
    (repair source).target.1 ≠ (repair source).target.2
  first_target : ∀ source,
    (repair source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 false))
  second_target : ∀ source,
    (repair source).swapTarget.target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 true))

namespace SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair

theorem source_recoverable
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
      T middle hmiddle_pos hmiddle_lt grade)
    (first second : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) (firstBranch secondBranch : Bool)
    (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
          (data.key first firstBranch) =
        sixVertexHorizontalDegreeTwoLoopRoutedTarget second
          (data.key second secondBranch)) :
    first = second := by
  have hdecode := congrArg data.decode heq
  rw [data.decode_target first firstBranch,
    data.decode_target second secondBranch] at hdecode
  exact hdecode


theorem high_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (data.key source.1 false) ≠
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (data.key source.1 true) := by
  intro heq
  have harrows := congrArg
    sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair heq
  apply ((data.repair source).target_ne_swapTarget_iff.mpr
    (data.repair_layers_ne source))
  calc
    (data.repair source).target =
        sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 false)) := data.first_target source
    _ = sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 true)) := harrows
    _ = (data.repair source).swapTarget.target :=
      (data.second_target source).symm



def toRoutedReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  key := data.key
  source_recoverable := by
    intro first firstBranch second secondBranch heq
    exact data.source_recoverable first second firstBranch secondBranch heq
  high_distinct := data.high_distinct

end SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair

def SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
    T middle hmiddle_pos hmiddle_lt grade)

theorem degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨repair⟩ := hrepairs grade
  exact ⟨repair.toRoutedReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections
    T middle hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt hrepairs)

end

end StatMech.FrontierD
