/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveSeamWindingFlows
import Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting












namespace StatMech.FrontierD

noncomputable section


def sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexArrows T × SixVertexArrows T :=
  (source.1.1.1.1, source.1.1.2.1)


def sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
    {T : EvenTorus} {middle : Fin (T.width + 1)} {grade : Nat × Nat}
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    SixVertexArrows T × SixVertexArrows T :=
  (target.1.1.1.1, target.1.1.2.1)


def sixVertexHorizontalDegreeTwoLoopRoutedSignedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1))
    (family : SixVertexAtMostTwoCycleFamily T) (sign : Bool)
    (horizontalDelta : sixVertexPairUnionHorizontalDelta
        (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
        (sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)) =
      fun v => if sign then family.horizontalFlow v
        else -family.horizontalFlow v)
    (verticalDelta : sixVertexPairUnionVerticalDelta
        (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
        (sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)) =
      fun v => if sign then family.verticalFlow v
        else -family.verticalFlow v) :
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
      family sign where
  target := sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
    (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)
  horizontalDelta := horizontalDelta
  verticalDelta := verticalDelta






structure SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
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
  firstSigned : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).firstWindingFamily
      true
  first_target : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    (firstSigned source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 false))
  secondSigned : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).secondWindingFamily
      true
  second_target : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    (secondSigned source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 true))

namespace SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection



theorem source_recoverable
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
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
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
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
  apply (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).windingTargets_ne
    (data.firstSigned source) (data.secondSigned source)
  calc
    (data.firstSigned source).target =
        sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 false)) := data.first_target source
    _ = sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 true)) := harrows
    _ = (data.secondSigned source).target := (data.second_target source).symm


def toRoutedReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  key := data.key
  source_recoverable := by
    intro first firstBranch second secondBranch heq
    exact data.source_recoverable first second firstBranch secondBranch heq
  high_distinct := data.high_distinct

end SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection


def SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade)



theorem degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨data⟩ := hdecoded grade
  exact ⟨data.toRoutedReconnection⟩



theorem loopBigradeFibers_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle :=
  loopBigradeFibers_of_degreeTwoLoopRoutedReconnections T middle
    hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt hdecoded)



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections
    T middle hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt hdecoded)

end

end StatMech.FrontierD
