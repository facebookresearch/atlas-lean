/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierBlockLower
import Code.FrontierD.FKRectDualBarrierForceTopology
import Code.FrontierD.FKRectDualSourceBarrierPattern



namespace StatMech.FrontierD

noncomputable section




theorem fkRectWindingBlockColumn_forcedAuxiliary_le_dualPullbackSource
    (k scale blocks right : Nat) (hright : 1 ≤ right)
    (hproper : right + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 ≤ x.val) (hxright : x.val ≤ right)
    {q a b c : Real} (hq : 1 ≤ q)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hattachment : c ≤
      fkRectCriticalEventMass
        (fkRectWindingBlockVerticalFamily k scale blocks) q
        (fkRectUnitAttachmentOpenEvent
          (fkRectWindingBlockVerticalFamily k scale blocks)))
    (hbulk : ∀ xy ∈ fkRectWindingBlockColumnBulkPairs
        k scale blocks right x hxleft hxright,
      a ≤ FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectColumnBand
            (fkRectWindingBlockVerticalFamily k scale blocks)
            1 right 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hconnector : ∀ xy ∈ fkRectWindingBlockColumnConnectorPairs
        k scale blocks right hright x hxleft hxright,
      b ≤ FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectColumnBand
            (fkRectWindingBlockVerticalFamily k scale blocks)
            1 right 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    FK.cFE (fkRectCriticalP q) q ^
          (2 * (fkRectWindingBlockVerticalFamily k scale blocks).width) *
        (c * b ^ 2 * a ^ (blocks + 1)) ≤
      fkRectCriticalEventMass
        (fkRectWindingBlockVerticalFamily k scale blocks) q
        (fkRectDualPullbackSourceLeftBarrier
          (fkRectWindingBlockVerticalFamily k scale blocks) right
          (fkRectUnitLeftBarrierGap
            (fkRectWindingBlockVerticalFamily k scale blocks))) := by
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let pairs := fkRectWindingBlockColumnAuxiliaryPairs
    k scale blocks right hright x hxleft hxright
  let A := fkRectUnitDualBarrierAuxiliary R right pairs
  have hauxLower : c * b ^ 2 * a ^ (blocks + 1) ≤
      fkRectCriticalEventMass R q A := by
    exact fkRectWindingBlockColumn_attachment_mul_connector_sq_mul_bulk_pow_le_auxiliary
      k scale blocks right hright x hxleft hxright hq ha ha1 hb hb1
        hattachment hbulk hconnector
  have hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R
          (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
          (fkRectDualPullbackConfiguration R
            (fkRectAllButOneOpenConfiguration R
              (fkRectUnitLeftBarrierGap R))) omega ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R right) := by
    intro omega homega
    exact
      fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing
        R right hright hproper omega pairs
        (fkRectWindingBlockColumnAuxiliaryPairs_spans
          k scale blocks right hright x hxleft hxright) homega
  have hpattern :=
    fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource
      R right hq (fkRectUnitLeftBarrierGap R) A hforce
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  calc
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
          (c * b ^ 2 * a ^ (blocks + 1)) ≤
        FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
          fkRectCriticalEventMass R q A :=
      mul_le_mul_of_nonneg_left hauxLower (pow_nonneg hc _)
    _ ≤ fkRectCriticalEventMass R q
        (fkRectDualPullbackSourceLeftBarrier R right
          (fkRectUnitLeftBarrierGap R)) := hpattern

end

end StatMech.FrontierD
