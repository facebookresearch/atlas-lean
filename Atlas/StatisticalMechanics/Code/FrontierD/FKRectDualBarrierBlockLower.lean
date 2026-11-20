/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierBlockChain
import Code.FrontierD.FiniteProductExceptions



namespace StatMech.FrontierD

noncomputable section




theorem fkRectWindingBlockColumn_attachment_mul_connector_sq_mul_bulk_pow_le_auxiliary
    (k scale blocks right : Nat) (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right)
    {q a b c : Real} (hq : 1 <= q)
    (ha : 0 < a) (ha1 : a <= 1)
    (hb : 0 < b) (hb1 : b <= 1)
    (hattachment : c <=
      fkRectCriticalEventMass
        (fkRectWindingBlockVerticalFamily k scale blocks) q
        (fkRectUnitAttachmentOpenEvent
          (fkRectWindingBlockVerticalFamily k scale blocks)))
    (hbulk : ∀ xy ∈ fkRectWindingBlockColumnBulkPairs
        k scale blocks right x hxleft hxright,
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectColumnBand
            (fkRectWindingBlockVerticalFamily k scale blocks)
            1 right 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hconnector : ∀ xy ∈ fkRectWindingBlockColumnConnectorPairs
        k scale blocks right hright x hxleft hxright,
      b <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectColumnBand
            (fkRectWindingBlockVerticalFamily k scale blocks)
            1 right 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    c * b ^ 2 * a ^ (blocks + 1) <=
      fkRectCriticalEventMass
        (fkRectWindingBlockVerticalFamily k scale blocks) q
        (fkRectUnitDualBarrierAuxiliary
          (fkRectWindingBlockVerticalFamily k scale blocks) right
          (fkRectWindingBlockColumnAuxiliaryPairs
            k scale blocks right hright x hxleft hxright)) := by
  classical
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let S := fkRectColumnBand R 1 right 1 (R.height - 1)
  let G := fkRectInducedGraph R S
  let F := fun xy : FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
      FKRectColumnBandVertex R 1 right 1 (R.height - 1) =>
    FK.twoPointFun G (fkRectCriticalP q) q xy.1 xy.2
  let bulk := fkRectWindingBlockColumnBulkPairs
    k scale blocks right x hxleft hxright
  let connector := fkRectWindingBlockColumnConnectorPairs
    k scale blocks right hright x hxleft hxright
  let t := fkRectWindingBlockColumnAuxiliaryPairs
    k scale blocks right hright x hxleft hxright
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hFnonneg : ∀ xy, 0 <= F xy := by
    intro xy
    exact FK.twoPointFun_nonneg G hp hp1 hq0 xy.1 xy.2
  have hFleOne : ∀ xy, F xy <= 1 := by
    intro xy
    exact FK.twoPointFun_le_one G hp hp1 hq0 xy.1 xy.2
  have hbulkProd : a ^ bulk.card <= ∏ xy ∈ bulk, F xy := by
    rw [show a ^ bulk.card = ∏ _xy ∈ bulk, a by simp]
    apply Finset.prod_le_prod (fun _ _ => ha.le)
    intro xy hxy
    exact hbulk xy hxy
  have hbulkPow : a ^ (blocks + 1) <= a ^ bulk.card := by
    apply pow_le_pow_of_le_one ha.le ha1
    exact connectionPathPairs_card_le _ _
  have hconnectorProd : b ^ connector.card <=
      ∏ xy ∈ connector, F xy := by
    rw [show b ^ connector.card = ∏ _xy ∈ connector, b by simp]
    apply Finset.prod_le_prod (fun _ _ => hb.le)
    intro xy hxy
    exact hconnector xy hxy
  have hconnectorCard : connector.card <= 2 := by
    apply (Finset.card_insert_le _ _).trans
    rw [Finset.card_singleton]
  have hconnectorPow : b ^ 2 <= b ^ connector.card :=
    pow_le_pow_of_le_one hb.le hb1 hconnectorCard
  have hinterLeOne : (∏ xy ∈ bulk ∩ connector, F xy) <= 1 := by
    calc
      (∏ xy ∈ bulk ∩ connector, F xy) <=
          ∏ _xy ∈ bulk ∩ connector, (1 : Real) := by
        apply Finset.prod_le_prod
        · intro xy _
          exact hFnonneg xy
        · intro xy _
          exact hFleOne xy
      _ = 1 := by simp
  have htNonneg : 0 <= ∏ xy ∈ t, F xy :=
    Finset.prod_nonneg fun xy _ => hFnonneg xy
  have hunion : bulk ∪ connector = t := by
    rfl
  have hmerge :
      (∏ xy ∈ bulk, F xy) * (∏ xy ∈ connector, F xy) <=
        ∏ xy ∈ t, F xy := by
    rw [← hunion, ← Finset.prod_union_inter]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun xy _ => hFnonneg xy) hinterLeOne
  have hproduct : b ^ 2 * a ^ (blocks + 1) <= ∏ xy ∈ t, F xy := by
    calc
      b ^ 2 * a ^ (blocks + 1) <=
          b ^ connector.card * a ^ bulk.card :=
        mul_le_mul hconnectorPow hbulkPow
          (pow_nonneg ha.le _) (pow_nonneg hb.le _)
      _ <= (∏ xy ∈ connector, F xy) * (∏ xy ∈ bulk, F xy) :=
        mul_le_mul hconnectorProd hbulkProd
          (pow_nonneg ha.le _)
          (Finset.prod_nonneg fun xy _ => hFnonneg xy)
      _ = (∏ xy ∈ bulk, F xy) * (∏ xy ∈ connector, F xy) := by
        ring
      _ <= ∏ xy ∈ t, F xy := hmerge
  have hmassNonneg : 0 <= fkRectCriticalEventMass R q
      (fkRectUnitAttachmentOpenEvent R) :=
    fkRectCriticalEventMass_nonneg R hq0 _
  calc
    c * b ^ 2 * a ^ (blocks + 1) =
        c * (b ^ 2 * a ^ (blocks + 1)) := by ring
    _ <= fkRectCriticalEventMass R q
          (fkRectUnitAttachmentOpenEvent R) *
        (b ^ 2 * a ^ (blocks + 1)) :=
      mul_le_mul_of_nonneg_right hattachment
        (mul_nonneg (pow_nonneg hb.le _) (pow_nonneg ha.le _))
    _ <= fkRectCriticalEventMass R q
          (fkRectUnitAttachmentOpenEvent R) *
        (∏ xy ∈ t, F xy) :=
      mul_le_mul_of_nonneg_left hproduct hmassNonneg
    _ = (∏ xy ∈ t, F xy) *
          fkRectCriticalEventMass R q
            (fkRectUnitAttachmentOpenEvent R) := by ring
    _ <= fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R right t) :=
      fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary
        R right hq t

end

end StatMech.FrontierD
