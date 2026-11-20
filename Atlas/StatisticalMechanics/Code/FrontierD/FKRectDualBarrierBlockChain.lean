/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierAuxiliary
import Code.FrontierD.FKRectWindingBlockSource



namespace StatMech.FrontierD

noncomputable section



def fkRectWindingBlockColumnPathVertex
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right)
    (i : Fin (blocks + 2)) :
    FKRectColumnBandVertex
      (fkRectWindingBlockVerticalFamily k scale blocks)
      1 right 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  let v := fkRectWindingBlockPathVertex k scale blocks 1 x hxleft i
  exact ⟨v.1, ⟨v.2.1, hxright, v.2.2.1, v.2.2.2⟩⟩

theorem fkRectWindingBlockColumnPathVertex_first
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    fkRectWindingBlockColumnPathVertex k scale blocks right x
        hxleft hxright 0 =
      fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright := by
  apply Subtype.ext
  change (fkRectWindingBlockPathVertex
      k scale blocks 1 x hxleft 0).1 =
    (fkRectRightBandRowOne
      (fkRectWindingBlockVerticalFamily k scale blocks) 1 x hxleft).1
  exact congrArg Subtype.val
    (fkRectWindingBlockPathVertex_first k scale blocks 1 x hxleft)

theorem fkRectWindingBlockColumnPathVertex_last
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    fkRectWindingBlockColumnPathVertex k scale blocks right x
        hxleft hxright (Fin.last (blocks + 1)) =
      fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright := by
  apply Subtype.ext
  change (fkRectWindingBlockPathVertex
      k scale blocks 1 x hxleft (Fin.last (blocks + 1))).1 =
    (fkRectRightBandLastRow
      (fkRectWindingBlockVerticalFamily k scale blocks) 1 x hxleft).1
  exact congrArg Subtype.val
    (fkRectWindingBlockPathVertex_last k scale blocks 1 x hxleft)


def fkRectWindingBlockColumnBulkPairs
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :=
  connectionPathPairs (blocks + 1)
    (fkRectWindingBlockColumnPathVertex k scale blocks right x
      hxleft hxright)



def fkRectWindingBlockColumnConnectorPairs
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    Finset
      (FKRectColumnBandVertex
          (fkRectWindingBlockVerticalFamily k scale blocks)
          1 right 1
          ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) ×
        FKRectColumnBandVertex
          (fkRectWindingBlockVerticalFamily k scale blocks)
          1 right 1
          ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)) :=
  { (fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right
        (fkRectUnitGapColumn
          (fkRectWindingBlockVerticalFamily k scale blocks))
        (by rfl) hright,
      fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright),
    (fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright,
      fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right
        (fkRectUnitGapColumn
          (fkRectWindingBlockVerticalFamily k scale blocks))
        (by rfl) hright) }


def fkRectWindingBlockColumnAuxiliaryPairs
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :=
  fkRectWindingBlockColumnBulkPairs k scale blocks right x hxleft hxright ∪
    fkRectWindingBlockColumnConnectorPairs k scale blocks right hright x
      hxleft hxright

theorem fkRectWindingBlockColumnAuxiliaryPairs_card_le
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    (fkRectWindingBlockColumnAuxiliaryPairs k scale blocks right hright x
      hxleft hxright).card <= blocks + 3 := by
  calc
    (fkRectWindingBlockColumnAuxiliaryPairs k scale blocks right hright x
      hxleft hxright).card <=
        (fkRectWindingBlockColumnBulkPairs k scale blocks right x
          hxleft hxright).card +
        (fkRectWindingBlockColumnConnectorPairs k scale blocks right hright x
          hxleft hxright).card := by
      exact Finset.card_union_le _ _
    _ <= (blocks + 1) + 2 := by
      apply Nat.add_le_add
      · exact connectionPathPairs_card_le _ _
      · simpa only [fkRectWindingBlockColumnConnectorPairs] using
          (Finset.card_le_two :
            ({(fkRectColumnBandRowOne
                  (fkRectWindingBlockVerticalFamily k scale blocks)
                  1 right
                  (fkRectUnitGapColumn
                    (fkRectWindingBlockVerticalFamily k scale blocks))
                  (by rfl) hright,
                fkRectColumnBandRowOne
                  (fkRectWindingBlockVerticalFamily k scale blocks)
                  1 right x hxleft hxright),
              (fkRectColumnBandLastRow
                  (fkRectWindingBlockVerticalFamily k scale blocks)
                  1 right x hxleft hxright,
                fkRectColumnBandLastRow
                  (fkRectWindingBlockVerticalFamily k scale blocks)
                  1 right
                  (fkRectUnitGapColumn
                    (fkRectWindingBlockVerticalFamily k scale blocks))
                  (by rfl) hright)} : Finset _).card <= 2)
    _ = blocks + 3 := by omega



theorem fkRectWindingBlockColumnAuxiliaryPairs_spans
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    FKRectColumnBandConnectionChainSpans
      (fkRectWindingBlockVerticalFamily k scale blocks)
      1 right
      (fkRectUnitGapColumn
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (by rfl) hright
      (fkRectWindingBlockColumnAuxiliaryPairs
        k scale blocks right hright x hxleft hxright) := by
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let v := fkRectWindingBlockColumnPathVertex
    k scale blocks right x hxleft hxright
  let bottomGap := fkRectColumnBandRowOne R 1 right
    (fkRectUnitGapColumn R) (by rfl) hright
  let topGap := fkRectColumnBandLastRow R 1 right
    (fkRectUnitGapColumn R) (by rfl) hright
  let bottomBulk := fkRectColumnBandRowOne R 1 right x hxleft hxright
  let topBulk := fkRectColumnBandLastRow R 1 right x hxleft hxright
  intro sigma hchain
  have hbottom :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 right 1 (R.height - 1))) sigma).Reachable
        bottomGap bottomBulk := by
    apply hchain (bottomGap, bottomBulk)
    apply Finset.mem_union_right
    apply Finset.mem_insert.mpr
    left
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  have hbulk :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 right 1 (R.height - 1))) sigma).Reachable
        bottomBulk topBulk := by
    have hspan := fkRectColumnBandConnectionChainSpans_connectionPathPairs
      R 1 right x hxleft hxright (blocks + 1) v
      (by
        dsimp [v, bottomBulk, R]
        exact fkRectWindingBlockColumnPathVertex_first
          k scale blocks right x hxleft hxright)
      (by
        dsimp [v, topBulk, R]
        exact fkRectWindingBlockColumnPathVertex_last
          k scale blocks right x hxleft hxright)
    apply hspan sigma
    intro pair hpair
    exact hchain pair (Finset.mem_union_left _ hpair)
  have htop :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 right 1 (R.height - 1))) sigma).Reachable
        topBulk topGap := by
    apply hchain (topBulk, topGap)
    apply Finset.mem_union_right
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_singleton.mpr
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  exact (hbottom.trans hbulk).trans htop

end

end StatMech.FrontierD
