/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectWindingOneThermodynamicBridge
import Code.FrontierD.FKQgt4DiagonalRate



namespace StatMech.FrontierD

noncomputable section

open Filter Topology



def fkRectWindingBlockVerticalFamily
    (k scale blocks : Nat) : FKRectTorus where
  width := 2 * (k + 3)
  height := 2 * (scale + 1) * (blocks + 1) + 2
  width_gt_two := by omega
  height_gt_two := by
    have h : 0 < 2 * (scale + 1) * (blocks + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  height_even := ⟨(scale + 1) * (blocks + 1) + 1, by ring⟩

@[simp] theorem fkRectWindingBlockVerticalFamily_width
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).width =
      2 * (k + 3) := rfl

@[simp] theorem fkRectWindingBlockVerticalFamily_height
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).height =
      2 * (scale + 1) * (blocks + 1) + 2 := rfl

@[simp] theorem fkRectWindingBlockVerticalFamily_medialWidth
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.width =
      sixVertexFourWidth 1 (k + 1) := by
  change 2 * (2 * (k + 3)) = 4 * (1 + (k + 1) + 1)
  omega

@[simp] theorem fkRectWindingBlockVerticalFamily_medialHeight
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.height =
      2 * (scale + 1) * (blocks + 1) + 2 := rfl


def fkRectWindingBlockPathVertex
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 2)) :
    FKRectRightStripBandVertex
      (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let row := 1 + 2 * (scale + 1) * i.val
  have hi : i.val <= blocks + 1 := by omega
  have hmul : 2 * (scale + 1) * i.val <=
      2 * (scale + 1) * (blocks + 1) :=
    Nat.mul_le_mul_left (2 * (scale + 1)) hi
  have hrow : row < R.height := by
    dsimp [row, R, fkRectWindingBlockVerticalFamily]
    omega
  let y : Fin R.height := ⟨row, hrow⟩
  refine ⟨(x, y), ?_⟩
  change cut <= x.val ∧ 1 <= row ∧ row <= R.height - 1
  refine ⟨hx, by omega, ?_⟩
  dsimp [row, R, fkRectWindingBlockVerticalFamily]
  omega

theorem fkRectWindingBlockPathVertex_first
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    fkRectWindingBlockPathVertex k scale blocks cut x hx 0 =
      fkRectRightBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change 1 = 1
    rfl

theorem fkRectWindingBlockPathVertex_last
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    fkRectWindingBlockPathVertex k scale blocks cut x hx
        (Fin.last (blocks + 1)) =
      fkRectRightBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change 1 + 2 * (scale + 1) * (blocks + 1) =
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1
    simp only [fkRectWindingBlockVerticalFamily_height]
    omega


theorem fkRectWindingBlockPathPairs_card_le
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    (connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card <=
        blocks + 1 :=
  connectionPathPairs_card_le _ _

theorem fkRectWindingBlockPath_pairMap_injective
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    Function.Injective (fun i : Fin (blocks + 1) =>
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc,
        fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)) := by
  intro i j hij
  have hrow := congrArg (fun pair => pair.1.1.2.val) hij
  change 1 + 2 * (scale + 1) * i.val =
    1 + 2 * (scale + 1) * j.val at hrow
  have hmul : 2 * (scale + 1) * i.val =
      2 * (scale + 1) * j.val := Nat.add_left_cancel hrow
  apply Fin.ext
  exact Nat.mul_left_cancel (by positivity) hmul

theorem fkRectWindingBlockPathPairs_card_eq
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    (connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card =
        blocks + 1 := by
  rw [connectionPathPairs, Finset.card_image_of_injective _
    (fkRectWindingBlockPath_pairMap_injective k scale blocks cut x hx)]
  simp

theorem mem_fkRectWindingBlockPathPairs_iff
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val)
    (xy : FKRectRightStripBandVertex
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) ×
      FKRectRightStripBandVertex
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)) :
    xy ∈ connectionPathPairs (blocks + 1)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx) ↔
      ∃ i : Fin (blocks + 1),
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc,
          fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) = xy := by
  rw [connectionPathPairs, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hxy⟩
    exact ⟨i, hxy⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ _, rfl⟩



theorem fkRectWindingBlockPathVertex_squarePoint_step
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 1)) :
    fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ).1 -
      fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1 =
      (((scale + 1 : Nat) : Int), -((scale + 1 : Nat) : Int)) := by
  apply Prod.ext
  · simp [fkRectVertexSquarePoint, fkRectWindingBlockPathVertex,
      fkRectSquareDevelopPoint]
    rw [show (1 : Int) + 2 * (scale + 1) * (i.val + 1) + 1 =
          2 * ((scale + 1) * (i.val + 1) + 1) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num),
      show (1 : Int) + 2 * (scale + 1) * i.val + 1 =
          2 * ((scale + 1) * i.val + 1) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  · simp [fkRectVertexSquarePoint, fkRectWindingBlockPathVertex,
      fkRectSquareDevelopPoint]
    have hodd (z : Int) : (1 + 2 * z) / 2 = z := by omega
    have hcur :
        ((1 : Int) + 2 * (scale + 1) * i.val) / 2 =
          (scale + 1) * i.val := by
      convert hodd ((scale + 1) * i.val) using 1 <;> ring
    have hnext :
        ((1 : Int) + 2 * (scale + 1) * (i.val + 1)) / 2 =
          (scale + 1) * (i.val + 1) := by
      convert hodd ((scale + 1) * (i.val + 1)) using 1 <;> ring
    rw [hcur, hnext]
    ring




noncomputable def fkRectWindingBlockSource
    (k scale blocks leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (q a : Real) (ha : 0 < a)
    (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx),
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    FKRectWindingOneSource
      (fkRectWindingBlockVerticalFamily k scale blocks) q :=
  fkRectPathWindingOneSource
    (fkRectWindingBlockVerticalFamily k scale blocks) q leftRight cut
    hone hsep hleft x hx (blocks + 1)
    (fkRectWindingBlockPathVertex k scale blocks cut x hx)
    (fkRectWindingBlockPathVertex_first k scale blocks cut x hx)
    (fkRectWindingBlockPathVertex_last k scale blocks cut x hx)
    (by
      intro xy hxy
      apply reachable_of_twoPointFun_pos
      exact ha.trans_le (hlower xy hxy))

@[simp] theorem fkRectWindingBlockSource_pairs
    (k scale blocks leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (q a : Real) (ha : 0 < a)
    (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx),
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    (fkRectWindingBlockSource k scale blocks leftRight cut hone hsep
      hleft x hx q a ha hlower).pairs =
      connectionPathPairs (blocks + 1)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx) := rfl



theorem fkRectWindingBlockSource_connectionProduct_negLogRate_le
    (k scale blocks leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) {q a : Real} (ha : 0 < a) (ha1 : a <= 1)
    (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx),
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log (fkRectWindingBlockSource k scale blocks leftRight cut
        hone hsep hleft x hx q a ha hlower).connectionProduct /
        (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      ((blocks + 1 : Nat) : Real) * (-Real.log a) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height := by
  apply FKRectWindingOneSource.connectionProduct_negLogRate_le_of_card
  · simpa using fkRectWindingBlockPathPairs_card_le
      k scale blocks cut x hx
  · exact ha
  · exact ha1
  · simpa using hlower



theorem fkRectWindingBlockSource_windingOne_negLogRate_le
    (k scale blocks leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) {q a : Real} (hq : 1 <= q)
    (ha : 0 < a) (ha1 : a <= 1)
    (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx),
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log (fkRectCriticalWindingOneMass
        (fkRectWindingBlockVerticalFamily k scale blocks) q) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      ((blocks + 1 : Nat) : Real) * (-Real.log a) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height +
        -Real.log (fkRectWindingBlockSource k scale blocks leftRight cut
          hone hsep hleft x hx q a ha hlower).barrierMass /
          (fkRectWindingBlockVerticalFamily k scale blocks).height +
        -Real.log (FK.cFE (fkRectCriticalP q) q) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height := by
  have hsource :=
    (fkRectWindingBlockSource k scale blocks leftRight cut hone hsep
      hleft x hx q a ha hlower).windingOne_negLogRate_le hq
  have hconnection :=
    fkRectWindingBlockSource_connectionProduct_negLogRate_le
      k scale blocks leftRight cut hone hsep hleft x hx ha ha1 hlower
  linarith


theorem tendsto_fkRectWindingBlockVerticalFamily_height
    (k scale : Nat) :
    Tendsto (fun blocks =>
      (fkRectWindingBlockVerticalFamily k scale blocks).height)
      atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with blocks hblocks
  simp only [fkRectWindingBlockVerticalFamily_height]
  have hmul : blocks + 1 <= 2 * (scale + 1) * (blocks + 1) :=
    Nat.le_mul_of_pos_left (blocks + 1) (by positivity)
  omega



theorem fkRectWindingBlock_count_div_height_tendsto
    (k scale : Nat) :
    Tendsto (fun blocks : Nat =>
      ((blocks + 1 : Nat) : Real) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height)
      atTop (nhds (1 / (2 * (scale + 1) : Real))) := by
  have hn : Tendsto (fun blocks : Nat => ((blocks + 1 : Nat) : Real))
      atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto (fun blocks : Nat =>
      (2 : Real) / ((blocks + 1 : Nat) : Real)) atTop (nhds 0) :=
    hn.const_div_atTop 2
  have hsum : Tendsto (fun blocks : Nat =>
      (2 * (scale + 1) : Real) +
        2 / ((blocks + 1 : Nat) : Real)) atTop
      (nhds (2 * (scale + 1) : Real)) := by
    simpa using (tendsto_const_nhds.add hsmall)
  have hinv := hsum.inv₀ (by positivity : (2 * (scale + 1) : Real) ≠ 0)
  rw [one_div]
  apply hinv.congr'
  filter_upwards [] with blocks
  simp only [fkRectWindingBlockVerticalFamily_height,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  <;> ring



theorem fkRectWindingBlock_vertical_negLogRatio_tendsto
    {c : Real} (hc : 0 < c) (k scale : Nat) :
    Tendsto (fun blocks =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus
                1 (by
                  rw [fkRectWindingBlockVerticalFamily_medialWidth]
                  exact sixVertexFourWidth_charge_le 1 (k + 1)) c /
            sixVertexTorusFixedChargePartitionSum
                (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus
                0 (Nat.zero_le _) c) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height)
      atTop (nhds (-sixVertexFixedChargeLogRatio c 1 (k + 1))) := by
  have hindex := tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have h := (sixVertexFixedChargeTraceLogRatio_div_height_tendsto
    hc 1 (k + 1)).comp hindex
  have hneg := h.neg
  apply hneg.congr'
  filter_upwards [] with blocks
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace,
    sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
  rw [fkRectWindingBlockVerticalFamily_medialWidth]
  simp only [fkRectWindingBlockVerticalFamily_medialHeight,
    fkRectWindingBlockVerticalFamily_height, Function.comp_apply,
    Nat.sub_zero, neg_div]



theorem fkRectWindingBlock_chargeOneRate_le_windingOneEventualUpper
    {q windingUpper : Real} (hq : 4 < q) (k scale : Nat)
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        windingUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
  let R : Nat -> FKRectTorus := fkRectWindingBlockVerticalFamily k scale
  have hheightNat : Tendsto (fun blocks => (R blocks).height) atTop atTop :=
    tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have hheight : Tendsto (fun blocks => ((R blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  apply chargeOneRate_le_of_windingOne_eventualUpper R hq
    (fun blocks => fkRectCriticalWindingOneMass_pos _ (by linarith))
    hheight
  · simpa [R] using fkRectWindingBlock_vertical_negLogRatio_tendsto
      (show 0 < fkQgt4SixVertexWeight q by
        linarith [two_lt_fkQgt4SixVertexWeight hq]) k scale
  · intro epsilon hepsilon
    simpa [R] using hwind epsilon hepsilon




theorem fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper
    {q sourceUpper : Real} (hq : 4 < q) (k scale : Nat)
    (source : forall blocks,
      FKRectWindingOneSource
        (fkRectWindingBlockVerticalFamily k scale blocks) q)
    (hsourceCost : forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ blocks in atTop,
        -Real.log (source blocks).connectionProduct /
              (fkRectWindingBlockVerticalFamily k scale blocks).height +
            -Real.log (source blocks).barrierMass /
              (fkRectWindingBlockVerticalFamily k scale blocks).height <=
          sourceUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= sourceUpper := by
  apply fkRectWindingBlock_chargeOneRate_le_windingOneEventualUpper
    hq k scale
  intro epsilon hepsilon
  let R : Nat -> FKRectTorus := fkRectWindingBlockVerticalFamily k scale
  let c : Real := FK.cFE (fkRectCriticalP q) q
  let error : Nat -> Real := fun blocks =>
    -Real.log c / ((R blocks).height : Real)
  have hheightNat : Tendsto (fun blocks => (R blocks).height) atTop atTop :=
    tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have hheight : Tendsto (fun blocks => ((R blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  have herror : Tendsto error atTop (nhds 0) :=
    hheight.const_div_atTop (-Real.log c)
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have herr : ∀ᶠ blocks in atTop, error blocks < delta :=
    (tendsto_order.1 herror).2 delta hdelta
  filter_upwards [hsourceCost delta hdelta, herr] with blocks hcost herr
  have hfinite := (source blocks).windingOne_negLogRate_le
    (by linarith : 1 <= q)
  simp only [fkRectWindingBlockVerticalFamily_height] at hfinite
  dsimp [R, error, c, delta] at herr hcost
  change -Real.log (fkRectCriticalWindingOneMass
      (fkRectWindingBlockVerticalFamily k scale blocks) q) /
      ((2 * (scale + 1) * (blocks + 1) + 2 : Nat) : Real) <=
    sourceUpper + epsilon
  linarith




theorem fkRectWindingBlock_chargeOneRate_le_productPowAndBarrier
    {q a C barrierUpper : Real} (hq : 4 < q) (ha : 0 < a) (hC : 0 < C)
    (k scale : Nat)
    (source : forall blocks,
      FKRectWindingOneSource
        (fkRectWindingBlockVerticalFamily k scale blocks) q)
    (hproduct : forall blocks,
      C * a ^ (blocks + 1) <= (source blocks).connectionProduct)
    (hbarrier : forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ blocks in atTop,
        -Real.log (source blocks).barrierMass /
            (fkRectWindingBlockVerticalFamily k scale blocks).height <=
          barrierUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <=
      -Real.log a / (2 * (scale + 1) : Real) + barrierUpper := by
  apply fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper
    hq k scale source
  intro epsilon hepsilon
  let blockCost : Nat -> Real := fun blocks =>
    ((blocks + 1 : Nat) : Real) * (-Real.log a) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  let prefactorCost : Nat -> Real := fun blocks =>
    (-Real.log C) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  have hblock : Tendsto blockCost atTop
      (nhds (-Real.log a / (2 * (scale + 1) : Real))) := by
    have h := (fkRectWindingBlock_count_div_height_tendsto k scale).mul_const
      (-Real.log a)
    convert h using 1
    · funext blocks
      simp only [blockCost, fkRectWindingBlockVerticalFamily_height,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · ring
  have hheightNat := tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have hheight : Tendsto (fun blocks =>
      ((fkRectWindingBlockVerticalFamily k scale blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  have hprefactor : Tendsto prefactorCost atTop (nhds 0) :=
    hheight.const_div_atTop (-Real.log C)
  have hconnection := hblock.add hprefactor
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hconnectionUpper : ∀ᶠ blocks in atTop,
      blockCost blocks + prefactorCost blocks <
        -Real.log a / (2 * (scale + 1) : Real) + delta :=
    (tendsto_order.1 hconnection).2 _ (by linarith)
  filter_upwards [hconnectionUpper, hbarrier delta hdelta] with
    blocks hconn hbar
  have hproductCost :=
    (source blocks).connectionProduct_negLogRate_le_of_mul_pow
      (blocks + 1) hC ha (hproduct blocks)
  have hproductCost' :
      -Real.log (source blocks).connectionProduct /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        blockCost blocks + prefactorCost blocks := by
    calc
      _ <= (((blocks + 1 : Nat) : Real) * (-Real.log a) +
          (-Real.log C)) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height :=
        hproductCost
      _ = _ := by
        dsimp [blockCost, prefactorCost]
        ring
  change -Real.log (source blocks).connectionProduct /
          (fkRectWindingBlockVerticalFamily k scale blocks).height +
        -Real.log (source blocks).barrierMass /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      -Real.log a / (2 * (scale + 1) : Real) + barrierUpper + epsilon
  dsimp [delta] at hbar hconn
  simp only [fkRectWindingBlockVerticalFamily_height] at hproductCost' ⊢
  linarith [hproductCost']




theorem fkRectWindingBlock_chargeOneRate_le_blockAndBarrier
    {q a barrierUpper : Real} (hq : 4 < q) (ha : 0 < a) (ha1 : a <= 1)
    (k scale leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < 2 * (k + 3))
    (x : Fin (2 * (k + 3))) (hx : cut <= x.val)
    (hblock : forall blocks,
      ∀ xy ∈ connectionPathPairs (blocks + 1)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx),
        a <= FK.twoPointFun
          (fkRectInducedGraph
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectRightStripBand
              (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
              ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2)
    (hbarrier : forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ blocks in atTop,
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks)
                leftRight
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
            (fkRectWindingBlockVerticalFamily k scale blocks).height <=
          barrierUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <=
      -Real.log a / (2 * (scale + 1) : Real) + barrierUpper := by
  let source : forall blocks,
      FKRectWindingOneSource
        (fkRectWindingBlockVerticalFamily k scale blocks) q := fun blocks =>
    fkRectWindingBlockSource k scale blocks leftRight cut hone hsep hleft
      x hx q a ha (hblock blocks)
  apply fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper
    hq k scale source
  intro epsilon hepsilon
  let connectionUpper : Real :=
    -Real.log a / (2 * (scale + 1) : Real)
  let connectionCost : Nat -> Real := fun blocks =>
    ((blocks + 1 : Nat) : Real) * (-Real.log a) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  have hconnection : Tendsto connectionCost atTop (nhds connectionUpper) := by
    have h := (fkRectWindingBlock_count_div_height_tendsto k scale).mul_const
      (-Real.log a)
    convert h using 1
    · funext blocks
      simp only [connectionCost, fkRectWindingBlockVerticalFamily_height,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · dsimp [connectionUpper]
      ring
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hconnectionUpper : ∀ᶠ blocks in atTop,
      connectionCost blocks < connectionUpper + delta :=
    (tendsto_order.1 hconnection).2 _ (by linarith)
  filter_upwards [hconnectionUpper, hbarrier delta hdelta] with
    blocks hconn hbar
  have hproduct :=
    fkRectWindingBlockSource_connectionProduct_negLogRate_le
      k scale blocks leftRight cut hone hsep hleft x hx ha ha1
      (hblock blocks)
  change -Real.log (source blocks).connectionProduct /
      (fkRectWindingBlockVerticalFamily k scale blocks).height <=
    connectionCost blocks at hproduct
  change -Real.log (source blocks).connectionProduct /
          (fkRectWindingBlockVerticalFamily k scale blocks).height +
        -Real.log (source blocks).barrierMass /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      -Real.log a / (2 * (scale + 1) : Real) + barrierUpper + epsilon
  change -Real.log (source blocks).connectionProduct /
          (fkRectWindingBlockVerticalFamily k scale blocks).height +
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks)
                leftRight
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      -Real.log a / (2 * (scale + 1) : Real) + barrierUpper + epsilon
  dsimp [connectionCost, connectionUpper, delta] at hconn
  dsimp [connectionCost] at hproduct
  dsimp [delta] at hbar
  simp only [fkRectWindingBlockVerticalFamily_height] at hproduct hbar ⊢
  linarith



theorem fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds
    {q upper : Real} (hq : 4 < q)
    (hbound : ∀ᶠ k in atTop,
      -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) 1 (k + 1) <= upper) :
    fkQgt4SixVertexGapRate q <= upper := by
  have hle : ((1 : Nat) : Real) * fkQgt4SixVertexGapRate q <= upper :=
    le_of_tendsto
      (tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq 1 (by omega))
      hbound
  simpa using hle



theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds
    {q : Real} (hq : 4 < q) (barrierUpper : Nat -> Real)
    (hbarrier : Tendsto barrierUpper atTop (nhds 0))
    (hscale : forall scale,
      fkQgt4SixVertexGapRate q <=
        -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
            (2 * (scale + 1) : Real) + barrierUpper scale) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  have hdiag := (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).comp
    (tendsto_add_atTop_nat 1)
  have hhalf : Tendsto (fun scale =>
      -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
        (2 * (scale + 1) : Real)) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
    have h := hdiag.div_const 2
    apply h.congr'
    filter_upwards [] with scale
    simp only [Function.comp_apply]
    push_cast
    field_simp
  have htotal := hhalf.add hbarrier
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds htotal
    (Filter.Eventually.of_forall hscale)
  simpa using hle





theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_blockBounds
    {q : Real} (hq : 4 < q) (barrierUpper : Nat -> Real)
    (hbarrier : Tendsto barrierUpper atTop (nhds 0))
    (hcharge : forall scale,
      ∀ᶠ k in atTop,
        -sixVertexFixedChargeLogRatio
            (fkQgt4SixVertexWeight q) 1 (k + 1) <=
          -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
              (2 * (scale + 1) : Real) + barrierUpper scale) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds
    hq barrierUpper hbarrier
  intro scale
  exact fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds
    hq (hcharge scale)

end

end StatMech.FrontierD
