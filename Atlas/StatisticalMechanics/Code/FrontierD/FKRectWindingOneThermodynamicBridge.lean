/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectWindingOneResidualLower
import Code.FrontierD.FKRectBalancedSectorThermodynamicBridge
import Code.FrontierD.FKRectUnitLeftBarrier
import Code.FrontierD.FKRectSourceChainWindingUpper



open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def fkRectCriticalWindingOneMass (R : FKRectTorus) (q : Real) : Real :=
  fkRectCriticalEventMass R q
    {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}



theorem fkRectCriticalEventMass_pos_of_mem
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) (omega : R.Configuration) (homega : omega ∈ A) :
    0 < fkRectCriticalEventMass R q A := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_pos'
  · intro eta heta
    exact Set.indicator_nonneg
      (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _
  · refine ⟨omega, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem homega]
    unfold fkRectCriticalRandomClusterProb
    exact div_pos (fkRectCriticalReducedWeight_pos R hq omega)
      (fkRectCriticalReducedZ_pos R hq)



theorem fkRectRightBand_distinguished_reachable
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut <= x.val) :
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
        (fkRectRightBandRowOne R cut x hx)
        (fkRectRightBandLastRow R cut x hx) := by
  have hheight : 2 < R.height := R.height_gt_two
  have hxlt : x.val < R.width := x.isLt
  let v (n : Nat) (hn1 : 1 <= n) (hnH : n < R.height) :
      FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
    ⟨(x, ⟨n, hnH⟩), by
      change cut <= x.val ∧ 1 <= n ∧ n <= R.height - 1
      omega⟩
  have hreach : forall n (hn1 : 1 <= n) (hnH : n < R.height),
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
          (v 1 le_rfl (by omega)) (v n hn1 hnH) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        intro hn1 hnH
        by_cases hn0 : n = 0
        · subst n
          exact SimpleGraph.Reachable.refl _
        · have hn1' : 1 <= n := by omega
          have hnH' : n < R.height := by omega
          have hprev := ih hn1' hnH'
          have hpred : SixVertexArrows.cyclicPred R.height_pos
              (⟨n + 1, hnH⟩ : Fin R.height) =
              (⟨n, hnH'⟩ : Fin R.height) := by
            apply Fin.ext
            rw [fkRectCyclicPred_val]
            simp only [if_neg (by omega : n + 1 ≠ 0)]
            omega
          have hadj : (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1))).Adj
              (v n hn1' hnH') (v (n + 1) hn1 hnH) := by
            change (fkRectTorusGraph R).Adj
              (x, (⟨n, hnH'⟩ : Fin R.height))
              (x, (⟨n + 1, hnH⟩ : Fin R.height))
            simpa [hpred] using
              (fkRectTorusGraph_adj_verticalPred R x
                (⟨n + 1, hnH⟩ : Fin R.height)).symm
          exact hprev.trans hadj.reachable
  have hlast := hreach (R.height - 1) (by omega) (by omega)
  have hstart : v 1 le_rfl (by omega) =
      fkRectRightBandRowOne R cut x hx := by
    apply Subtype.ext
    rfl
  have hend : v (R.height - 1) (by omega) (by omega) =
      fkRectRightBandLastRow R cut x hx := by
    apply Subtype.ext
    rfl
  rwa [hstart, hend] at hlast



theorem fkRectRightBandConnectionProduct_pos
    (R : FKRectTorus) (cut : Nat) {q : Real} (hq : 0 < q)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hreaches : ∀ xy ∈ t,
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable xy.1 xy.2) :
    0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2 := by
  apply Finset.prod_pos
  intro xy hxy
  exact FK.twoPointFun_pos_of_reachable
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1)))
    (fkRectCriticalP_pos hq) (fkRectCriticalP_lt_one hq) hq
    (hreaches xy hxy)



theorem fkRectCriticalWindingOneMass_pos_of_source
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
    (hproduct : 0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hbarrier : 0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R leftRight gap)) :
    0 < fkRectCriticalWindingOneMass R q := by
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hlower :=
    fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans
      R leftRight cut hsep hleft hq hgap x hx hchosen t hspans
  unfold fkRectCriticalWindingOneMass
  exact (mul_pos (mul_pos hc hproduct) hbarrier).trans_le hlower




theorem windingOne_negLogRate_le_source_cost
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
    (hproduct : 0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hbarrier : 0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R leftRight gap)) :
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
      -Real.log (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) / R.height +
        -Real.log (fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap)) / R.height +
        -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
  let P : Real := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  let B : Real := fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R leftRight gap)
  let c : Real := FK.cFE (fkRectCriticalP q) q
  have hc : 0 < c := by
    dsimp [c]
    exact FK.cFE_pos
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hmass : 0 < fkRectCriticalWindingOneMass R q :=
    fkRectCriticalWindingOneMass_pos_of_source R leftRight cut hsep hleft
      hq hgap x hx hchosen t hspans hproduct hbarrier
  have hlower : c * P * B <= fkRectCriticalWindingOneMass R q := by
    simpa [c, P, B, fkRectCriticalWindingOneMass] using
      (fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans
        R leftRight cut hsep hleft hq hgap x hx hchosen t hspans)
  have hlog := Real.log_le_log (mul_pos (mul_pos hc hproduct) hbarrier) hlower
  rw [Real.log_mul (mul_pos hc hproduct).ne' hbarrier.ne',
    Real.log_mul hc.ne' hproduct.ne'] at hlog
  have hnum : -Real.log (fkRectCriticalWindingOneMass R q) <=
      -Real.log P + -Real.log B + -Real.log c := by
    linarith
  have hh : 0 <= (R.height : Real) := by positivity
  calc
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
        (-Real.log P + -Real.log B + -Real.log c) / R.height :=
      div_le_div_of_nonneg_right hnum hh
    _ = -Real.log P / R.height + -Real.log B / R.height +
        -Real.log c / R.height := by ring
    _ = _ := by rfl




structure FKRectWindingOneSource (R : FKRectTorus) (q : Real) where
  leftRight : Nat
  cut : Nat
  sep : leftRight < cut
  left : leftRight + 1 < R.width
  gap : R.EdgeIndex
  gap_mem : gap ∈ fkRectHorizontalCutEdges R
  x : Fin R.width
  x_right : cut <= x.val
  chosen : fkRectVerticalSeamEdgeAt R x ≠ gap
  pairs : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
    FKRectRightStripBandVertex R cut 1 (R.height - 1))
  chain_spans :
    FKRectRightBandConnectionChainSpans R cut x x_right pairs
  pair_reachable : ∀ xy ∈ pairs,
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable xy.1 xy.2
  barrierConfiguration : R.Configuration
  barrier_mem : barrierConfiguration ∈
    fkRectSourceLeftBarrier R leftRight gap



noncomputable def fkRectUnitWindingOneSource
    (R : FKRectTorus) (q : Real) : FKRectWindingOneSource R q := by
  let x : Fin R.width := ⟨2, R.width_gt_two⟩
  let hx : 2 <= x.val := le_rfl
  let pair :=
    (fkRectRightBandRowOne R 2 x hx,
      fkRectRightBandLastRow R 2 x hx)
  refine
    { leftRight := 1
      cut := 2
      sep := by omega
      left := R.width_gt_two
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := {pair}
      chain_spans := by
        apply fkRectRightBandConnectionChainSpans_of_pair_mem
        simp [pair]
      pair_reachable := ?_
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source R }
  · intro h
    have hdir := congrArg Prod.fst h
    simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir
  · intro xy hxy
    have hxyEq : xy = pair := by simpa using hxy
    subst xy
    exact fkRectRightBand_distinguished_reachable R 2 x hx



noncomputable def fkRectStraightWindingOneSource
    (R : FKRectTorus) (q : Real) (leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width) (hcut : cut < R.width) :
    FKRectWindingOneSource R q := by
  let x : Fin R.width := ⟨cut, hcut⟩
  let hx : cut <= x.val := le_rfl
  let pair :=
    (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx)
  refine
    { leftRight := leftRight
      cut := cut
      sep := hsep
      left := hleft
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := {pair}
      chain_spans := by
        apply fkRectRightBandConnectionChainSpans_of_pair_mem
        simp [pair]
      pair_reachable := ?_
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft }
  · intro h
    have hdir := congrArg Prod.fst h
    simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir
  · intro xy hxy
    have hxyEq : xy = pair := by simpa using hxy
    subst xy
    exact fkRectRightBand_distinguished_reachable R cut x hx




noncomputable def fkRectPathWindingOneSource
    (R : FKRectTorus) (q : Real) (leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    (x : Fin R.width) (hx : cut <= x.val) (n : Nat)
    (v : Fin (n + 1) ->
      FKRectRightStripBandVertex R cut 1 (R.height - 1))
    (hfirst : v 0 = fkRectRightBandRowOne R cut x hx)
    (hlast : v (Fin.last n) = fkRectRightBandLastRow R cut x hx)
    (hreaches : ∀ xy ∈ connectionPathPairs n v,
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
          xy.1 xy.2) :
    FKRectWindingOneSource R q := by
  refine
    { leftRight := leftRight
      cut := cut
      sep := hsep
      left := hleft
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := connectionPathPairs n v
      chain_spans :=
        fkRectRightBandConnectionChainSpans_connectionPathPairs
          R cut x hx n v hfirst hlast
      pair_reachable := hreaches
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft }
  intro h
  have hdir := congrArg Prod.fst h
  simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir

noncomputable def FKRectWindingOneSource.connectionProduct
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q) : Real :=
  ∏ xy ∈ source.pairs,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R source.cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2

noncomputable def FKRectWindingOneSource.barrierMass
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q) : Real :=
  fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R source.leftRight source.gap)

theorem FKRectWindingOneSource.connectionProduct_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 0 < q) :
    0 < source.connectionProduct := by
  exact fkRectRightBandConnectionProduct_pos R source.cut hq source.pairs
    source.pair_reachable



theorem FKRectWindingOneSource.connectionProduct_negLogRate_le
    {R : FKRectTorus} {q a : Real} (source : FKRectWindingOneSource R q)
    (ha : 0 < a)
    (hlower : ∀ xy ∈ source.pairs, a <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R source.cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log source.connectionProduct / R.height <=
      (source.pairs.card : Real) * (-Real.log a) / R.height := by
  have hprod : a ^ source.pairs.card <= source.connectionProduct := by
    rw [show a ^ source.pairs.card = ∏ _xy ∈ source.pairs, a by simp]
    unfold FKRectWindingOneSource.connectionProduct
    exact Finset.prod_le_prod (fun _ _ => ha.le) hlower
  have hlog := Real.log_le_log (pow_pos ha _) hprod
  rw [Real.log_pow] at hlog
  have hnum : -Real.log source.connectionProduct <=
      (source.pairs.card : Real) * (-Real.log a) := by
    linarith
  exact div_le_div_of_nonneg_right hnum (by positivity)




theorem FKRectWindingOneSource.connectionProduct_negLogRate_le_of_mul_pow
    {R : FKRectTorus} {q C a : Real} (source : FKRectWindingOneSource R q)
    (n : Nat) (hC : 0 < C) (ha : 0 < a)
    (hlower : C * a ^ n <= source.connectionProduct) :
    -Real.log source.connectionProduct / R.height <=
      ((n : Real) * (-Real.log a) + (-Real.log C)) / R.height := by
  have hCa : 0 < C * a ^ n := mul_pos hC (pow_pos ha n)
  have hlog := Real.log_le_log hCa hlower
  rw [Real.log_mul hC.ne' (pow_pos ha n).ne', Real.log_pow] at hlog
  have hnum : -Real.log source.connectionProduct <=
      (n : Real) * (-Real.log a) + (-Real.log C) := by
    linarith
  exact div_le_div_of_nonneg_right hnum (by positivity)



theorem FKRectWindingOneSource.connectionProduct_negLogRate_le_of_card
    {R : FKRectTorus} {q a : Real} (source : FKRectWindingOneSource R q)
    (blocks : Nat) (hcard : source.pairs.card <= blocks)
    (ha : 0 < a) (ha1 : a <= 1)
    (hlower : ∀ xy ∈ source.pairs, a <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R source.cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log source.connectionProduct / R.height <=
      (blocks : Real) * (-Real.log a) / R.height := by
  have hbase := source.connectionProduct_negLogRate_le ha hlower
  have hcost : 0 <= -Real.log a := by
    linarith [Real.log_nonpos ha.le ha1]
  have hcardReal : (source.pairs.card : Real) <= blocks := by
    exact_mod_cast hcard
  have hmul : (source.pairs.card : Real) * (-Real.log a) <=
      (blocks : Real) * (-Real.log a) :=
    mul_le_mul_of_nonneg_right hcardReal hcost
  exact hbase.trans (div_le_div_of_nonneg_right hmul (by positivity))

theorem FKRectWindingOneSource.barrierMass_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 0 < q) :
    0 < source.barrierMass := by
  exact fkRectCriticalEventMass_pos_of_mem R hq _
    source.barrierConfiguration source.barrier_mem

theorem FKRectWindingOneSource.windingOneMass_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 1 <= q) :
    0 < fkRectCriticalWindingOneMass R q := by
  exact fkRectCriticalWindingOneMass_pos_of_source R
    source.leftRight source.cut source.sep source.left hq source.gap_mem
    source.x source.x_right source.chosen source.pairs
    source.chain_spans
    (source.connectionProduct_pos (zero_lt_one.trans_le hq))
    (source.barrierMass_pos (zero_lt_one.trans_le hq))



theorem fkRectCriticalWindingOneMass_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalWindingOneMass R q :=
  (fkRectUnitWindingOneSource R q).windingOneMass_pos hq

theorem fkRectSourceLeftBarrier_mass_pos_of_one_le
    (R : FKRectTorus) (right : Nat) (hone : 1 <= right)
    (hright : right + 1 < R.width) {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R right (fkRectUnitLeftBarrierGap R)) :=
  fkRectCriticalEventMass_pos_of_mem R hq _
    (fkRectUnitLeftBarrierConfiguration R)
    (fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
      R right hone hright)

theorem FKRectWindingOneSource.windingOne_negLogRate_le
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 1 <= q) :
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
      -Real.log source.connectionProduct / R.height +
        -Real.log source.barrierMass / R.height +
        -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
  exact windingOne_negLogRate_le_source_cost R
    source.leftRight source.cut source.sep source.left hq source.gap_mem
    source.x source.x_right source.chosen source.pairs
    source.chain_spans
    (source.connectionProduct_pos (zero_lt_one.trans_le hq))
    (source.barrierMass_pos (zero_lt_one.trans_le hq))




theorem chargeOne_negLogRate_le_windingOne_add_constant
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hmass : 0 < fkRectCriticalWindingOneMass R q) :
    -Real.log
          (sixVertexTorusFixedChargePartitionSum R.medialTorus 1
                (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum R.medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        R.height <=
      -Real.log (fkRectCriticalWindingOneMass R q) / R.height +
        (Real.log
              (fkRectChargeOneModeCost
                (sixVertexAntiferroelectricLambda
                  (fkQgt4SixVertexWeight q)) ^ 2) -
            Real.log ((2 / Real.sqrt q) ^ 2 / q)) /
          R.height := by
  let c : Real := (2 / Real.sqrt q) ^ 2 / q
  let K : Real := fkRectChargeOneModeCost
    (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
  let Q : Real :=
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
      sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hK : 0 < K ^ 2 := by
    exact sq_pos_of_pos (lt_of_lt_of_le zero_lt_one
      (fkRectChargeOneModeCost_one_le _))
  have hQ : 0 < Q := by
    dsimp [Q]
    apply div_pos
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        ((Nat.sub_le _ _).trans
          (Nat.div_le_self R.medialTorus.width 2))
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        (Nat.div_le_self R.medialTorus.width 2)
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
  have hfinite : c * fkRectCriticalWindingOneMass R q <= K ^ 2 * Q := by
    simpa [c, K, Q, fkRectCriticalWindingOneMass] using
      (windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio R hq)
  have hlog := Real.log_le_log (mul_pos hc hmass) hfinite
  rw [Real.log_mul hc.ne' hmass.ne', Real.log_mul hK.ne' hQ.ne'] at hlog
  have hnum :
      -Real.log Q <= -Real.log (fkRectCriticalWindingOneMass R q) +
        (Real.log (K ^ 2) - Real.log c) := by
    linarith
  have hh : 0 <= (R.height : Real) := by positivity
  calc
    -Real.log Q / R.height <=
        (-Real.log (fkRectCriticalWindingOneMass R q) +
          (Real.log (K ^ 2) - Real.log c)) / R.height :=
      div_le_div_of_nonneg_right hnum hh
    _ = -Real.log (fkRectCriticalWindingOneMass R q) / R.height +
        (Real.log (K ^ 2) - Real.log c) / R.height := by ring
    _ = _ := by rfl


theorem chargeOneRate_le_windingOneRate_of_tendsto
    (R : Nat -> FKRectTorus) {q chargeRate windingRate : Real}
    (hq : 4 < q)
    (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
    (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hwind : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingOneMass (R n) q) /
        (R n).height) atTop (nhds windingRate)) :
    chargeRate <= windingRate := by
  let C : Real :=
    Real.log
        (fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2) -
      Real.log ((2 / Real.sqrt q) ^ 2 / q)
  have hconstant : Tendsto (fun n => C / ((R n).height : Real))
      atTop (nhds 0) := hheight.const_div_atTop C
  have hright := hwind.add hconstant
  have hle : chargeRate <= windingRate + 0 := by
    apply le_of_tendsto_of_tendsto hcharge hright
    filter_upwards [] with n
    simpa [C] using
      chargeOne_negLogRate_le_windingOne_add_constant (R n) hq (hmass n)
  simpa using hle




theorem le_of_tendsto_of_eventually_le_add_vanishing
    (f g error : Nat -> Real) {limit upper : Real}
    (hf : Tendsto f atTop (nhds limit))
    (herror : Tendsto error atTop (nhds 0))
    (hle : ∀ᶠ n in atTop, f n <= g n + error n)
    (hg : forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ n in atTop, g n <= upper + epsilon) :
    limit <= upper := by
  by_contra hnot
  have hgap : 0 < limit - upper := sub_pos.mpr (lt_of_not_ge hnot)
  let epsilon : Real := (limit - upper) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hflow : ∀ᶠ n in atTop, limit - epsilon < f n :=
    (tendsto_order.1 hf).1 (limit - epsilon) (by linarith)
  have herr : ∀ᶠ n in atTop, error n < epsilon :=
    (tendsto_order.1 herror).2 epsilon hepsilon
  obtain ⟨n, hn, hgn, hfn, hen⟩ :=
    (hle.and ((hg epsilon hepsilon).and (hflow.and herr))).exists
  dsimp [epsilon] at hgn hfn hen
  linarith




theorem chargeOneRate_le_of_windingOne_eventualUpper
    (R : Nat -> FKRectTorus) {q chargeRate windingUpper : Real}
    (hq : 4 < q)
    (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
    (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ n in atTop,
      -Real.log (fkRectCriticalWindingOneMass (R n) q) /
          (R n).height <= windingUpper + epsilon) :
    chargeRate <= windingUpper := by
  let charge : Nat -> Real := fun n =>
    -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height
  let winding : Nat -> Real := fun n =>
    -Real.log (fkRectCriticalWindingOneMass (R n) q) / (R n).height
  let C : Real :=
    Real.log
        (fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2) -
      Real.log ((2 / Real.sqrt q) ^ 2 / q)
  let error : Nat -> Real := fun n => C / ((R n).height : Real)
  have herror : Tendsto error atTop (nhds 0) := by
    exact hheight.const_div_atTop C
  apply le_of_tendsto_of_eventually_le_add_vanishing
    charge winding error hcharge herror
  · filter_upwards [] with n
    simpa [charge, winding, error, C] using
      chargeOne_negLogRate_le_windingOne_add_constant (R n) hq (hmass n)
  · intro epsilon hepsilon
    simpa [winding] using hwind epsilon hepsilon



theorem fixedChargeVertical_chargeOneRate_le_windingOneRate
    {q windingRate : Real} (hq : 4 < q) (k : Nat)
    (hmass : forall m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : Tendsto (fun m =>
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
        (fkRectFixedChargeVerticalFamily 1 k m).height)
      atTop (nhds windingRate)) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingRate := by
  let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
  have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by
      dsimp [R]
      omega⟩
  have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hheightNat
  apply chargeOneRate_le_windingOneRate_of_tendsto R hq hmass hheight
  · simpa [R] using fkRectFixedCharge_vertical_negLogRatio_tendsto
      (show 0 < fkQgt4SixVertexWeight q by
        linarith [two_lt_fkQgt4SixVertexWeight hq]) 1 k
  · simpa [R] using hwind


theorem fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper
    {q windingUpper : Real} (hq : 4 < q) (k : Nat)
    (hmass : forall m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        windingUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
  let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
  have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by
      dsimp [R]
      omega⟩
  have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hheightNat
  apply chargeOneRate_le_of_windingOne_eventualUpper R hq hmass hheight
  · simpa [R] using fkRectFixedCharge_vertical_negLogRatio_tendsto
      (show 0 < fkQgt4SixVertexWeight q by
        linarith [two_lt_fkQgt4SixVertexWeight hq]) 1 k
  · intro epsilon hepsilon
    simpa [R] using hwind epsilon hepsilon



theorem fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional
    {q windingUpper : Real} (hq : 4 < q) (k : Nat)
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        windingUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper :=
  fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper hq k
    (fun m => fkRectCriticalWindingOneMass_pos _ (by linarith)) hwind



theorem fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds
    {q xiInv : Real} (hq : 4 < q)
    (hbound : forall k : Nat,
      -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) 1 (k + 1) <= xiInv) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  have hle : ((1 : Nat) : Real) * fkQgt4SixVertexGapRate q <= xiInv :=
    le_of_tendsto
      (tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq 1 (by omega))
      (Filter.Eventually.of_forall hbound)
  simpa using hle




theorem fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper
    {q xiInv : Real} (hq : 4 < q)
    (hmass : forall k m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds hq
  intro k
  exact fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper
    hq k (hmass k) (hwind k)



theorem fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_unconditional
    {q xiInv : Real} (hq : 4 < q)
    (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds hq
  intro k
  exact fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional
    hq k (hwind k)





theorem fkQgt4SixVertexGapRate_le_of_sourceCostEventualUpper
    {q xiInv : Real} (hq : 4 < q)
    (source : forall k m,
      FKRectWindingOneSource (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hsourceCost : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (source k m).connectionProduct /
            (fkRectFixedChargeVerticalFamily 1 k m).height +
          -Real.log (source k m).barrierMass /
            (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper hq
  · intro k m
    exact (source k m).windingOneMass_pos (by linarith)
  · intro k epsilon hepsilon
    let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
    let c : Real := FK.cFE (fkRectCriticalP q) q
    let error : Nat -> Real := fun m => -Real.log c / ((R m).height : Real)
    have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
      refine tendsto_atTop.2 (fun N => ?_)
      exact eventually_atTop.2 <| ⟨N, fun m hm => by
        dsimp [R]
        omega⟩
    have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hheightNat
    have herror : Tendsto error atTop (nhds 0) := by
      exact hheight.const_div_atTop (-Real.log c)
    let delta : Real := epsilon / 2
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have herr : ∀ᶠ m in atTop, error m < delta :=
      (tendsto_order.1 herror).2 delta hdelta
    filter_upwards [hsourceCost k delta hdelta, herr] with m hcost hmerror
    have hfinite := (source k m).windingOne_negLogRate_le
      (by linarith : 1 <= q)
    simp only [fkRectFixedChargeVerticalFamily_height] at hfinite
    dsimp [R, error, c] at hmerror
    dsimp [delta] at hcost hmerror
    change -Real.log (fkRectCriticalWindingOneMass
        (fkRectFixedChargeVerticalFamily 1 k m) q) /
      ((2 * (m + 2) : Nat) : Real) <= xiInv + epsilon
    linarith

end

end StatMech.FrontierD
