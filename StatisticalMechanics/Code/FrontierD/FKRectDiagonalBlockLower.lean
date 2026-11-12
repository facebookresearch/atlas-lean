/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKFiniteConnectionApproximation
import Code.FrontierD.FKRectLocalBoxEmbedding
import Code.FrontierD.FKRectWindingBlockSource
import Code.FK.TwoPointPathLower
import Code.FrontierD.FiniteProductExceptions



namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation Filter Topology

noncomputable section


def fkRectRightBandVertexAtRow
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width) (hx : cut <= x.val)
    (r : Nat) (hr : 1 <= r ∧ r <= R.height - 1) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨(x, ⟨r, by omega⟩), hx, hr⟩



theorem exists_fkRectRightBand_verticalWalk_length
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width) (hx : cut <= x.val)
    (r n : Nat) (hr : 1 <= r) (hupper : r + n <= R.height - 1) :
    ∃ w : (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Walk
          (fkRectRightBandVertexAtRow R cut x hx r ⟨hr, by omega⟩)
          (fkRectRightBandVertexAtRow R cut x hx (r + n)
            ⟨by omega, hupper⟩),
      w.length = n := by
  induction n with
  | zero =>
      exact ⟨.nil, rfl⟩
  | succ n ih =>
      have hnupper : r + n <= R.height - 1 := by omega
      obtain ⟨w, hw⟩ := ih hnupper
      have hlast : 1 <= r + n := by omega
      have hnext : r + n + 1 <= R.height - 1 := by omega
      have hpred : SixVertexArrows.cyclicPred R.height_pos
          (⟨r + n + 1, by omega⟩ : Fin R.height) =
          (⟨r + n, by omega⟩ : Fin R.height) := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg (by omega : r + n + 1 ≠ 0)]
        omega
      have hadj : (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1))).Adj
          (fkRectRightBandVertexAtRow R cut x hx (r + n)
            ⟨hlast, hnupper⟩)
          (fkRectRightBandVertexAtRow R cut x hx (r + n + 1)
            ⟨by omega, hnext⟩) := by
        change (fkRectTorusGraph R).Adj
          (x, (⟨r + n, by omega⟩ : Fin R.height))
          (x, (⟨r + n + 1, by omega⟩ : Fin R.height))
        simpa [hpred] using
          (fkRectTorusGraph_adj_verticalPred R x
            (⟨r + n + 1, by omega⟩ : Fin R.height)).symm
      let w' := w.concat hadj
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using w'
      · simp [w', hw]




theorem fkRectWindingBlock_twoPoint_ge_cFE_pow
    {q : Real} (hq : 1 <= q)
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 1)) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1)) <=
      FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) := by
  let r := 1 + 2 * (scale + 1) * i.val
  have hr : 1 <= r := by omega
  have hupper : r + 2 * (scale + 1) <=
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 := by
    have hi : i.val + 1 <= blocks + 1 := by omega
    have hmul := Nat.mul_le_mul_left (2 * (scale + 1)) hi
    calc
      r + 2 * (scale + 1) =
          1 + 2 * (scale + 1) * (i.val + 1) := by
        dsimp [r]
        ring
      _ <= 1 + 2 * (scale + 1) * (blocks + 1) :=
        Nat.add_le_add_left hmul 1
      _ = (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 := by
        simp only [fkRectWindingBlockVerticalFamily_height]
        omega
  obtain ⟨w, hw⟩ := exists_fkRectRightBand_verticalWalk_length
    (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx
    r (2 * (scale + 1)) hr hupper
  have hstart : fkRectRightBandVertexAtRow
      (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx r
        ⟨hr, by omega⟩ =
      fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc := by
    apply Subtype.ext
    rfl
  have hend : fkRectRightBandVertexAtRow
      (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx
        (r + 2 * (scale + 1)) ⟨by omega, hupper⟩ =
      fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change r + 2 * (scale + 1) =
        1 + 2 * (scale + 1) * (i.val + 1)
      dsimp [r]
      ring
  have hpath := FK.cFE_pow_walk_length_le_twoPoint
    (fkRectInducedGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
      (fkRectRightStripBand
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
    (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
    (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq w
  rw [hw] at hpath
  rw [hstart, hend] at hpath
  exact hpath

def fkRectWindingBlockBadIndices (blocks m : Nat) :
    Finset (Fin (blocks + 1)) :=
  (Finset.univ.filter fun i => i.val < m) ∪
    (Finset.univ.filter fun i => blocks - i.val < m)

theorem fkRectWindingBlockBadIndices_card_le (blocks m : Nat) :
    (fkRectWindingBlockBadIndices blocks m).card <= 2 * m := by
  classical
  let low := Finset.univ.filter fun i : Fin (blocks + 1) => i.val < m
  let high := Finset.univ.filter fun i : Fin (blocks + 1) => blocks - i.val < m
  have hlow : low.card <= m := by
    rw [← Fintype.card_coe]
    let f : {i // i ∈ low} -> Fin m := fun i =>
      ⟨i.1.val, (Finset.mem_filter.1 i.2).2⟩
    have hinj : Function.Injective f := by
      intro i j hij
      dsimp [f] at hij
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun z : Fin m => z.val) hij
    simpa using Fintype.card_le_of_injective f hinj
  have hhigh : high.card <= m := by
    rw [← Fintype.card_coe]
    let f : {i // i ∈ high} -> Fin m := fun i =>
      ⟨blocks - i.1.val, (Finset.mem_filter.1 i.2).2⟩
    have hinj : Function.Injective f := by
      intro i j hij
      dsimp [f] at hij
      have hv := congrArg (fun z : Fin m => z.val) hij
      change blocks - i.1.val = blocks - j.1.val at hv
      apply Subtype.ext
      apply Fin.ext
      have hi : i.1.val <= blocks := by omega
      have hj : j.1.val <= blocks := by omega
      omega
    simpa using Fintype.card_le_of_injective f hinj
  change (low ∪ high).card <= 2 * m
  exact (Finset.card_union_le low high).trans (by omega)

theorem not_mem_fkRectWindingBlockBadIndices
    {blocks m : Nat} (i : Fin (blocks + 1))
    (hi : i ∉ fkRectWindingBlockBadIndices blocks m) :
    m <= i.val ∧ m <= blocks - i.val := by
  classical
  rw [fkRectWindingBlockBadIndices, Finset.mem_union,
    Finset.mem_filter, Finset.mem_filter] at hi
  simp only [Finset.mem_univ, true_and] at hi
  omega




theorem fkRectWindingBlock_connectionProduct_ge_of_bulk
    {q a : Real} (hq : 1 <= q) (ha : 0 < a) (ha1 : a <= 1)
    (m k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val)
    (hbulk : ∀ i : Fin (blocks + 1),
      i ∉ fkRectWindingBlockBadIndices blocks m ->
        a <= FK.twoPointFun
          (fkRectInducedGraph
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectRightStripBand
              (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
              ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
          (fkRectCriticalP q) q
          (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc)
          (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)) :
    (FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))) ^ (2 * m) *
        a ^ (blocks + 1) <=
      ∏ xy ∈ connectionPathPairs (blocks + 1)
          (fkRectWindingBlockPathVertex k scale blocks cut x hx),
        FK.twoPointFun
          (fkRectInducedGraph
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectRightStripBand
              (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
              ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2 := by
  let b := FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))
  let F : Fin (blocks + 1) -> Real := fun i =>
    FK.twoPointFun
      (fkRectInducedGraph
        (fkRectWindingBlockVerticalFamily k scale blocks)
        (fkRectRightStripBand
          (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
          ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
      (fkRectCriticalP q) q
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hb : 0 < b := pow_pos hc _
  have hc1 : FK.cFE (fkRectCriticalP q) q <= 1 := by
    linarith [FK.cFE_le_half
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq]
  have hb1 : b <= 1 := by
    exact (pow_le_one₀ hc.le hc1)
  have hall : ∀ i, b <= F i := by
    intro i
    exact fkRectWindingBlock_twoPoint_ge_cFE_pow hq
      k scale blocks cut x hx i
  have hprod := pow_mul_pow_le_prod_of_exception_card
    (fkRectWindingBlockBadIndices blocks m) (2 * m)
    ha ha1 hb hb1 (fkRectWindingBlockBadIndices_card_le blocks m)
    F hall (by
      intro i hi
      exact hbulk i hi)
  simp only [Fintype.card_fin] at hprod
  change b ^ (2 * m) * a ^ (blocks + 1) <= _
  rw [connectionPathPairs]
  rw [Finset.prod_image
    (fkRectWindingBlockPath_pairMap_injective k scale blocks cut x hx).injOn]
  exact hprod




theorem exists_margin_criticalDiagonal_lt_windingBlock_twoPoint
    {q : Real} (hq : 4 < q) (scale : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m : Nat, scale + 1 <= m ∧
      ∀ (k blocks cut : Nat)
        (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
        (hx : cut <= x.val) (i : Fin (blocks + 1)),
        1 <= cut ->
        cut + 2 * m <= x.val ->
        x.val + 2 * m <
          (fkRectWindingBlockVerticalFamily k scale blocks).width ->
        1 + 2 * m <=
          (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val ->
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val +
            2 * m <=
          (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 ->
        fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon <
          FK.twoPointFun
            (fkRectInducedGraph
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectRightStripBand
                (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
                ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
            (fkRectCriticalP q) q
            (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc)
            (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) := by
  obtain ⟨m, hx0, hyDiag, hfinite⟩ :=
    exists_criticalFreeBox_exactDiagonalTwoPoint_gt_sub hq scale hepsilon
  have hsm : scale + 1 <= m := by
    have h := hyDiag 0
    simpa [fkQgt4ExactDiagonalSite] using h
  refine ⟨m, hsm, ?_⟩
  intro k blocks cut x hx i hcut hcolLower hcolUpper hrowLower hrowUpper
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let center :=
    (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1
  have hupper : R.height - 1 < R.height := by
    dsimp [R]
    omega
  have hfit : FKRectLocalBoxFits R center m cut 1 (R.height - 1) := by
    apply fkRectLocalBoxFits_of_margin
    · exact hupper
    · exact hcolLower
    · exact hcolUpper
    · exact hrowLower
    · exact hrowUpper
  have hbox := fkRectLocalBox_twoPoint_le_strip R center m cut 1
    (R.height - 1) hcut (by omega) hfit
    (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
    (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
    (by linarith : (1 : Real) <= q)
    (fkRectLocalBoxOrigin m)
    (fkRectLocalBoxReflectedDiagonal (scale + 1) m hsm)
  have hreflection := fkRectLocalBox_twoPoint_reflectedDiagonal_eq
    m (scale + 1) hsm (fkRectCriticalP q) q
  have horigin :
      (⟨origin 2, hx0⟩ : FK.boxVerts 2 m) = fkRectLocalBoxOrigin m := by
    apply Subtype.ext
    rfl
  have hdiag :
      (⟨fkQgt4ExactDiagonalSite (scale + 1), hyDiag⟩ : FK.boxVerts 2 m) =
        fkRectLocalBoxPositiveDiagonal (scale + 1) m hsm := by
    apply Subtype.ext
    funext j
    fin_cases j <;>
      simp [fkQgt4ExactDiagonalSite, fkRectLocalBoxPositiveDiagonal,
        fkRectPositiveDiagonalSite]
  rw [horigin, hdiag, ← hreflection] at hfinite
  have hcenter :
      fkRectLocalBoxEmbedding R center m cut 1 (R.height - 1) hfit
          (fkRectLocalBoxOrigin m) =
        fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc := by
    apply Subtype.ext
    exact fkRectLocalBoxVertex_origin R center
  have htarget :
      fkRectLocalBoxEmbedding R center m cut 1 (R.height - 1) hfit
          (fkRectLocalBoxReflectedDiagonal (scale + 1) m hsm) =
        fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ := by
    apply Subtype.ext
    exact fkRectLocalBoxVertex_reflectedDiagonal_eq R center
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ).1
      (scale + 1)
      (fkRectWindingBlockPathVertex_squarePoint_step
        k scale blocks cut x hx i)
  rw [hcenter, htarget] at hbox
  exact hfinite.trans_le hbox




theorem exists_margin_windingBlock_connectionProduct_ge_diagonal_sub
    {q : Real} (hq : 4 < q) (scale : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon <
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) :
    ∃ m : Nat, scale + 1 <= m ∧
      ∀ (k blocks cut : Nat)
        (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
        (hx : cut <= x.val),
        1 <= cut ->
        cut + 2 * m <= x.val ->
        x.val + 2 * m <
          (fkRectWindingBlockVerticalFamily k scale blocks).width ->
        (FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))) ^ (2 * m) *
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) ^
              (blocks + 1) <=
          ∏ xy ∈ connectionPathPairs (blocks + 1)
              (fkRectWindingBlockPathVertex k scale blocks cut x hx),
            FK.twoPointFun
              (fkRectInducedGraph
                (fkRectWindingBlockVerticalFamily k scale blocks)
                (fkRectRightStripBand
                  (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
                  ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
              (fkRectCriticalP q) q xy.1 xy.2 := by
  obtain ⟨m, hsm, hmargin⟩ :=
    exists_margin_criticalDiagonal_lt_windingBlock_twoPoint hq scale hepsilon
  refine ⟨m, hsm, ?_⟩
  intro k blocks cut x hx hcut hcolLower hcolUpper
  apply fkRectWindingBlock_connectionProduct_ge_of_bulk
    (by linarith : 1 <= q) (by linarith) (by
      have hone := fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one hq (scale + 1)
      linarith) m k scale blocks cut x hx
  intro i hi
  have hibounds := not_mem_fkRectWindingBlockBadIndices i hi
  have himul : i.val <= (scale + 1) * i.val :=
    Nat.le_mul_of_pos_left i.val (by omega)
  have hrowLower : 1 + 2 * m <=
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val := by
    change 1 + 2 * m <= 1 + 2 * (scale + 1) * i.val
    nlinarith
  have hiAdd : i.val + m <= blocks := by omega
  have hmMul : m <= (scale + 1) * m :=
    Nat.le_mul_of_pos_left m (by omega)
  have hrowUpper :
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val +
          2 * m <=
        (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 := by
    change 1 + 2 * (scale + 1) * i.val + 2 * m <=
      2 * (scale + 1) * (blocks + 1) + 2 - 1
    have hmul := Nat.mul_le_mul_left (2 * (scale + 1))
      (show i.val + m <= blocks + 1 by omega)
    have hmMul2 := Nat.mul_le_mul_left 2 hmMul
    calc
      1 + 2 * (scale + 1) * i.val + 2 * m <=
          1 + 2 * (scale + 1) * i.val + 2 * (scale + 1) * m := by
        nlinarith
      _ = 1 + 2 * (scale + 1) * (i.val + m) := by ring
      _ <= 1 + 2 * (scale + 1) * (blocks + 1) :=
        Nat.add_le_add_left hmul 1
      _ = 2 * (scale + 1) * (blocks + 1) + 2 - 1 := by omega
  exact (hmargin k blocks cut x hx i hcut hcolLower hcolUpper
    hrowLower hrowUpper).le




theorem eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight
    {q : Real} (hq : 4 < q) (scale leftRight : Nat)
    (hone : 1 <= leftRight)
    {epsilon barrierUpper : Real} (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon <
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1))
    (hbarrier : ∀ᶠ k in Filter.atTop,
      ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop,
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        barrierUpper + delta) :
    ∀ᶠ k in Filter.atTop,
      -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) 1 (k + 1) <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) /
          (2 * (scale + 1) : Real) + barrierUpper := by
  obtain ⟨m, _hsm, hproductRaw⟩ :=
    exists_margin_windingBlock_connectionProduct_ge_diagonal_sub
      hq scale hepsilon hepsilonLt
  filter_upwards [Filter.eventually_ge_atTop (leftRight + 4 * m), hbarrier] with
    k hk hkbarrier
  let cut := leftRight + 1
  let x : Fin (2 * (k + 3)) := ⟨cut + 2 * m, by
    dsimp [cut]
    omega⟩
  have hx : cut <= x.val := by dsimp [x]; omega
  let a := fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon
  let b := FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))
  let C := b ^ (2 * m)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by
    dsimp [b]
    exact pow_pos (FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
      (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
      (by linarith : (1 : Real) <= q)) _
  have hC : 0 < C := by dsimp [C]; exact pow_pos hb _
  let source : forall blocks,
      FKRectWindingOneSource
        (fkRectWindingBlockVerticalFamily k scale blocks) q := fun blocks =>
    fkRectWindingBlockSource k scale blocks leftRight cut hone (by
        dsimp [cut]
        omega)
      (by simp only [fkRectWindingBlockVerticalFamily_width]; omega)
      x hx q b hb (by
        intro xy hxy
        obtain ⟨i, rfl⟩ :=
          (mem_fkRectWindingBlockPathPairs_iff
            k scale blocks cut x hx xy).1 hxy
        exact fkRectWindingBlock_twoPoint_ge_cFE_pow
          (by linarith : 1 <= q) k scale blocks cut x hx i)
  have hproduct : forall blocks,
      C * a ^ (blocks + 1) <= (source blocks).connectionProduct := by
    intro blocks
    have hraw := hproductRaw k blocks cut x hx (by
        dsimp [cut]
        omega)
      (by dsimp [x]; omega) (by
        simp only [fkRectWindingBlockVerticalFamily_width]
        dsimp [x]
        omega)
    change C * a ^ (blocks + 1) <= _
    simpa [C, b, a, source, FKRectWindingOneSource.connectionProduct] using hraw
  apply fkRectWindingBlock_chargeOneRate_le_productPowAndBarrier
    hq ha hC k scale source hproduct
  intro delta hdelta
  have hbarr := hkbarrier delta hdelta
  filter_upwards [hbarr] with blocks hbarr
  simpa [source, FKRectWindingOneSource.barrierMass,
    fkRectWindingBlockSource] using hbarr


theorem eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier
    {q : Real} (hq : 4 < q) (scale : Nat)
    {epsilon barrierUpper : Real} (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon <
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1))
    (hbarrier : ∀ᶠ k in Filter.atTop,
      ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop,
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks) 1
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        barrierUpper + delta) :
    ∀ᶠ k in Filter.atTop,
      -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) 1 (k + 1) <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) /
          (2 * (scale + 1) : Real) + barrierUpper := by
  exact eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight
    hq scale 1 (by omega) hepsilon hepsilonLt hbarrier




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight
    {q : Real} (hq : 4 < q) (scale leftRight : Nat)
    (hone : 1 <= leftRight) {barrierUpper : Real}
    (hbarrier : ∀ᶠ k in Filter.atTop,
      ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop,
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        barrierUpper + delta) :
    fkQgt4SixVertexGapRate q <=
      -Real.log
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
        (2 * (scale + 1) : Real) + barrierUpper := by
  let tau := fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)
  let epsilon : Nat -> Real := fun n => tau / (n + 2 : Nat)
  have htau : 0 < tau := by
    dsimp [tau]
    exact fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq (scale + 1)
  have hepsilonPos : forall n, 0 < epsilon n := by
    intro n
    exact div_pos htau (by positivity)
  have hepsilonLt : forall n, epsilon n < tau := by
    intro n
    exact div_lt_self htau (by
      exact_mod_cast (show 1 < n + 2 by omega))
  have hbound : forall n,
      fkQgt4SixVertexGapRate q <=
        -Real.log (tau - epsilon n) / (2 * (scale + 1) : Real) +
          barrierUpper := by
    intro n
    apply fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds hq
    simpa [tau] using
      (eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight
        hq scale leftRight hone (hepsilonPos n)
        (by simpa [tau] using hepsilonLt n) hbarrier)
  have hden : Tendsto (fun n : Nat => ((n + 2 : Nat) : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hepsilon : Tendsto epsilon Filter.atTop (nhds 0) := by
    exact hden.const_div_atTop tau
  have hsub : Tendsto (fun n => tau - epsilon n) Filter.atTop (nhds tau) := by
    simpa using tendsto_const_nhds.sub hepsilon
  have hlog : Tendsto (fun n => Real.log (tau - epsilon n))
      Filter.atTop (nhds (Real.log tau)) :=
    (Real.continuousAt_log htau.ne').tendsto.comp hsub
  have hrhs : Tendsto (fun n =>
      -Real.log (tau - epsilon n) / (2 * (scale + 1) : Real) +
        barrierUpper) Filter.atTop
      (nhds (-Real.log tau / (2 * (scale + 1) : Real) +
        barrierUpper)) :=
    (hlog.neg.div_const _).add_const _
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hrhs
    (Filter.Eventually.of_forall hbound)
  simpa [tau] using hle


theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier
    {q : Real} (hq : 4 < q) (scale : Nat) {barrierUpper : Real}
    (hbarrier : ∀ᶠ k in Filter.atTop,
      ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop,
        -Real.log
            (fkRectCriticalEventMass
              (fkRectWindingBlockVerticalFamily k scale blocks) q
              (fkRectSourceLeftBarrier
                (fkRectWindingBlockVerticalFamily k scale blocks) 1
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        barrierUpper + delta) :
    fkQgt4SixVertexGapRate q <=
      -Real.log
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
        (2 * (scale + 1) : Real) + barrierUpper := by
  exact fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight
    hq scale 1 (by omega) hbarrier




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_leftBarrierBounds
    {q : Real} (hq : 4 < q) (leftRight : Nat -> Nat)
    (hone : forall scale, 1 <= leftRight scale)
    (barrierUpper : Nat -> Real)
    (hbarrierUpper : Tendsto barrierUpper Filter.atTop (nhds 0))
    (hbarrier : forall scale,
      ∀ᶠ k in Filter.atTop,
        ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop,
          -Real.log
              (fkRectCriticalEventMass
                (fkRectWindingBlockVerticalFamily k scale blocks) q
                (fkRectSourceLeftBarrier
                  (fkRectWindingBlockVerticalFamily k scale blocks)
                  (leftRight scale)
                  (fkRectUnitLeftBarrierGap
                    (fkRectWindingBlockVerticalFamily k scale blocks)))) /
            (fkRectWindingBlockVerticalFamily k scale blocks).height <=
          barrierUpper scale + delta) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds
    hq barrierUpper hbarrierUpper
  intro scale
  exact
    fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight
      hq scale (leftRight scale) (hone scale) (hbarrier scale)

end

end StatMech.FrontierD
