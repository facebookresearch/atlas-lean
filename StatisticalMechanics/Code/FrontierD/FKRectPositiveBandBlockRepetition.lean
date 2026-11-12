/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectColumnTranslation
import Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Code.FrontierD.FKRectDualBarrierForceTopology
import Code.FrontierD.FKRectDualSourceBarrierPattern
import Code.FrontierD.FKRectDualSourceBarrierRate
import Code.FK.TwoPointPathLower



open Set SimpleGraph Filter Topology

namespace StatMech.FrontierD

noncomputable section



def fkRectPositiveBandBulkBlocks
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale) : Nat :=
  (R.height - 1 - (24 * scale + 4)) / B.step

theorem FKRectPositiveBandOrientedBlock.step_pos
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hscale : 3 ≤ scale) :
    0 < B.step := by
  have hbound := B.step_scale
  omega

theorem fkRectPositiveBandBulkBlocks_mul_step_le
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale) :
    fkRectPositiveBandBulkBlocks B * B.step ≤
      R.height - 1 - (24 * scale + 4) := by
  exact Nat.div_mul_le_self _ _

theorem fkRectPositiveBandBulkBlocks_remainder_lt
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hscale : 3 ≤ scale) :
    R.height - 1 - (24 * scale + 4) -
        fkRectPositiveBandBulkBlocks B * B.step < B.step := by
  let N := R.height - 1 - (24 * scale + 4)
  have hstep := B.step_pos hscale
  have hdecomp : N % B.step + N / B.step * B.step = N := by
    simpa [Nat.mul_comm] using Nat.mod_add_div N B.step
  have hmod : N % B.step < B.step := Nat.mod_lt N hstep
  have hle : N / B.step * B.step ≤ N := Nat.div_mul_le_self _ _
  have hsub : N - N / B.step * B.step = N % B.step := by omega
  change N - N / B.step * B.step < B.step
  rw [hsub]
  exact hmod



def fkRectPositiveBandBlockPathVertex
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B + 1)) :
    FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1) := by
  let v := fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1
  refine ⟨v, ?_⟩
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have hi : i.val ≤ fkRectPositiveBandBulkBlocks B := by omega
  have himul : i.val * B.step ≤
      fkRectPositiveBandBulkBlocks B * B.step :=
    Nat.mul_le_mul_right B.step hi
  have hrow := B.row_bound B.start.1 B.start.2
  have hlt : B.start.1.2.val + i.val * B.step < R.height := by
    have hrecover :
        R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
          R.height - 1 := Nat.sub_add_cancel hheight
    omega
  have htranslate := fkRectRowTranslate_eq_add_of_lt
    R (i.val * B.step) B.start.1.2 hlt
  change 1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1 ∧
    1 ≤ v.2.val ∧ v.2.val ≤ R.height - 1
  dsimp [v]
  rw [show fkRectRowTranslate R
      ((i.val : Int) * (B.step : Int)) B.start.1.2 =
        ⟨B.start.1.2.val + i.val * B.step, hlt⟩ by
      simpa [Nat.cast_mul] using htranslate]
  refine ⟨(B.column_bound B.start.1 B.start.2).1,
    (B.column_bound B.start.1 B.start.2).2, ?_, ?_⟩
  · exact hrow.1.trans (Nat.le_add_right _ _)
  · exact Nat.le_sub_one_of_lt hlt

@[simp] theorem fkRectPositiveBandBlockPathVertex_val
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B + 1)) :
    (fkRectPositiveBandBlockPathVertex B hheight i).1 =
      fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1 := rfl



theorem fkRectPositiveBandBlockPathVertex_pair
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B)) :
    ((fkRectPositiveBandBlockPathVertex B hheight i.castSucc).1,
      (fkRectPositiveBandBlockPathVertex B hheight i.succ).1) =
    (fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1,
      fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.finish.1) := by
  rw [fkRectPositiveBandBlockPathVertex_val,
    fkRectPositiveBandBlockPathVertex_val]
  congr 1
  calc
    fkRectEvenRowTranslationVertexEquiv R
        (i.succ.val * B.step) B.start.1 =
      fkRectEvenRowTranslationVertexEquiv R
        (i.val * B.step + B.step) B.start.1 := by
          rw [show i.succ.val = i.val + 1 by rfl, Nat.add_mul]
          simp
    _ = fkRectEvenRowTranslationVertexEquiv R (i.val * B.step)
        (fkRectEvenRowTranslationVertexEquiv R B.step B.start.1) :=
      (fkRectEvenRowTranslationVertexEquiv_add
        R (i.val * B.step) B.step B.start.1).symm
    _ = fkRectEvenRowTranslationVertexEquiv R
        (i.val * B.step) B.finish.1 := by rw [B.translate_start]


def fkRectPositiveBandBlockBulkPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :=
  connectionPathPairs (fkRectPositiveBandBulkBlocks B)
    (fkRectPositiveBandBlockPathVertex B hheight)



def fkRectPositiveBandBlockConnectorPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Finset
      (FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1)) :=
  { (fkRectColumnBandRowOne R 1 (4 * scale + 1)
        (fkRectUnitGapColumn R) (by rfl)
          (by simp [fkRectUnitGapColumn]),
      fkRectPositiveBandBlockPathVertex B hheight 0),
    (fkRectPositiveBandBlockPathVertex B hheight
        (Fin.last (fkRectPositiveBandBulkBlocks B)),
      fkRectColumnBandLastRow R 1 (4 * scale + 1)
        (fkRectUnitGapColumn R) (by rfl)
          (by simp [fkRectUnitGapColumn])) }


def fkRectPositiveBandBlockAuxiliaryPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :=
  fkRectPositiveBandBlockBulkPairs B hheight ∪
    fkRectPositiveBandBlockConnectorPairs B hheight



theorem fkRectPositiveBandBlockAuxiliaryPairs_spans
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    FKRectColumnBandConnectionChainSpans R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn])
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  let bottomGap := fkRectColumnBandRowOne R 1 (4 * scale + 1)
    (fkRectUnitGapColumn R) (by rfl)
      (by simp [fkRectUnitGapColumn])
  let topGap := fkRectColumnBandLastRow R 1 (4 * scale + 1)
    (fkRectUnitGapColumn R) (by rfl)
      (by simp [fkRectUnitGapColumn])
  let v := fkRectPositiveBandBlockPathVertex B hheight
  intro sigma hchain
  have hbottom :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable bottomGap (v 0) := by
    apply hchain (bottomGap, v 0)
    apply Finset.mem_union_right
    apply Finset.mem_insert.mpr
    left
    rfl
  have hbulk :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable (v 0)
          (v (Fin.last (fkRectPositiveBandBulkBlocks B))) := by
    apply reachable_first_last_of_connectionPathPairs
    intro i
    exact hchain _ (Finset.mem_union_left _
      (connectionPathPairs_pair_mem _ v i))
  have htop :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable
          (v (Fin.last (fkRectPositiveBandBulkBlocks B))) topGap := by
    exact hchain _ (Finset.mem_union_right _ (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))))
  exact (hbottom.trans hbulk).trans htop



theorem fkRectInduced_openSub_fullGraphConfiguration_eq
    (R : FKRectTorus) (omega : R.Configuration) (S : Set R.Vertex) :
    FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)
          (fkRectFullGraphConfiguration R omega)) =
      (fkRectOpenGraph R omega).induce S := by
  rw [← fkOpenSub_fullGraphConfiguration R omega]
  rfl




theorem fkRectCritical_inducedTwoPoint_le_connectedWithinMass
    (R : FKRectTorus) (S : Set R.Vertex) {q : Real} (hq : 1 ≤ q)
    (x y : FKRectInducedVertex R S) :
    FK.twoPointFun (fkRectInducedGraph R S) (fkRectCriticalP q) q x y ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  let A := FK.connEvent (fkRectInducedGraph R S) x y
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hdom := FK.bdp_free_inner_dominated_fkProb
    (Gin := fkRectInducedGraph R S) (Gout := fkRectTorusGraph R)
    (ιV := (Subtype.val : FKRectInducedVertex R S → R.Vertex))
    Subtype.val_injective (fkRectInducedGraph_adjMatch R S)
      hp hp1 hq (A := A)
      (FK.connEvent_isIncreasing (fkRectInducedGraph R S) x y)
  have hsubset :
      FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A ⊆
        fkRectFullGraphEvent R B := by
    intro rho hrho
    let omega := fkRectIndexedConfigurationOfFullGraph R rho
    have hreach : FKRectConnectedWithin R omega S x y := by
      unfold FKRectConnectedWithin
      rw [← fkRectInduced_openSub_fullGraphConfiguration_eq R omega S]
      rw [fkRectInduced_openSub_indexedConfiguration_eq R S rho]
      exact hrho
    change (fkRectFullEdgeConfigEquiv R).symm
      (FK.ecz_closeOff (fkRectTorusGraph R) rho) ∈ B
    exact hreach
  unfold FK.twoPointFun
  calc
    (∑ omega,
        FK.fkProb (fkRectInducedGraph R S) (fkRectCriticalP q) q omega *
          A.indicator (fun _ => (1 : Real)) omega) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectInducedGraph R S)
          (fkRectCriticalP q) q omega := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
    _ ≤ ∑ rho,
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := hdom
    _ ≤ ∑ rho,
        (fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
          apply Finset.sum_le_sum
          intro rho _
          apply mul_le_mul_of_nonneg_right _
            (FK.fkProb_nonneg (fkRectTorusGraph R) hp hp1 hq0 rho)
          by_cases hrho : rho ∈
              FK.ocd_innerRestrict
                (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A
          · rw [Set.indicator_of_mem hrho,
              Set.indicator_of_mem (hsubset hrho)]
          · rw [Set.indicator_of_notMem hrho]
            exact Set.indicator_nonneg (fun _ _ => zero_le_one) rho
    _ = fkRectCriticalEventMass R q B :=
      fkRectFullGraphEvent_mass_eq R hq B



theorem fkRectColumnBand_reachable_horizontalPred_of_lower_lt
    (R : FKRectTorus) (right lower upper : Nat)
    (x : Fin R.width) (y : Fin R.height)
    (hxleft : 1 < x.val) (hxright : x.val ≤ right)
    (hylower : lower < y.val) (hyupper : y.val ≤ upper) :
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      ⟨(x, y), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        omega⟩
      ⟨(xp, y), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        rw [fkRectCyclicPred_val]
        split <;> omega⟩ := by
  dsimp only
  let xp := SixVertexArrows.cyclicPred R.width_pos x
  let yp := SixVertexArrows.cyclicPred R.height_pos y
  have hxp : xp.val = x.val - 1 := by
    dsimp [xp]
    rw [fkRectCyclicPred_val]
    split <;> omega
  have hyp : yp.val = y.val - 1 := by
    dsimp [yp]
    rw [fkRectCyclicPred_val]
    split <;> omega
  let vx : FKRectInducedVertex R
      (fkRectColumnBand R 1 right lower upper) :=
    ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧
      lower ≤ y.val ∧ y.val ≤ upper; omega⟩
  let vp : FKRectInducedVertex R
      (fkRectColumnBand R 1 right lower upper) :=
    ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧
      lower ≤ y.val ∧ y.val ≤ upper; rw [hxp]; omega⟩
  by_cases hy : Even y.val
  · let vm : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, yp), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ yp.val ∧ yp.val ≤ upper
        rw [hxp, hyp]
        omega⟩
    have hdiag : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vx vm := by
      change (fkRectTorusGraph R).Adj (x, y) (xp, yp)
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    have hvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vp vm := by
      change (fkRectTorusGraph R).Adj (xp, y) (xp, yp)
      exact fkRectTorusGraph_adj_verticalPred R xp y
    simpa [vx, vp, xp] using hdiag.reachable.trans hvert.symm.reachable
  · let vm : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, yp), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ yp.val ∧ yp.val ≤ upper
        rw [hyp]
        omega⟩
    have hvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vx vm := by
      change (fkRectTorusGraph R).Adj (x, y) (x, yp)
      exact fkRectTorusGraph_adj_verticalPred R x y
    have hdiag : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vp vm := by
      change (fkRectTorusGraph R).Adj (xp, y) (x, yp)
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    simpa [vx, vp, xp] using hvert.reachable.trans hdiag.symm.reachable



theorem fkRectColumnBand_reachable_horizontalPred
    (R : FKRectTorus) (right lower upper : Nat)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    (x : Fin R.width) (y : Fin R.height)
    (hxleft : 1 < x.val) (hxright : x.val ≤ right)
    (hylower : lower ≤ y.val) (hyupper : y.val ≤ upper) :
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      ⟨(x, y), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        omega⟩
      ⟨(xp, y), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        rw [fkRectCyclicPred_val]
        split <;> omega⟩ := by
  dsimp only
  by_cases hy : lower < y.val
  · exact fkRectColumnBand_reachable_horizontalPred_of_lower_lt
      R right lower upper x y hxleft hxright hy hyupper
  · have hyeq : y.val = lower := by omega
    have hsuccLt : y.val + 1 < R.height := by
      omega
    let ys : Fin R.height := ⟨y.val + 1, hsuccLt⟩
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    have hxp : xp.val = x.val - 1 := by
      dsimp [xp]
      rw [fkRectCyclicPred_val]
      split <;> omega
    have hpredYs : SixVertexArrows.cyclicPred R.height_pos ys = y := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      split <;> simp [ys] at * <;> omega
    let vx : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧
        lower ≤ y.val ∧ y.val ≤ upper; omega⟩
    let vxs : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, ys), by change 1 ≤ x.val ∧ x.val ≤ right ∧
        lower ≤ ys.val ∧ ys.val ≤ upper; simp [ys]; omega⟩
    let vp : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧
        lower ≤ y.val ∧ y.val ≤ upper; rw [hxp]; omega⟩
    let vps : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, ys), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ ys.val ∧ ys.val ≤ upper
        rw [hxp]
        simp [ys]
        omega⟩
    have hxvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vxs vx := by
      change (fkRectTorusGraph R).Adj (x, ys) (x, y)
      rw [← hpredYs]
      exact fkRectTorusGraph_adj_verticalPred R x ys
    have hpvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vps vp := by
      change (fkRectTorusGraph R).Adj (xp, ys) (xp, y)
      rw [← hpredYs]
      exact fkRectTorusGraph_adj_verticalPred R xp ys
    have hmiddle := fkRectColumnBand_reachable_horizontalPred_of_lower_lt
      R right lower upper x ys hxleft hxright (by simp [ys]; omega)
        (by simp [ys]; omega)
    have hroute := hxvert.symm.reachable.trans
      (hmiddle.trans hpvert.reachable)
    simpa [vx, vxs, vp, vps, xp] using hroute


def fkRectColumnBandGridEquiv
    (R : FKRectTorus) (right lower upper : Nat)
    (hright : right < R.width) (hlowerUpper : lower ≤ upper)
    (hupper : upper < R.height) :
    (Fin right × Fin (upper + 1 - lower)) ≃
      FKRectColumnBandVertex R 1 right lower upper where
  toFun z := ⟨
    (⟨z.1.val + 1, by omega⟩, ⟨lower + z.2.val, by
      have hz := z.2.isLt
      omega⟩), by
        change 1 ≤ z.1.val + 1 ∧ z.1.val + 1 ≤ right ∧
          lower ≤ lower + z.2.val ∧ lower + z.2.val ≤ upper
        have hz := z.2.isLt
        omega⟩
  invFun v :=
    (⟨v.1.1.val - 1, by
      have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      omega⟩,
     ⟨v.1.2.val - lower, by
      have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      omega⟩)
  left_inv z := by
    apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      change v.1.1.val - 1 + 1 = v.1.1.val
      omega
    · have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      change lower + (v.1.2.val - lower) = v.1.2.val
      omega



theorem fkRectColumnBandGrid_adj_reachable
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    {z w : Fin right × Fin (upper + 1 - lower)}
    (hzw : ((pathGraph right) □
      (pathGraph (upper + 1 - lower))).Adj z w) :
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      (fkRectColumnBandGridEquiv R right lower upper hright
        hlowerUpper.le hupper z)
      (fkRectColumnBandGridEquiv R right lower upper hright
        hlowerUpper.le hupper w) := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper.le hupper
  change ((pathGraph right).Adj z.1 w.1 ∧ z.2 = w.2) ∨
    ((pathGraph (upper + 1 - lower)).Adj z.2 w.2 ∧ z.1 = w.1) at hzw
  rcases hzw with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · have hrow : (e w).1.2 = (e z).1.2 := by
      apply Fin.ext
      simp [e, fkRectColumnBandGridEquiv, hy]
    rw [pathGraph_adj] at hx
    rcases hx with hx | hx
    · have hr := fkRectColumnBand_reachable_horizontalPred
          R right lower upper hlowerUpper hupper
          (e w).1.1 (e w).1.2 (by
            change 1 < w.1.val + 1
            omega) (by
            change w.1.val + 1 ≤ right
            omega) (by
              rcases (e w).2 with ⟨_, _, hlow, _⟩
              exact hlow) (by
              rcases (e w).2 with ⟨_, _, _, hup⟩
              exact hup)
      have hpred : SixVertexArrows.cyclicPred R.width_pos (e w).1.1 =
          (e z).1.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hr' := hr.symm
      convert hr' using 1 <;> apply Subtype.ext
      · apply Prod.ext
        · exact hpred.symm
        · exact hrow.symm
    · have hr := fkRectColumnBand_reachable_horizontalPred
          R right lower upper hlowerUpper hupper
          (e z).1.1 (e z).1.2 (by
            change 1 < z.1.val + 1
            omega) (by
            change z.1.val + 1 ≤ right
            omega) (by
              rcases (e z).2 with ⟨_, _, hlow, _⟩
              exact hlow) (by
              rcases (e z).2 with ⟨_, _, _, hup⟩
              exact hup)
      have hpred : SixVertexArrows.cyclicPred R.width_pos (e z).1.1 =
          (e w).1.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      convert hr using 1 <;> apply Subtype.ext
      · apply Prod.ext
        · exact hpred.symm
        · exact hrow
  · have hcol : (e w).1.1 = (e z).1.1 := by
      apply Fin.ext
      simp [e, fkRectColumnBandGridEquiv, hx]
    rw [pathGraph_adj] at hy
    rcases hy with hy | hy
    · have hpred : SixVertexArrows.cyclicPred R.height_pos (e w).1.2 =
          (e z).1.2 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hadj : (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Adj (e w) (e z) := by
        change (fkRectTorusGraph R).Adj (e w).1 (e z).1
        rw [show (e z).1 = ((e w).1.1,
          SixVertexArrows.cyclicPred R.height_pos (e w).1.2) by
            apply Prod.ext
            · exact hcol.symm
            · exact hpred.symm]
        exact fkRectTorusGraph_adj_verticalPred R (e w).1.1 (e w).1.2
      exact hadj.symm.reachable
    · have hpred : SixVertexArrows.cyclicPred R.height_pos (e z).1.2 =
          (e w).1.2 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hadj : (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Adj (e z) (e w) := by
        change (fkRectTorusGraph R).Adj (e z).1 (e w).1
        rw [show (e w).1 = ((e z).1.1,
          SixVertexArrows.cyclicPred R.height_pos (e z).1.2) by
            apply Prod.ext
            · exact hcol
            · exact hpred.symm]
        exact fkRectTorusGraph_adj_verticalPred R (e z).1.1 (e z).1.2
      exact hadj.reachable



theorem fkRectColumnBand_preconnected
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height) :
    (fkRectInducedGraph R
      (fkRectColumnBand R 1 right lower upper)).Preconnected := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper.le hupper
  intro u v
  have hgrid := ((pathGraph_preconnected right).boxProd
    (pathGraph_preconnected (upper + 1 - lower))) (e.symm u) (e.symm v)
  have hroute : (fkRectInducedGraph R
      (fkRectColumnBand R 1 right lower upper)).Reachable
        (e (e.symm u)) (e (e.symm v)) := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at hgrid
    have hlift := hgrid.lift e (fun _ _ hxy =>
      fkRectColumnBandGrid_adj_reachable
        R right lower upper hrightPos hright hlowerUpper hupper hxy)
    have collapse : ∀ {a b}, Relation.ReflTransGen
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Reachable a b →
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Reachable a b := by
      intro a b hab
      induction hab with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih => exact ih.trans hbc
    exact collapse hlift
  simpa using hroute

theorem fkRectColumnBand_fintype_card
    (R : FKRectTorus) (right lower upper : Nat)
    (hright : right < R.width) (hlowerUpper : lower ≤ upper)
    (hupper : upper < R.height) :
    Fintype.card (FKRectColumnBandVertex R 1 right lower upper) =
      right * (upper + 1 - lower) := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper hupper
  rw [← Fintype.card_congr e]
  simp



theorem fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    {q : Real} (hq : 1 ≤ q)
    (x y : FKRectColumnBandVertex R 1 right lower upper) :
    FK.cFE (fkRectCriticalP q) q ^
        (right * (upper + 1 - lower)) ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnBand R 1 right lower upper) x y} := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hreach := fkRectColumnBand_preconnected R right lower upper
    hrightPos hright hlowerUpper hupper x y
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hlength : w.length < right * (upper + 1 - lower) := by
    rw [← fkRectColumnBand_fintype_card R right lower upper
      hright hlowerUpper.le hupper]
    exact hw.length_lt
  have hcpos : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos hp hp1 hq
  have hcle : FK.cFE (fkRectCriticalP q) q ≤ 1 := by
    linarith [FK.cFE_le_half hp hp1 hq]
  calc
    FK.cFE (fkRectCriticalP q) q ^
        (right * (upper + 1 - lower)) ≤
      FK.cFE (fkRectCriticalP q) q ^ w.length :=
        pow_le_pow_of_le_one hcpos.le hcle (Nat.le_of_lt hlength)
    _ ≤ FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper))
        (fkRectCriticalP q) q x y :=
      FK.cFE_pow_walk_length_le_twoPoint
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)) hp hp1 hq w
    _ ≤ fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnBand R 1 right lower upper) x y} :=
      fkRectCritical_inducedTwoPoint_le_connectedWithinMass
        R (fkRectColumnBand R 1 right lower upper) hq x y



theorem fkRectPositiveBandBlock_translatedCarrier_subset
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Nat) (hi : i < fkRectPositiveBandBulkBlocks B) :
    fkRectEvenRowTranslationSet R (i * B.step) B.carrier ⊆
      fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1) := by
  intro v hv
  rcases hv with ⟨w, hw, rfl⟩
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have himul : i * B.step ≤
      fkRectPositiveBandBulkBlocks B * B.step :=
    Nat.mul_le_mul_right B.step (Nat.le_of_lt hi)
  have hrow := B.row_bound w hw
  have hlt : w.2.val + i * B.step < R.height := by
    have hrecover :
        R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
          R.height - 1 := Nat.sub_add_cancel hheight
    omega
  rw [fkRectEvenRowTranslationVertexEquiv_apply,
    fkRectRowTranslate_eq_add_of_lt R (i * B.step) w.2 hlt]
  refine ⟨(B.column_bound w hw).1, (B.column_bound w hw).2, ?_, ?_⟩
  · exact hrow.1.trans (Nat.le_add_right _ _)
  · exact Nat.le_sub_one_of_lt hlt



theorem fkRectPositiveBandBlockIntersection_inducedChain
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (omega : R.Configuration)
    (hmem : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B)) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectColumnBandVertex R 1 (4 * scale + 1) 1
            (R.height - 1) → R.Vertex)
        (fkRectFullGraphConfiguration R omega) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
        (fkRectPositiveBandBlockBulkPairs B hheight) := by
  intro pair hpair
  rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
  change (FK.openSub
    (fkRectInducedGraph R
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
    (FK.ocd_innerRestrict Subtype.val
      (fkRectFullGraphConfiguration R omega))).Reachable _ _
  rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
  have hcopy : omega ∈ fkRectEvenRowTranslatedConnectionEvent
      R B.carrier B.start B.finish (i.val * B.step) :=
    hmem i.val (Finset.mem_range.mpr i.isLt)
  have hwithin := hcopy.mono_set R omega
    (fkRectPositiveBandBlock_translatedCarrier_subset
      B hheight i.val i.isLt)
  have hp := fkRectPositiveBandBlockPathVertex_pair B hheight i
  have hp0 := congrArg Prod.fst hp
  have hp1 := congrArg Prod.snd hp
  change ((fkRectOpenGraph R omega).induce
    (fkRectColumnBand R 1 (4 * scale + 1) 1
      (R.height - 1))).Reachable _ _
  convert hwithin using 1
  · apply Subtype.ext
    exact hp1


def fkRectPositiveBandBlockBottomConnectorEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
    (fkRectColumnBandRowOne R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn]))
    (fkRectPositiveBandBlockPathVertex B hheight 0)}



def fkRectPositiveBandBlockTopConnectorEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
    (fkRectPositiveBandBlockPathVertex B hheight
      (Fin.last (fkRectPositiveBandBulkBlocks B)))
    (fkRectColumnBandLastRow R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn]))}

theorem fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockBottomConnectorEvent B hheight) :=
  fkRectConnectedWithin_isIncreasing R _ _ _

theorem fkRectPositiveBandBlockTopConnectorEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockTopConnectorEvent B hheight) :=
  fkRectConnectedWithin_isIncreasing R _ _ _



theorem fkRectCritical_cFE_pow_le_bottomConnector
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (24 * scale + 4)) ≤
      fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockBottomConnectorEvent B hheight) := by
  let S0 := fkRectColumnBand R 1 (4 * scale + 1) 1 (24 * scale + 4)
  let x0 : FKRectInducedVertex R S0 :=
    ⟨fkRectRowOneVertex R (fkRectUnitGapColumn R), by
      change 1 ≤ 1 ∧ 1 ≤ 4 * scale + 1 ∧
        1 ≤ 1 ∧ 1 ≤ 24 * scale + 4
      omega⟩
  let y0 : FKRectInducedVertex R S0 :=
    ⟨B.start.1, by
      exact ⟨(B.column_bound B.start.1 B.start.2).1,
        (B.column_bound B.start.1 B.start.2).2,
        (B.row_bound B.start.1 B.start.2).1,
        (B.row_bound B.start.1 B.start.2).2⟩⟩
  have hbase := fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    R (4 * scale + 1) 1 (24 * scale + 4)
      (by omega) hproper (by omega) (by omega) hq x0 y0
  have hsubset :
      {omega | FKRectConnectedWithin R omega S0 x0 y0} ⊆
        fkRectPositiveBandBlockBottomConnectorEvent B hheight := by
    intro omega homega
    have hmono := homega.mono_set R omega (T :=
        fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) (by
      intro v hv
      exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.trans hheight⟩)
    unfold fkRectPositiveBandBlockBottomConnectorEvent
    change FKRectConnectedWithin R omega
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) _ _
    convert hmono using 1
    · apply Subtype.ext
      rw [fkRectPositiveBandBlockPathVertex_val]
      simpa [y0] using
        (fkRectEvenRowTranslationVertexEquiv_zero R B.start.1)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmonoMass := fkRectCriticalEventMass_mono R hq0 hsubset
  simpa [S0] using hbase.trans hmonoMass

theorem fkRectPositiveBandBlockPathVertex_last_row_lower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale) :
    R.height - 1 - (40 * scale + 6) ≤
      (fkRectPositiveBandBlockPathVertex B hheight
        (Fin.last (fkRectPositiveBandBulkBlocks B))).1.2.val := by
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have hrow := B.row_bound B.start.1 B.start.2
  have hrecover :
      R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
        R.height - 1 := Nat.sub_add_cancel hheight
  have hrem := fkRectPositiveBandBulkBlocks_remainder_lt B hscale
  have hlt : B.start.1.2.val +
      fkRectPositiveBandBulkBlocks B * B.step < R.height := by omega
  rw [fkRectPositiveBandBlockPathVertex_val,
    fkRectEvenRowTranslationVertexEquiv_apply]
  change R.height - 1 - (40 * scale + 6) ≤
    (fkRectRowTranslate R
      (((Fin.last (fkRectPositiveBandBulkBlocks B)).val : Nat) * B.step)
      B.start.1.2).val
  rw [show (Fin.last (fkRectPositiveBandBulkBlocks B)).val =
      fkRectPositiveBandBulkBlocks B by rfl]
  rw [show fkRectRowTranslate R
      ((fkRectPositiveBandBulkBlocks B : Int) * (B.step : Int))
        B.start.1.2 =
      ⟨B.start.1.2.val +
        fkRectPositiveBandBulkBlocks B * B.step, hlt⟩ by
      simpa [Nat.cast_mul] using
        (fkRectRowTranslate_eq_add_of_lt R
          (fkRectPositiveBandBulkBlocks B * B.step) B.start.1.2 hlt)]
  simp only [Fin.val_mk]
  have hstep := B.step_upper
  omega



theorem fkRectCritical_cFE_pow_le_topConnector
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (40 * scale + 7)) ≤
      fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockTopConnectorEvent B hheight) := by
  let lower := R.height - 1 - (40 * scale + 6)
  let S1 := fkRectColumnBand R 1 (4 * scale + 1) lower (R.height - 1)
  have hlower : 1 ≤ lower := by dsimp [lower]; omega
  have hlowerLast : lower < R.height - 1 := by dsimp [lower]; omega
  let x1 : FKRectInducedVertex R S1 :=
    ⟨(fkRectPositiveBandBlockPathVertex B hheight
      (Fin.last (fkRectPositiveBandBulkBlocks B))).1, by
        have hv := (fkRectPositiveBandBlockPathVertex B hheight
          (Fin.last (fkRectPositiveBandBulkBlocks B))).2
        exact ⟨hv.1, hv.2.1,
          fkRectPositiveBandBlockPathVertex_last_row_lower
            B hheight hscale, hv.2.2.2⟩⟩
  let y1 : FKRectInducedVertex R S1 :=
    ⟨fkRectLastRowVertex R (fkRectUnitGapColumn R), by
      change 1 ≤ 1 ∧ 1 ≤ 4 * scale + 1 ∧
        lower ≤ (svFinLast R.height_pos).val ∧
          (svFinLast R.height_pos).val ≤ R.height - 1
      exact ⟨by omega, by omega, by simp [svFinLast]; omega,
        by simp [svFinLast]⟩⟩
  have hbase := fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    R (4 * scale + 1) lower (R.height - 1)
      (by omega) hproper hlowerLast (by omega) hq x1 y1
  have hsubset :
      {omega | FKRectConnectedWithin R omega S1 x1 y1} ⊆
        fkRectPositiveBandBlockTopConnectorEvent B hheight := by
    intro omega homega
    have hmono := homega.mono_set R omega (T :=
        fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) (by
      intro v hv
      exact ⟨hv.1, hv.2.1, hlower.trans hv.2.2.1, hv.2.2.2⟩)
    unfold fkRectPositiveBandBlockTopConnectorEvent
    change FKRectConnectedWithin R omega
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) _ _
    exact hmono
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmonoMass := fkRectCriticalEventMass_mono R hq0 hsubset
  have hheightCount : R.height - 1 + 1 - lower = 40 * scale + 7 := by
    dsimp [lower]
    omega
  simpa [S1, hheightCount] using hbase.trans hmonoMass

theorem fkRectUnitAttachmentOpenEvent_isIncreasing
    (R : FKRectTorus) :
    IsIncreasing (fkRectUnitAttachmentOpenEvent R) := by
  intro omega tau hot homega
  change omega (fkRectRowZeroAttachmentEdgeAt R
    (fkRectUnitGapColumn R)) = true at homega
  change tau (fkRectRowZeroAttachmentEdgeAt R
    (fkRectUnitGapColumn R)) = true
  cases htau : tau (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R))
  · have hle := hot (fkRectRowZeroAttachmentEdgeAt R
        (fkRectUnitGapColumn R))
    rw [homega, htau] at hle
    exact ((by decide : ¬ (true ≤ false)) hle).elim
  · rfl

theorem fkRectCriticalOpenMass_singleton_eq_eventMass
    (R : FKRectTorus) (q : Real) (a : R.EdgeIndex) :
    fkRectCriticalOpenMass R q {a} =
      fkRectCriticalEventMass R q {omega | omega a = true} := by
  classical
  unfold fkRectCriticalOpenMass fkRectCriticalEventMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases h : omega a = true
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

theorem fkRectCritical_cFE_le_unitAttachmentOpenEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ≤
      fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) := by
  have h := fkRectCritical_cFE_pow_le_openMass R hq
    ({fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)} : Finset R.EdgeIndex)
  rw [Finset.card_singleton, pow_one,
    fkRectCriticalOpenMass_singleton_eq_eventMass] at h
  exact h



def fkRectPositiveBandBlockAssembledEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  ((fkRectEvenRowBlockIntersection R B.carrier B.start B.finish
      B.step (fkRectPositiveBandBulkBlocks B) ∩
    fkRectPositiveBandBlockBottomConnectorEvent B hheight) ∩
    fkRectPositiveBandBlockTopConnectorEvent B hheight) ∩
    fkRectUnitAttachmentOpenEvent R

theorem fkRectPositiveBandBlockAssembledEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockAssembledEvent B hheight) := by
  intro omega tau hot hmem
  exact ⟨⟨⟨
    fkRectEvenRowBlockIntersection_isIncreasing
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B) hot hmem.1.1.1,
    fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing
      B hheight hot hmem.1.1.2⟩,
    fkRectPositiveBandBlockTopConnectorEvent_isIncreasing
      B hheight hot hmem.1.2⟩,
    fkRectUnitAttachmentOpenEvent_isIncreasing R hot hmem.2⟩



theorem fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (omega : R.Configuration)
    (hbulk : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B))
    (hbottom : omega ∈
      fkRectPositiveBandBlockBottomConnectorEvent B hheight)
    (htop : omega ∈
      fkRectPositiveBandBlockTopConnectorEvent B hheight)
    (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
    omega ∈ fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  constructor
  · intro pair hpair
    rcases Finset.mem_union.mp hpair with hpair | hpair
    · exact fkRectPositiveBandBlockIntersection_inducedChain
        B hheight omega hbulk pair hpair
    · simp only [fkRectPositiveBandBlockConnectorPairs,
        Finset.mem_insert, Finset.mem_singleton] at hpair
      rcases hpair with rfl | rfl
      · change (FK.openSub
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
          (FK.ocd_innerRestrict Subtype.val
            (fkRectFullGraphConfiguration R omega))).Reachable _ _
        rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
        exact hbottom
      · change (FK.openSub
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
          (FK.ocd_innerRestrict Subtype.val
            (fkRectFullGraphConfiguration R omega))).Reachable _ _
        rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
        exact htop
  · exact hattach

theorem fkRectPositiveBandBlockAssembledEvent_subset_auxiliary
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    fkRectPositiveBandBlockAssembledEvent B hheight ⊆
      fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  intro omega hmem
  exact fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
    B hheight omega hmem.1.1.1 hmem.1.1.2 hmem.1.2 hmem.2



theorem exists_fkRectPositiveBandBlock_localizedVerticalCycle
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hproper : 4 * scale + 2 < R.width)
    (omega : R.Configuration)
    (hbulk : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B))
    (hbottom : omega ∈
      fkRectPositiveBandBlockBottomConnectorEvent B hheight)
    (htop : omega ∈
      fkRectPositiveBandBlockTopConnectorEvent B hheight)
    (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    ∃ z : (fkRectOpenGraph R forced).Walk
        (fkRectRowOneVertex R (fkRectUnitGapColumn R))
        (fkRectRowOneVertex R (fkRectUnitGapColumn R)),
      fkRectWalkWinding R z = (0, 1) ∧
      ∀ v ∈ z.support,
        1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1 := by
  exact exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle
    R (4 * scale + 1) (by omega) hproper omega
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
      (fkRectPositiveBandBlockAuxiliaryPairs_spans B hheight)
      (fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
        B hheight omega hbulk hbottom htop hattach)


theorem fkRectCritical_positiveBandBulkLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hq : 1 ≤ q) :
    B.massFloor ^
        fkRectPositiveBandBulkBlocks B ≤
      fkRectCriticalEventMass R q
        (fkRectEvenRowBlockIntersection R B.carrier B.start B.finish
          B.step (fkRectPositiveBandBulkBlocks B)) := by
  apply fkRectCritical_evenRowBlockLower_pow_le_intersection
    R B.carrier B.start B.finish B.step
      (fkRectPositiveBandBulkBlocks B) B.step_even hq
  · exact B.massFloor_nonneg
  · exact B.mass_lower




theorem fkRectCritical_positiveBandAuxiliaryLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hq : 1 ≤ q)
    {bottom top attachment : Real}
    (hbottom0 : 0 ≤ bottom) (htop0 : 0 ≤ top)
    (hattachment0 : 0 ≤ attachment)
    (hbottom : bottom ≤ fkRectCriticalEventMass R q
      (fkRectPositiveBandBlockBottomConnectorEvent B hheight))
    (htop : top ≤ fkRectCriticalEventMass R q
      (fkRectPositiveBandBlockTopConnectorEvent B hheight))
    (hattachment : attachment ≤ fkRectCriticalEventMass R q
      (fkRectUnitAttachmentOpenEvent R)) :
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
      fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
          (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
  let A := fkRectEvenRowBlockIntersection
    R B.carrier B.start B.finish B.step
      (fkRectPositiveBandBulkBlocks B)
  let C := fkRectPositiveBandBlockBottomConnectorEvent B hheight
  let D := fkRectPositiveBandBlockTopConnectorEvent B hheight
  let E := fkRectUnitAttachmentOpenEvent R
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hAinc : IsIncreasing A :=
    fkRectEvenRowBlockIntersection_isIncreasing
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B)
  have hCinc : IsIncreasing C :=
    fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing B hheight
  have hDinc : IsIncreasing D :=
    fkRectPositiveBandBlockTopConnectorEvent_isIncreasing B hheight
  have hEinc : IsIncreasing E := fkRectUnitAttachmentOpenEvent_isIncreasing R
  have hACinc : IsIncreasing (A ∩ C) := by
    intro omega tau hot hmem
    exact ⟨hAinc hot hmem.1, hCinc hot hmem.2⟩
  have hACDinc : IsIncreasing ((A ∩ C) ∩ D) := by
    intro omega tau hot hmem
    exact ⟨hACinc hot hmem.1, hDinc hot hmem.2⟩
  have hmA0 := fkRectCriticalEventMass_nonneg R hq0 A
  have hmC0 := fkRectCriticalEventMass_nonneg R hq0 C
  have hmD0 := fkRectCriticalEventMass_nonneg R hq0 D
  have hmE0 := fkRectCriticalEventMass_nonneg R hq0 E
  have hsource0 : 0 ≤ B.massFloor ^
      fkRectPositiveBandBulkBlocks B :=
    pow_nonneg B.massFloor_nonneg _
  have hbulk : B.massFloor ^
        fkRectPositiveBandBulkBlocks B ≤
      fkRectCriticalEventMass R q A := by
    exact fkRectCritical_positiveBandBulkLower B hq
  have hlower :
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
        ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E := by
    calc
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
          ((fkRectCriticalEventMass R q A * bottom) * top) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            apply mul_le_mul_of_nonneg_right _ htop0
            exact mul_le_mul_of_nonneg_right hbulk hbottom0
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) * top) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            apply mul_le_mul_of_nonneg_right _ htop0
            exact mul_le_mul_of_nonneg_left hbottom hmA0
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            exact mul_le_mul_of_nonneg_left htop
              (mul_nonneg hmA0 hmC0)
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E :=
            mul_le_mul_of_nonneg_left hattachment
              (mul_nonneg (mul_nonneg hmA0 hmC0) hmD0)
  have hproduct :
      ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E ≤
        fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) := by
    calc
      ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E ≤
          (fkRectCriticalEventMass R q (A ∩ C) *
            fkRectCriticalEventMass R q D) *
              fkRectCriticalEventMass R q E := by
            apply mul_le_mul_of_nonneg_right _ hmE0
            apply mul_le_mul_of_nonneg_right _ hmD0
            exact fkRectCriticalEventMass_mul_le_inter R hq hAinc hCinc
      _ ≤ fkRectCriticalEventMass R q ((A ∩ C) ∩ D) *
            fkRectCriticalEventMass R q E := by
            exact mul_le_mul_of_nonneg_right
              (fkRectCriticalEventMass_mul_le_inter
                R hq hACinc hDinc) hmE0
      _ ≤ fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) :=
            fkRectCriticalEventMass_mul_le_inter R hq hACDinc hEinc
  calc
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
      fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) :=
        hlower.trans hproduct
    _ = fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockAssembledEvent B hheight) := by rfl
    _ ≤ fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
          (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) :=
      fkRectCriticalEventMass_mono R hq0
        (fkRectPositiveBandBlockAssembledEvent_subset_auxiliary B hheight)


theorem fkRectCritical_concretePositiveBandAuxiliaryLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (24 * scale + 4))) *
      FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (40 * scale + 7))) *
      FK.cFE (fkRectCriticalP q) q ≤
    fkRectCriticalEventMass R q
      (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    (FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le
  exact fkRectCritical_positiveBandAuxiliaryLower B hheight hq
    (pow_nonneg hc _) (pow_nonneg hc _) hc
    (fkRectCritical_cFE_pow_le_bottomConnector
      B hheight hproper hq)
    (fkRectCritical_cFE_pow_le_topConnector
      B hheight hscale htall hproper hq)
    (fkRectCritical_cFE_le_unitAttachmentOpenEvent R hq)




theorem fkRectCritical_concretePositiveBandDualBarrierLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 2 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
      (((B.massFloor ^
            fkRectPositiveBandBulkBlocks B *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q) ≤
      fkRectCriticalEventMass R q
        (fkRectDualPullbackSourceLeftBarrier R (4 * scale + 1)
          (fkRectUnitLeftBarrierGap R)) := by
  let A := fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
    (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
  have haux :
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q ≤
      fkRectCriticalEventMass R q A :=
    fkRectCritical_concretePositiveBandAuxiliaryLower
      B hheight hscale htall (by omega) hq
  have hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R
          (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
          (fkRectDualPullbackConfiguration R
            (fkRectAllButOneOpenConfiguration R
              (fkRectUnitLeftBarrierGap R))) omega ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R (4 * scale + 1)) := by
    intro omega homega
    exact fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing
      R (4 * scale + 1) (by omega) (by omega) omega
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
        (fkRectPositiveBandBlockAuxiliaryPairs_spans B hheight) homega
  have hpattern :=
    fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource
      R (4 * scale + 1) hq (fkRectUnitLeftBarrierGap R) A hforce
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    (FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le
  exact (mul_le_mul_of_nonneg_left haux
    (pow_nonneg hc _)).trans hpattern




theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow
    (k scale leftRight : Nat) (hone : 1 ≤ leftRight)
    (hleft : leftRight + 1 < 2 * (k + 3))
    {q C a : Real} (hq : 1 ≤ q) (hC : 0 < C) (ha : 0 < a)
    (haux : ∀ᶠ blocks in atTop,
      C * a ^ (blocks + 1) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
        -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
  intro epsilon hepsilon
  let blockCost : Nat → Real := fun blocks ↦
    ((blocks + 1 : Nat) : Real) * (-Real.log a) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  let dualConstant : Real := -Real.log ((1 / q) * C)
  let dualCost : Nat → Real := fun blocks ↦
    dualConstant /
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
  have hheight : Tendsto (fun blocks ↦
      ((fkRectWindingBlockVerticalFamily k scale blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  have hdual : Tendsto dualCost atTop (nhds 0) :=
    hheight.const_div_atTop dualConstant
  have hevent : ∀ᶠ blocks in atTop,
      blockCost blocks + dualCost blocks <
        -Real.log a / (2 * (scale + 1) : Real) + epsilon :=
    (tendsto_order.1 (hblock.add hdual)).2 _ (by linarith)
  filter_upwards [hevent, haux] with blocks hcost hbound
  have hfinite := fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow
    (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (blocks + 1)
    hone hleft hq hC ha hbound
  change -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
      -Real.log a / (2 * (scale + 1) : Real) + epsilon
  dsimp [blockCost, dualCost, dualConstant] at hcost
  exact hfinite.trans hcost.le

end

end StatMech.FrontierD
