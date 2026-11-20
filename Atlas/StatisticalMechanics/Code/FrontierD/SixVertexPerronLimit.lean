/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPerronNoAdjacent









open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexSectorTransferNormalized
    (N n : Nat) (c : Real) : Matrix (SixVertexSector N n)
      (SixVertexSector N n) Real :=
  fun x y => sixVertexSectorTransfer N n c x y / (c ^ 2 - 2) ^ n


def sixVertexSectorTransferNormalizedMaxRowSum
    (N n : Nat) (hn : n ≤ N) (c : Real) : Real :=
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  (Finset.univ : Finset (SixVertexSector N n)).sup'
    Finset.univ_nonempty
    (fun x => ∑ y, sixVertexSectorTransferNormalized N n c x y)



theorem sixVertexSectorTop_div_le_normalizedMaxRowSum
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c)
    (hden : 0 < (c ^ 2 - 2) ^ n) :
    sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n ≤
      sixVertexSectorTransferNormalizedMaxRowSum N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector hn hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image
    (Finset.univ : Finset (SixVertexSector N n)) (fun x => v x)
    Finset.univ_nonempty
  have hcoord := congrFun hveig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcoord
  have hsum :
      (∑ j, sixVertexSectorTransferNormalized N n c i j * v j) ≤
        (∑ j, sixVertexSectorTransferNormalized N n c i j) * v i := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j))
    exact div_nonneg (sixVertexSectorTransfer_nonneg hc.le i j) hden.le
  have heq :
      (∑ j, sixVertexSectorTransferNormalized N n c i j * v j) =
        (sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n) * v i := by
    calc
      (∑ j, sixVertexSectorTransferNormalized N n c i j * v j) =
          (∑ j, sixVertexSectorTransfer N n c i j * v j) /
            (c ^ 2 - 2) ^ n := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              simp only [sixVertexSectorTransferNormalized]
              ring
      _ = (sixVertexSectorTopEigenvalue N n hn c * v i) /
          (c ^ 2 - 2) ^ n := by rw [hcoord]
      _ = _ := by ring
  have hrow :
      sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n ≤
        ∑ j, sixVertexSectorTransferNormalized N n c i j := by
    rw [heq] at hsum
    nlinarith [hvpos i]
  exact hrow.trans <| Finset.le_sup'
    (fun x => ∑ y, sixVertexSectorTransferNormalized N n c x y)
    (Finset.mem_univ i)



theorem sixVertexSectorTransfer_entry_le_top
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransfer N n c x y ≤
      sixVertexSectorTopEigenvalue N n hn c := by
  classical
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector hn hc
  have hx := congrFun hveig x
  have hy := congrFun hveig y
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx hy
  have hxy : sixVertexSectorTransfer N n c x y * v y ≤
      sixVertexSectorTopEigenvalue N n hn c * v x := by
    rw [← hx]
    exact Finset.single_le_sum
      (fun z _ => mul_nonneg (sixVertexSectorTransfer_nonneg hc.le x z)
        (hvpos z).le)
      (Finset.mem_univ y)
  have hyx : sixVertexSectorTransfer N n c x y * v x ≤
      sixVertexSectorTopEigenvalue N n hn c * v y := by
    have hsym : sixVertexSectorTransfer N n c y x =
        sixVertexSectorTransfer N n c x y :=
      sixVertexTransfer_symmetric N c
        (sixVertexSectorRow y) (sixVertexSectorRow x)
    rw [← hsym]
    rw [← hy]
    exact Finset.single_le_sum
      (fun z _ => mul_nonneg (sixVertexSectorTransfer_nonneg hc.le y z)
        (hvpos z).le)
      (Finset.mem_univ x)
  have hprod := mul_le_mul hxy hyx
    (mul_nonneg (sixVertexSectorTransfer_nonneg hc.le x y) (hvpos x).le)
    (mul_nonneg (sixVertexSectorTopEigenvalue_pos hn hc).le (hvpos x).le)
  have hvxy : 0 < v x * v y := mul_pos (hvpos x) (hvpos y)
  have hsq : sixVertexSectorTransfer N n c x y ^ 2 ≤
      sixVertexSectorTopEigenvalue N n hn c ^ 2 := by
    nlinarith [hprod]
  nlinarith [sixVertexSectorTransfer_nonneg hc.le x y,
    sixVertexSectorTopEigenvalue_pos hn hc]



theorem tendsto_sixVertexSectorTransferNormalizedMaxRowSum_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    Tendsto (sixVertexSectorTransferNormalizedMaxRowSum N n (by omega))
      atTop (nhds 1) := by
  classical
  have hnN : n ≤ N := by omega
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hnN
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  let limitRow : SixVertexSector N n → Real := fun x =>
    if x = even then 1 else if x = odd then 1 else 0
  have hrow (x : SixVertexSector N n) :
      Tendsto (fun c => ∑ y, sixVertexSectorTransferNormalized N n c x y)
        atTop (nhds (limitRow x)) := by
    have hsum := tendsto_finset_sum (s := Finset.univ)
      (fun y _ => tendsto_sixVertexSectorTransfer_normalized_atTop hn x y)
    have hlimit : ∑ y, sixVertexSectorTransferInfinity N n x y = limitRow x := by
      have hmul := sixVertexSectorTransferInfinity_mulVec_half hn hhalf
        (fun _ => (1 : Real)) x
      rw [Matrix.mulVec, dotProduct] at hmul
      simpa [limitRow, even, odd] using hmul
    simpa [sixVertexSectorTransferNormalized, hlimit] using hsum
  have hsup := Filter.Tendsto.finset_sup'_nhds_apply
    (s := (Finset.univ : Finset (SixVertexSector N n)))
    Finset.univ_nonempty (fun x hx => hrow x)
  have hlimitSup :
      (Finset.univ : Finset (SixVertexSector N n)).sup'
          Finset.univ_nonempty limitRow = 1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro x hx
      simp only [limitRow]
      split_ifs <;> norm_num
    · have heven : limitRow even = 1 := by simp [limitRow, even]
      rw [← heven]
      exact Finset.le_sup' limitRow (Finset.mem_univ even)
  simpa [sixVertexSectorTransferNormalizedMaxRowSum, hlimitSup] using hsup



theorem tendsto_sixVertexSectorTop_normalized_atTop_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    Tendsto (fun c =>
      sixVertexSectorTopEigenvalue N n (by omega) c / (c ^ 2 - 2) ^ n)
      atTop (nhds 1) := by
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hlower : Tendsto (fun c =>
      sixVertexSectorTransferNormalized N n c even odd) atTop (nhds 1) := by
    have h := tendsto_sixVertexSectorTransfer_normalized_atTop hn even odd
    have hadj := sixVertexInfinityGraph_adj_alternating_of_half hn hhalf
    have hinf : sixVertexSectorTransferInfinity N n even odd = 1 := by
      rw [sixVertexSectorTransferInfinity_apply]
      exact if_pos hadj
    simpa [sixVertexSectorTransferNormalized, hinf] using h
  have hupper :=
    tendsto_sixVertexSectorTransferNormalizedMaxRowSum_half hn hhalf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    have hc0 : 0 < c := by linarith
    have hden : 0 < (c ^ 2 - 2) ^ n := pow_pos (by nlinarith) n
    exact (div_le_div_iff_of_pos_right hden).2
      (sixVertexSectorTransfer_entry_le_top (by omega) hc0 even odd)
  · filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexSectorTop_div_le_normalizedMaxRowSum (by omega)
      (by linarith) (pow_pos (by nlinarith) n)

end

end StatMech.FrontierD
