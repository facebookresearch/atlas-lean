/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Mathlib
import Code.Universality.HexZConvClose
import Code.Universality.HexLiteralCountLaws

namespace StatMech.Universality

open scoped BigOperators
open HexWalk




noncomputable def hzc_coeffWeight (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) : ℝ :=
  (hzc_sawCount a h0 n : ℝ) * x ^ n


theorem hzc_coeffWeight_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ hzc_coeffWeight a h0 x n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)


@[simp] theorem hzc_coeffWeight_zero (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hzc_coeffWeight a h0 x 0 = 0 := by
  simp [hzc_coeffWeight, hzc_sawCount_zero]


@[simp] theorem hzc_hexSAWwt_zero_fugacity (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    hexSAWwt a h0 0 ts = 0 := by
  unfold hexSAWwt
  split
  · rw [numVertices_eq]
    simp
  · rfl


@[simp] theorem hzc_coeffWeight_zero_fugacity (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hzc_coeffWeight a h0 0 n = 0 := by
  cases n with
  | zero => exact hzc_coeffWeight_zero a h0 0
  | succ n => simp [hzc_coeffWeight]





theorem hzc_truncFinset_eq_empty_of_le_one (a : ℂ) (h0 : ℤ) {N : ℕ} (hN : N ≤ 1) :
    hzc_truncFinset a h0 N = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ts hts
  have hlt := ((hzc_mem_truncFinset a h0 N ts).mp hts).2
  rw [numVertices_eq] at hlt
  omega

@[simp] theorem hzc_truncFinset_zero (a : ℂ) (h0 : ℤ) :
    hzc_truncFinset a h0 0 = ∅ :=
  hzc_truncFinset_eq_empty_of_le_one a h0 (by omega)

@[simp] theorem hzc_truncFinset_one (a : ℂ) (h0 : ℤ) :
    hzc_truncFinset a h0 1 = ∅ :=
  hzc_truncFinset_eq_empty_of_le_one a h0 (le_refl 1)



theorem hzc_trunc_sum_eq_coeff_sum (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts =
      ∑ n ∈ Finset.range N, hzc_coeffWeight a h0 x n := by
  simpa only [hzc_coeffWeight] using hzc_partial_eq a h0 x N






theorem hzc_finset_sum_le_trunc_sum (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (s : Finset (List ℤ)) :
    ∑ ts ∈ s, hexSAWwt a h0 x ts ≤
      ∑ ts ∈ hzc_truncFinset a h0
        (s.sup (fun ts => (ofTurns a h0 ts).numVertices) + 1), hexSAWwt a h0 x ts := by
  classical
  let legal : Finset (List ℤ) :=
    s.filter (fun ts => (ofTurns a h0 ts).IsLegalSAW)
  have hsum :
      (∑ ts ∈ legal, hexSAWwt a h0 x ts) = ∑ ts ∈ s, hexSAWwt a h0 x ts := by
    apply Finset.sum_filter_of_ne
    intro ts hts hne
    unfold hexSAWwt at hne
    split at hne
    · assumption
    · contradiction
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ts hts
    simp only [legal, Finset.mem_filter] at hts
    rw [hzc_mem_truncFinset]
    exact ⟨hts.2, Nat.lt_succ_of_le
      (Finset.le_sup (f := fun ts : List ℤ => (ofTurns a h0 ts).numVertices) hts.1)⟩
  · intro ts _ _
    exact hexSAWwt_nonneg a h0 hx ts





theorem hzc_coeff_summable_of_walk_summable (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hwalk : Summable (hexSAWwt a h0 x)) :
    Summable (hzc_coeffWeight a h0 x) := by
  refine summable_of_sum_range_le
    (f := hzc_coeffWeight a h0 x) (c := ∑' ts, hexSAWwt a h0 x ts)
    (hzc_coeffWeight_nonneg a h0 hx) ?_
  intro N
  rw [← hzc_trunc_sum_eq_coeff_sum]
  exact Summable.sum_le_tsum _ (fun ts _ => hexSAWwt_nonneg a h0 hx ts) hwalk



theorem hzc_walk_summable_of_coeff_summable (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hcoeff : Summable (hzc_coeffWeight a h0 x)) :
    Summable (hexSAWwt a h0 x) := by
  refine summable_of_sum_le
    (f := hexSAWwt a h0 x) (c := ∑' n, hzc_coeffWeight a h0 x n)
    (fun ts => hexSAWwt_nonneg a h0 hx ts) ?_
  intro s
  let N := s.sup (fun ts => (ofTurns a h0 ts).numVertices) + 1
  calc
    ∑ ts ∈ s, hexSAWwt a h0 x ts ≤
        ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts := by
          exact hzc_finset_sum_le_trunc_sum a h0 hx s
    _ = ∑ n ∈ Finset.range N, hzc_coeffWeight a h0 x n :=
      hzc_trunc_sum_eq_coeff_sum a h0 x N
    _ ≤ ∑' n, hzc_coeffWeight a h0 x n :=
      Summable.sum_le_tsum _ (fun n _ => hzc_coeffWeight_nonneg a h0 hx n) hcoeff




theorem hzc_walk_summable_iff_coeff_summable (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (hexSAWwt a h0 x) ↔ Summable (hzc_coeffWeight a h0 x) :=
  ⟨hzc_coeff_summable_of_walk_summable a h0 hx,
    hzc_walk_summable_of_coeff_summable a h0 hx⟩





theorem hzc_tsum_eq_coeff_tsum_of_summable (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hwalk : Summable (hexSAWwt a h0 x)) :
    (∑' ts, hexSAWwt a h0 x ts) = ∑' n, hzc_coeffWeight a h0 x n := by
  have hcoeff := hzc_coeff_summable_of_walk_summable a h0 hx hwalk
  apply le_antisymm
  · apply hwalk.tsum_le_of_sum_le
    intro s
    let N := s.sup (fun ts => (ofTurns a h0 ts).numVertices) + 1
    calc
      ∑ ts ∈ s, hexSAWwt a h0 x ts ≤
          ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts := by
            exact hzc_finset_sum_le_trunc_sum a h0 hx s
      _ = ∑ n ∈ Finset.range N, hzc_coeffWeight a h0 x n :=
        hzc_trunc_sum_eq_coeff_sum a h0 x N
      _ ≤ ∑' n, hzc_coeffWeight a h0 x n :=
        Summable.sum_le_tsum _ (fun n _ => hzc_coeffWeight_nonneg a h0 hx n) hcoeff
  · apply Real.tsum_le_of_sum_range_le (hzc_coeffWeight_nonneg a h0 hx)
    intro N
    rw [← hzc_trunc_sum_eq_coeff_sum]
    exact Summable.sum_le_tsum _ (fun ts _ => hexSAWwt_nonneg a h0 hx ts) hwalk




theorem hzc_tsum_eq_coeff_tsum (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' ts, hexSAWwt a h0 x ts) = ∑' n, hzc_coeffWeight a h0 x n := by
  by_cases hwalk : Summable (hexSAWwt a h0 x)
  · exact hzc_tsum_eq_coeff_tsum_of_summable a h0 hx hwalk
  · have hcoeff : ¬ Summable (hzc_coeffWeight a h0 x) := by
      simpa only [hzc_walk_summable_iff_coeff_summable a h0 hx] using hwalk
    rw [tsum_eq_zero_of_not_summable hwalk, tsum_eq_zero_of_not_summable hcoeff]



theorem hzc_trunc_sum_tendsto (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hwalk : Summable (hexSAWwt a h0 x)) :
    Filter.Tendsto
      (fun N => ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts)
      Filter.atTop (nhds (∑' ts, hexSAWwt a h0 x ts)) := by
  have hcoeff := hzc_coeff_summable_of_walk_summable a h0 hx hwalk
  rw [hzc_tsum_eq_coeff_tsum_of_summable a h0 hx hwalk]
  convert hcoeff.hasSum.tendsto_sum_nat using 1
  ext N
  exact hzc_trunc_sum_eq_coeff_sum a h0 x N


theorem hzc_walk_hasSum_iff_coeff_hasSum (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (z : ℝ) :
    HasSum (hexSAWwt a h0 x) z ↔ HasSum (hzc_coeffWeight a h0 x) z := by
  constructor
  · intro hwalk
    have hcoeff := hzc_coeff_summable_of_walk_summable a h0 hx hwalk.summable
    rw [← hwalk.tsum_eq, hzc_tsum_eq_coeff_tsum a h0 hx]
    exact hcoeff.hasSum
  · intro hcoeff
    have hwalk := hzc_walk_summable_of_coeff_summable a h0 hx hcoeff.summable
    rw [← hcoeff.tsum_eq, ← hzc_tsum_eq_coeff_tsum a h0 hx]
    exact hwalk.hasSum




theorem hzc_summable_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) ↔
      Summable (fun n : ℕ => (hzc_sawCount a h0 n : ℝ) * x ^ n) := by
  simpa only [hzc_coeffWeight] using hzc_walk_summable_iff_coeff_summable a h0 hx


theorem hzc_tsum_eq (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' ts : List ℤ, hexSAWwt a h0 x ts) =
      ∑' n : ℕ, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
  simpa only [hzc_coeffWeight] using hzc_tsum_eq_coeff_tsum a h0 hx


theorem hzc_hasSum_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (z : ℝ) :
    HasSum (fun ts : List ℤ => hexSAWwt a h0 x ts) z ↔
      HasSum (fun n : ℕ => (hzc_sawCount a h0 n : ℝ) * x ^ n) z := by
  simpa only [hzc_coeffWeight] using hzc_walk_hasSum_iff_coeff_hasSum a h0 hx z






noncomputable def hlc_coeffWeight (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) : ℝ :=
  (hlc_sawCount a h0 n : ℝ) * x ^ n

theorem hlc_coeffWeight_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ hlc_coeffWeight a h0 x n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)


@[simp] theorem hlc_coeffWeight_zero (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hlc_coeffWeight a h0 x 0 = 1 := by
  simp [hlc_coeffWeight, hlc_sawCount_zero]



@[simp] theorem hlc_coeffWeight_zero_fugacity (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hlc_coeffWeight a h0 0 n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simp [hlc_coeffWeight]


theorem hzc_coeffWeight_succ_eq_mul_hlc (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) :
    hzc_coeffWeight a h0 x (n + 1) = x * hlc_coeffWeight a h0 x n := by
  unfold hzc_coeffWeight hlc_coeffWeight hlc_sawCount
  rw [pow_succ]
  ring



theorem hzc_coeff_sum_shift (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), hzc_coeffWeight a h0 x k =
      x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ (f := hzc_coeffWeight a h0 x) (n := N + 1), ih,
        Finset.sum_range_succ (f := hlc_coeffWeight a h0 x) (n := N), mul_add,
        hzc_coeffWeight_succ_eq_mul_hlc]



theorem hlc_trunc_sum_eq_mul_coeff_sum (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hzc_truncFinset a h0 (N + 1), hexSAWwt a h0 x ts =
      x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
  rw [hzc_trunc_sum_eq_coeff_sum, hzc_coeff_sum_shift]







theorem hzc_coeff_summable_iff_hlc_coeff_summable
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (hzc_coeffWeight a h0 x) ↔ Summable (hlc_coeffWeight a h0 x) := by
  rcases hx.eq_or_lt with rfl | hx
  · constructor
    · intro _
      exact (hasSum_single 0 (fun n hn => by simp [hn])).summable
    · intro _
      exact (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr
        (fun n => (hzc_coeffWeight_zero_fugacity a h0 n).symm)
  · calc
      Summable (hzc_coeffWeight a h0 x) ↔
          Summable (fun n => hzc_coeffWeight a h0 x (n + 1)) :=
        (summable_nat_add_iff 1).symm
      _ ↔ Summable (fun n => x * hlc_coeffWeight a h0 x n) :=
        summable_congr (hzc_coeffWeight_succ_eq_mul_hlc a h0 x)
      _ ↔ Summable (hlc_coeffWeight a h0 x) := summable_mul_left_iff hx.ne'




theorem hlc_summable_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) ↔
      Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) := by
  exact (hzc_walk_summable_iff_coeff_summable a h0 hx).trans
    ((hzc_coeff_summable_iff_hlc_coeff_summable a h0 hx).trans
      (by rfl : Summable (hlc_coeffWeight a h0 x) ↔
        Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n)))



theorem hzc_coeff_tsum_eq_mul_hlc_coeff_tsum
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' n, hzc_coeffWeight a h0 x n) = x * ∑' n, hlc_coeffWeight a h0 x n := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · by_cases hvertex : Summable (hzc_coeffWeight a h0 x)
    · have htail := hvertex.sum_add_tsum_nat_add 1
      calc
        (∑' n, hzc_coeffWeight a h0 x n) =
            ∑' n, hzc_coeffWeight a h0 x (n + 1) := by
              simpa using htail.symm
        _ = ∑' n, x * hlc_coeffWeight a h0 x n := by
          apply tsum_congr
          exact hzc_coeffWeight_succ_eq_mul_hlc a h0 x
        _ = x * ∑' n, hlc_coeffWeight a h0 x n := tsum_mul_left
    · have hstep : ¬ Summable (hlc_coeffWeight a h0 x) := by
        rwa [hzc_coeff_summable_iff_hlc_coeff_summable a h0 hx.le] at hvertex
      rw [tsum_eq_zero_of_not_summable hvertex, tsum_eq_zero_of_not_summable hstep, mul_zero]





theorem hlc_tsum_eq (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' ts : List ℤ, hexSAWwt a h0 x ts) =
      x * ∑' n : ℕ, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
  rw [hzc_tsum_eq_coeff_tsum a h0 hx,
    hzc_coeff_tsum_eq_mul_hlc_coeff_tsum a h0 hx]
  rfl



theorem hlc_walk_hasSum_of_coeff_hasSum (a : ℂ) (h0 : ℤ) {x z : ℝ} (hx : 0 ≤ x)
    (hcoeff : HasSum (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) z) :
    HasSum (fun ts : List ℤ => hexSAWwt a h0 x ts) (x * z) := by
  have hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) :=
    (hlc_summable_iff a h0 hx).mpr hcoeff.summable
  rw [← hcoeff.tsum_eq, ← hlc_tsum_eq a h0 hx]
  exact hwalk.hasSum

end StatMech.Universality
