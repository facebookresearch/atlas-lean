/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexEndpointWalk

namespace StatMech.Universality

open HexWalk
open scoped BigOperators

noncomputable section


noncomputable def hexEndpointSAWwt
    (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable (ofTurns a h0 ts).EndpointIsLegalSAW
  if (ofTurns a h0 ts).EndpointIsLegalSAW then
    x ^ (ofTurns a h0 ts).endpointNumVertices
  else 0

theorem hexEndpointSAWwt_nonneg
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ hexEndpointSAWwt a h0 x ts := by
  unfold hexEndpointSAWwt
  split
  · exact pow_nonneg hx _
  · exact le_rfl


noncomputable def hexEndpointTruncFinset
    (a : ℂ) (h0 : ℤ) (N : ℕ) : Finset (List ℤ) :=
  (Finset.range N).biUnion (hexEndpointSAWFinset a h0)

theorem hexEndpoint_mem_truncFinset
    (a : ℂ) (h0 : ℤ) (N : ℕ) (ts : List ℤ) :
    ts ∈ hexEndpointTruncFinset a h0 N ↔
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧ ts.length < N := by
  classical
  rw [hexEndpointTruncFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨n, hn, hts⟩
    have hm := (hexEndpoint_mem_sawFinset a h0 n ts).mp hts
    exact ⟨hm.1, hm.2.symm ▸ Finset.mem_range.mp hn⟩
  · rintro ⟨hlegal, hlen⟩
    exact ⟨ts.length, Finset.mem_range.mpr hlen,
      (hexEndpoint_mem_sawFinset a h0 ts.length ts).2
        ⟨hlegal, rfl⟩⟩

theorem hexEndpoint_levels_disjoint
    (a : ℂ) (h0 : ℤ) {n m : ℕ} (hne : n ≠ m) :
    Disjoint (hexEndpointSAWFinset a h0 n)
      (hexEndpointSAWFinset a h0 m) := by
  classical
  rw [Finset.disjoint_left]
  intro ts hn hm
  have hnl := (hexEndpoint_mem_sawFinset a h0 n ts).mp hn |>.2
  have hml := (hexEndpoint_mem_sawFinset a h0 m ts).mp hm |>.2
  exact hne (hnl.symm.trans hml)

theorem hexEndpoint_level_sum
    (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) :
    ∑ ts ∈ hexEndpointSAWFinset a h0 n,
        hexEndpointSAWwt a h0 x ts =
      hexEndpointCoeffWeight a h0 x n := by
  classical
  calc
    ∑ ts ∈ hexEndpointSAWFinset a h0 n,
        hexEndpointSAWwt a h0 x ts =
        ∑ _ts ∈ hexEndpointSAWFinset a h0 n, x ^ n := by
      apply Finset.sum_congr rfl
      intro ts hts
      have hm := (hexEndpoint_mem_sawFinset a h0 n ts).mp hts
      simp [hexEndpointSAWwt, hm.1, endpointNumVertices, hm.2]
    _ = (hexEndpointSAWFinset a h0 n).card * x ^ n := by simp
    _ = hexEndpointCoeffWeight a h0 x n := by
      simp [hexEndpointCoeffWeight, hexEndpointSAWCountR,
        hexEndpointSAWCount]


theorem hexEndpoint_trunc_sum_eq_coeff_sum
    (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hexEndpointTruncFinset a h0 N,
        hexEndpointSAWwt a h0 x ts =
      ∑ n ∈ Finset.range N, hexEndpointCoeffWeight a h0 x n := by
  classical
  have hdisj : ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (hexEndpointSAWFinset a h0) := by
    intro n hn m hm hnm
    rw [Function.onFun]
    exact hexEndpoint_levels_disjoint a h0 hnm
  unfold hexEndpointTruncFinset
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro n _
  exact hexEndpoint_level_sum a h0 x n


theorem hexEndpoint_finset_sum_le_trunc_sum
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (s : Finset (List ℤ)) :
    ∑ ts ∈ s, hexEndpointSAWwt a h0 x ts ≤
      ∑ ts ∈ hexEndpointTruncFinset a h0
          (s.sup List.length + 1), hexEndpointSAWwt a h0 x ts := by
  classical
  let legal : Finset (List ℤ) :=
    s.filter (fun ts => (ofTurns a h0 ts).EndpointIsLegalSAW)
  have hsum :
      (∑ ts ∈ legal, hexEndpointSAWwt a h0 x ts) =
        ∑ ts ∈ s, hexEndpointSAWwt a h0 x ts := by
    apply Finset.sum_filter_of_ne
    intro ts hts hne
    unfold hexEndpointSAWwt at hne
    split at hne
    · assumption
    · contradiction
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ts hts
    simp only [legal, Finset.mem_filter] at hts
    rw [hexEndpoint_mem_truncFinset]
    exact ⟨hts.2, Nat.lt_succ_of_le
      (Finset.le_sup (f := List.length) hts.1)⟩
  · intro ts _ _
    exact hexEndpointSAWwt_nonneg a h0 hx ts

theorem hexEndpoint_coeffWeight_nonneg
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ hexEndpointCoeffWeight a h0 x n := by
  unfold hexEndpointCoeffWeight hexEndpointSAWCountR
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)


theorem hexEndpoint_coeff_summable_of_walk_summable
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hwalk : Summable (hexEndpointSAWwt a h0 x)) :
    Summable (hexEndpointCoeffWeight a h0 x) := by
  refine summable_of_sum_range_le
    (f := hexEndpointCoeffWeight a h0 x)
    (c := ∑' ts, hexEndpointSAWwt a h0 x ts)
    (hexEndpoint_coeffWeight_nonneg a h0 hx) ?_
  intro N
  rw [← hexEndpoint_trunc_sum_eq_coeff_sum]
  exact Summable.sum_le_tsum _
    (fun ts _ => hexEndpointSAWwt_nonneg a h0 hx ts) hwalk


theorem hexEndpoint_walk_summable_of_coeff_summable
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hcoeff : Summable (hexEndpointCoeffWeight a h0 x)) :
    Summable (hexEndpointSAWwt a h0 x) := by
  refine summable_of_sum_le
    (f := hexEndpointSAWwt a h0 x)
    (c := ∑' n, hexEndpointCoeffWeight a h0 x n)
    (hexEndpointSAWwt_nonneg a h0 hx) ?_
  intro s
  let N := s.sup List.length + 1
  calc
    ∑ ts ∈ s, hexEndpointSAWwt a h0 x ts ≤
        ∑ ts ∈ hexEndpointTruncFinset a h0 N,
          hexEndpointSAWwt a h0 x ts := by
      exact hexEndpoint_finset_sum_le_trunc_sum a h0 hx s
    _ = ∑ n ∈ Finset.range N, hexEndpointCoeffWeight a h0 x n :=
      hexEndpoint_trunc_sum_eq_coeff_sum a h0 x N
    _ ≤ ∑' n, hexEndpointCoeffWeight a h0 x n :=
      Summable.sum_le_tsum _
        (fun n _ => hexEndpoint_coeffWeight_nonneg a h0 hx n) hcoeff



theorem hexEndpoint_walk_summable_iff_coeff_summable
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (hexEndpointSAWwt a h0 x) ↔
      Summable (hexEndpointCoeffWeight a h0 x) :=
  ⟨hexEndpoint_coeff_summable_of_walk_summable a h0 hx,
    hexEndpoint_walk_summable_of_coeff_summable a h0 hx⟩



theorem hexEndpoint_walk_summable_iff_hlc
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x) :
    Summable (hexEndpointSAWwt a h0 x) ↔
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  (hexEndpoint_walk_summable_iff_coeff_summable a h0 hx.le).trans
    (hexEndpoint_summable_iff_hlc_of_pos a h0 hx)



theorem hexEndpoint_hlc_not_summable_of_walk
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (hdiv : ¬ Summable (hexEndpointSAWwt a h0 x)) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  (not_congr (hexEndpoint_walk_summable_iff_hlc a h0 hx)).mp hdiv

end

end StatMech.Universality
