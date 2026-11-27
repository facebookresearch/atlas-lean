/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Powerset

/-! # Subset counts for the Wilcoxon signed-rank test -/

namespace WantedExt.Probability.Statistics.WilcoxonSignedRankWanted

@[expose] public section

/-- **Number of subsets with a given sum.** The number `c_n(t)` of subsets of `{1, …, n}` with
sum `t`. -/
def subsetSumCount (n t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
    fun S : Finset (Fin n) => (∑ j ∈ S, ((j : ℕ) + 1)) = t).card

private def rankSum (S : Finset ℕ) : ℕ := ∑ j ∈ S, (j + 1)

private def cumulativeCount (s : Finset ℕ) (t : ℕ) : ℕ :=
  (s.powerset.filter fun S => rankSum S ≤ t).card

private theorem sum_subsetSumCount_eq_cumulativeCount (n t : ℕ) :
    ∑ i ∈ Finset.range (t + 1), subsetSumCount n i =
      cumulativeCount (Finset.range n) t := by
  unfold subsetSumCount cumulativeCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  let e : Fin n ↪ ℕ := Fin.valEmbedding
  have he (i : Fin n) : e i = i.val := rfl
  apply Finset.card_bij (fun S _ => S.map e)
  · intro S hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
      exact Finset.mem_range.mpr i.isLt
    · simpa only [rankSum, Finset.sum_map, he, Finset.mem_range, Nat.lt_succ_iff] using
        (Finset.mem_filter.mp hS).2
  · intro S₁ _ S₂ _ h
    exact Finset.map_injective e h
  · intro T hT
    have hTr : T ⊆ Finset.range n := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    let S : Finset (Fin n) := Finset.univ.filter fun (i : Fin n) => i.val ∈ T
    have hmap : S.map e = T := by
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact (Finset.mem_filter.mp hi).2
      · intro hj
        have hjn := Finset.mem_range.mp (hTr hj)
        exact Finset.mem_map.mpr ⟨⟨j, hjn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
    refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hmap⟩
    have h := (Finset.mem_filter.mp hT).2
    rw [← hmap] at h
    simpa only [rankSum, Finset.sum_map, he, Finset.mem_range, Nat.lt_succ_iff] using h

private theorem cumulativeCount_insert (s : Finset ℕ) (a t : ℕ) (ha : a ∉ s) :
    cumulativeCount (insert a s) t =
      cumulativeCount s t + (if a + 1 ≤ t then cumulativeCount s (t - (a + 1)) else 0) := by
  have hnot (S : Finset ℕ) (hS : S ∈ s.powerset) : a ∉ S :=
    fun h => ha (Finset.mem_powerset.mp hS h)
  unfold cumulativeCount
  rw [Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
  · congr 1
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    · by_cases ht : a + 1 ≤ t
      · rw [ite_eq_left ht]
        congr 1
        apply Finset.filter_congr
        intro S hS
        simp only [rankSum, Finset.sum_insert (hnot S hS)]
        omega
      · rw [ite_eq_right ht]
        have hfilter : (s.powerset.filter fun S => rankSum (insert a S) ≤ t) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro S hS
          obtain ⟨hS, hle⟩ := Finset.mem_filter.mp hS
          simp only [rankSum, Finset.sum_insert (hnot S hS)] at hle
          omega
        rw [hfilter, Finset.card_empty]
    · intro S hS T hT h
      change S ∈ s.powerset.filter _ at hS
      change T ∈ s.powerset.filter _ at hT
      simpa only [Finset.erase_insert (hnot S (Finset.mem_filter.mp hS).1),
        Finset.erase_insert (hnot T (Finset.mem_filter.mp hT).1)] using
        congrArg (fun U : Finset ℕ => U.erase a) h
  · rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, hT⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hS').1
    exact hnot S (Finset.mem_filter.mp hS).1 (hT ▸ Finset.mem_insert_self a T)

private theorem cumulativeCount_range_zero (t : ℕ) : cumulativeCount (Finset.range 0) t = 1 := by
  change ((∅ : Finset ℕ).powerset.filter fun S => rankSum S ≤ t).card = 1
  rw [Finset.powerset_empty, Finset.filter_eq_self.mpr]
  · exact Finset.card_singleton _
  · intro S hS
    rw [Finset.mem_singleton.mp hS]
    simp [rankSum]

private theorem cumulativeCount_range_succ (n t : ℕ) :
    cumulativeCount (Finset.range (n + 1)) t = cumulativeCount (Finset.range n) t +
      (if n + 1 ≤ t then cumulativeCount (Finset.range n) (t - (n + 1)) else 0) := by
  have h : Finset.range (n + 1) = insert n (Finset.range n) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  rw [h, cumulativeCount_insert _ _ _ (by simp)]

-- Each row stores the cumulative counts at thresholds 0 through `bound - 1`.
-- Adding weight `n + 1` adds the preceding row shifted right by that weight.
-- Weights outside the stored thresholds leave the row unchanged.
private def cumulativeRows (bound : ℕ) : ℕ → List ℕ
  | 0 => List.replicate bound 1
  | n + 1 =>
    let row := cumulativeRows bound n
    if bound ≤ n + 1 then row else
      List.zipWith (· + ·) row (List.replicate (n + 1) 0 ++ row)

private theorem cumulativeRows_getElem? (bound n t : ℕ) (ht : t < bound) :
    (cumulativeRows bound n)[t]? = some (cumulativeCount (Finset.range n) t) := by
  induction n generalizing t with
  | zero =>
    rw [cumulativeRows, cumulativeCount_range_zero]
    simp [ht]
  | succ n ih =>
    rw [cumulativeRows, cumulativeCount_range_succ]
    by_cases hb : bound ≤ n + 1
    · rw [ite_eq_left hb, ite_eq_right (show ¬ n + 1 ≤ t by omega), Nat.add_zero, ih t ht]
    · rw [ite_eq_right hb, List.getElem?_zipWith, ih t ht]
      by_cases h : n + 1 ≤ t
      · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using h)]
        rw [List.length_replicate, ih _ (by omega), ite_eq_left h]
      · have hlt : t < n + 1 := Nat.lt_of_not_ge h
        rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hlt)]
        simp [hlt, h]

/-- **Wilcoxon's worked cases.** For `15` pairs, `∑_{t ≤ 24} c_15(t) = 676`, so
`P(W⁺ ≤ 24) = 676 / 32768 ≈ 0.0206`, inside the source's range `[0.019, 0.054]`; for `8` pairs,
`∑_{t ≤ 3} c_8(t) = 5`, so `P(W⁺ ≤ 3) = 5 / 256`.

Sources: F. Wilcoxon, "Individual comparisons by ranking methods", Biometrics Bull. 1 (1945) 80–83,
Table II and the worked examples. -/
public theorem subsetSumCount_examples :
    ∑ t ∈ Finset.range 25, subsetSumCount 15 t = 676 ∧
      ∑ t ∈ Finset.range 4, subsetSumCount 8 t = 5 := by
  rw [sum_subsetSumCount_eq_cumulativeCount 15 24, sum_subsetSumCount_eq_cumulativeCount 8 3]
  constructor
  · apply Option.some.inj
    rw [← cumulativeRows_getElem? 25 15 24 (by decide)]
    rfl
  · apply Option.some.inj
    rw [← cumulativeRows_getElem? 4 8 3 (by decide)]
    rfl

end

end WantedExt.Probability.Statistics.WilcoxonSignedRankWanted
