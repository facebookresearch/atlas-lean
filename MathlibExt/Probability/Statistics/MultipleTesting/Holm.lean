/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni

/-!
# Holm's step-down procedure controls the family-wise error rate

Let `p₍₁₎ ≤ ⋯ ≤ p₍ₘ₎` be the sorted p-values. Holm's step-down procedure at level `α` compares
`p₍ₖ₎` with `α / (m - k + 1)` for `k = 1, 2, …` and rejects the hypotheses with the smallest
p-values as long as the comparisons succeed: it rejects `H₍₁₎, …, H₍ᵣ₎`, where `r` is the
largest index such that `p₍ₖ₎ ≤ α / (m - k + 1)` for every `k ≤ r`.

Since `p₍ₖ₎ ≤ t ↔ k ≤ numBelow p t`, the step-down count is stated without sorting
(`holmIndex`), and the rejection set is `{i | p i ≤ α / (m - r + 1)}` (`holmRejections`),
which consists of exactly `r` hypotheses carrying the `r` smallest p-values
(`card_holmRejections`, `mem_holmRejections_of_le`).

Holm proved that the procedure controls the family-wise error rate at `α` whenever the
true-null p-values are valid, with no assumption on their dependence: the first true null to
be rejected sits at a sorted position `k ≤ m - |H0| + 1`, so its p-value is at most `α / |H0|`,
and the union bound applies.

## Main results

* `card_holmRejections`: Holm rejects exactly `holmIndex α p` hypotheses.
* `measure_holm_familywiseError_le`: `μ (Holm rejects a true null) ≤ α`.

## References

* S. Holm, *A simple sequentially rejective multiple test procedure*, Scand. J. Statist. 6
  (1979), 65–70.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- Holm's step-down count at level `α`: the largest `r ∈ {0, …, m}` such that for every
`k ∈ {1, …, r}` the `k`-th smallest p-value is at most `α / (m - k + 1)`, i.e. at least `k`
p-values are at most `α / (m - k + 1)`. (`r = 0` always qualifies.) -/
noncomputable def holmIndex (α : ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun r : ℕ =>
    ∀ k ∈ Finset.Icc (1 : ℕ) r, k ≤ numBelow p (α / ((m : ℝ) - k + 1))).max' ⟨0, by simp; omega⟩

/-- The hypotheses rejected by Holm's step-down procedure at level `α`: those whose p-value is
at most `α / (m - r + 1)` with `r = holmIndex α p`; these are the hypotheses with the `r`
smallest p-values. -/
noncomputable def holmRejections (α : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ α / ((m : ℝ) - holmIndex α p + 1)

/-- Holm's step-down count is at most `m`. -/
theorem holmIndex_le (α : ℝ) (p : Fin m → ℝ) : holmIndex α p ≤ m := by
  have h := Finset.max'_mem ((Finset.range (m + 1)).filter fun r : ℕ =>
    ∀ k ∈ Finset.Icc (1 : ℕ) r, k ≤ numBelow p (α / ((m : ℝ) - k + 1))) ⟨0, by simp; omega⟩
  simp only [Finset.mem_filter, Finset.mem_range] at h
  exact Nat.lt_succ_iff.1 h.1

/-- Every step up to Holm's count succeeds: for `1 ≤ k ≤ holmIndex α p`, at least `k`
p-values are at most `α / (m - k + 1)`. -/
theorem le_numBelow_of_le_holmIndex {α : ℝ} {p : Fin m → ℝ} {k : ℕ} (hk₁ : 1 ≤ k)
    (hk : k ≤ holmIndex α p) : k ≤ numBelow p (α / ((m : ℝ) - k + 1)) := by
  have h := Finset.max'_mem ((Finset.range (m + 1)).filter fun r : ℕ =>
    ∀ k ∈ Finset.Icc (1 : ℕ) r, k ≤ numBelow p (α / ((m : ℝ) - k + 1))) ⟨0, by simp; omega⟩
  simp only [Finset.mem_filter] at h
  exact h.2 k (Finset.mem_Icc.2 ⟨hk₁, hk⟩)

/-- Holm's count is the largest index up to which every step succeeds. -/
theorem le_holmIndex {α : ℝ} {p : Fin m → ℝ} {r : ℕ} (hr : r ≤ m)
    (h : ∀ k ∈ Finset.Icc (1 : ℕ) r, k ≤ numBelow p (α / ((m : ℝ) - k + 1))) :
    r ≤ holmIndex α p :=
  Finset.le_max' _ r (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hr), h⟩)

/-- The rejection set is closed under smaller p-values. -/
theorem mem_holmRejections_of_le {α : ℝ} {p : Fin m → ℝ} {i j : Fin m} (hij : p i ≤ p j)
    (hj : j ∈ holmRejections α p) : i ∈ holmRejections α p := by
  simp only [holmRejections, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hij.trans hj

/-- Every step up to Holm's count succeeds (membership form). -/
private theorem holmIndex_spec (α : ℝ) (p : Fin m → ℝ) :
    ∀ k ∈ Finset.Icc (1 : ℕ) (holmIndex α p),
      k ≤ numBelow p (α / ((m : ℝ) - k + 1)) := fun _ hk =>
  le_numBelow_of_le_holmIndex (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2

/-- Holm's procedure at level `α ≥ 0` rejects exactly `holmIndex α p` hypotheses. -/
theorem card_holmRejections {α : ℝ} (hα : 0 ≤ α) (p : Fin m → ℝ) :
    (holmRejections α p).card = holmIndex α p := by
  classical
  change numBelow p (α / ((m : ℝ) - holmIndex α p + 1)) = holmIndex α p
  let r := holmIndex α p
  change numBelow p (α / ((m : ℝ) - r + 1)) = r
  have hr : r ≤ m := holmIndex_le α p
  have hspec := holmIndex_spec α p
  apply Nat.le_antisymm
  · by_contra h
    have hcount : r + 1 ≤ numBelow p (α / ((m : ℝ) - r + 1)) := by omega
    have hcard : numBelow p (α / ((m : ℝ) - r + 1)) ≤ m := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
    have hrm : r + 1 ≤ m := hcount.trans hcard
    have hden : 0 < (m : ℝ) - (r + 1 : ℕ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hrm
      linarith
    have hthreshold : α / ((m : ℝ) - r + 1) ≤
        α / ((m : ℝ) - (r + 1 : ℕ) + 1) := by
      apply div_le_div_of_nonneg_left hα hden
      push_cast
      linarith
    have hnext : r + 1 ≤ r := le_holmIndex hrm (by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      by_cases hkr : k ≤ r
      · exact hspec k (Finset.mem_Icc.mpr ⟨hk'.1, hkr⟩)
      · have heq : k = r + 1 := by omega
        subst k
        exact hcount.trans (numBelow_mono p hthreshold))
    omega
  · by_cases hz : r = 0
    · omega
    · exact hspec r (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)

/-- If Holm rejects a true null, then some true null has p-value at most `α / |H0|`: the first
true null in sorted order sits at a position `k ≤ m - |H0| + 1`. -/
private theorem exists_null_le_of_rejection {α : ℝ} (hα : 0 ≤ α)
    (p : Fin m → ℝ) (H0 : Finset (Fin m))
    (h : (holmRejections α p ∩ H0).Nonempty) :
    ∃ j ∈ H0, p j ≤ α / H0.card := by
  classical
  obtain ⟨i, hi⟩ := h
  obtain ⟨hiR, hiH⟩ := Finset.mem_inter.mp hi
  obtain ⟨j, hjH, hmin⟩ := Finset.exists_min_image H0 p ⟨i, hiH⟩
  have hjR : j ∈ holmRejections α p :=
    mem_holmRejections_of_le (hmin i hiH) hiR
  let S := Finset.univ.filter fun l => p l < p j
  let k := S.card + 1
  have hjS : j ∉ S := by simp [S]
  have hdisj : Disjoint S H0 := by
    apply Finset.disjoint_left.mpr
    intro l hl hlH
    exact (not_lt_of_ge (hmin l hlH)) (Finset.mem_filter.mp hl).2
  have hsum : S.card + H0.card ≤ m := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin m)
  have hsubset : insert j S ⊆ holmRejections α p := by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hjR
    · exact mem_holmRejections_of_le (Finset.mem_filter.mp hl).2.le hjR
  have hkr : k ≤ holmIndex α p := by
    have hc := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hjS, card_holmRejections hα p] at hc
    exact hc
  have hkpos : 1 ≤ k := by omega
  have hkcount := holmIndex_spec α p k (Finset.mem_Icc.mpr ⟨hkpos, hkr⟩)
  have hjthreshold : p j ≤ α / ((m : ℝ) - k + 1) := by
    by_contra hn
    have hn' : α / ((m : ℝ) - k + 1) < p j := lt_of_not_ge hn
    have hc : numBelow p (α / ((m : ℝ) - k + 1)) ≤ S.card := by
      apply Finset.card_le_card
      intro l hl
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.trans_lt hn'⟩
    dsimp [k] at hkcount hc
    omega
  have hm0 : 0 < (H0.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨j, hjH⟩
  have hden : (H0.card : ℝ) ≤ (m : ℝ) - k + 1 := by
    have hs : (S.card : ℝ) + H0.card ≤ m := by exact_mod_cast hsum
    dsimp [k]
    push_cast
    linarith
  exact ⟨j, hjH,
    hjthreshold.trans (div_le_div_of_nonneg_left hα hm0 hden)⟩

/-- **Holm's procedure controls the FWER.** If every true-null p-value is valid, the
probability that Holm's step-down procedure at level `α ∈ [0, 1]` rejects at least one true
null is at most `α`. No independence is assumed.

Source: Holm (1979). -/
theorem measure_holm_familywiseError_le (μ : Measure Ω) (p : Fin m → Ω → ℝ)
    (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) :
    μ {ω | (holmRejections α (fun i => p i ω) ∩ H0).Nonempty} ≤ ENNReal.ofReal α := by
  classical
  by_cases hH0 : H0 = ∅
  · simp [hH0]
  · have hm0nat : 0 < H0.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hH0)
    have hm0 : 0 < (H0.card : ℝ) := by exact_mod_cast hm0nat
    have hm0one : (1 : ℝ) ≤ H0.card := by exact_mod_cast hm0nat
    have hc : α / H0.card ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hα₀ hm0.le, ?_⟩
      have hle : α / H0.card ≤ α := by
        simpa using div_le_div_of_nonneg_left hα₀ zero_lt_one hm0one
      exact hle.trans hα₁
    calc
      μ {ω | (holmRejections α (fun i => p i ω) ∩ H0).Nonempty}
          ≤ μ {ω | ∃ i ∈ H0, p i ω ≤ α / H0.card} := by
            apply measure_mono
            intro ω hω
            exact exists_null_le_of_rejection hα₀ (fun i => p i ω) H0 hω
      _ ≤ ENNReal.ofReal (H0.card * (α / H0.card)) :=
        measure_exists_mem_le_le μ p H0 hnull hc
      _ = ENNReal.ofReal α := by rw [mul_div_cancel₀ α (ne_of_gt hm0)]


end MathlibExt.Probability.Statistics.MultipleTesting
