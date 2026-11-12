/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

/-!
# Upper-tail p-values of discrete tests are valid

Let `X` be a count with null law `ν` on `ℕ`, and reject for large values of `X`. The exact
upper-tail p-value of the observation `X = k` is the null probability `ν {j | k ≤ j}` of a count
at least as extreme. This file shows that it is a valid (super-uniform) p-value:
`P(p(X) ≤ s) ≤ s` for every `s ∈ [0, 1]`. Equality fails in general because `ν` has atoms, which
is why discrete exact tests are conservative.

## Main definitions

* `upperTail ν k = ν {j | k ≤ j}`, as a real number.
* `upperTailPValue ν X ω = upperTail ν (X ω)`.

## Main results

* `upperTail_antitone`: the upper tail is antitone in the cutoff.
* `isValidPValue_upperTailPValue`: if `X` has law `ν`, the upper-tail p-value is valid.
* `isValidPValue_survival`: for any law `ν` on `ℝ`, `y ↦ ν [y, ∞)` evaluated at a
  variable with law `ν` is a valid p-value.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  Lemma 3.3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Probability.Statistics.ExactTests

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The upper tail `ν {j | k ≤ j}` of a measure `ν` on `ℕ` at the cutoff `k`, as a real
number. -/
noncomputable def upperTail (ν : Measure ℕ) (k : ℕ) : ℝ :=
  ν.real {j | k ≤ j}

/-- The exact upper-tail p-value of a count `X` with null law `ν`: the null probability of a
count at least as large as the observed `X ω`. -/
noncomputable def upperTailPValue (ν : Measure ℕ) (X : Ω → ℕ) (ω : Ω) : ℝ :=
  upperTail ν (X ω)

/-- The upper tail of a finite measure on `ℕ` is antitone in the cutoff. -/
theorem upperTail_antitone (ν : Measure ℕ) [IsFiniteMeasure ν] : Antitone (upperTail ν) :=
  fun _ _ h => measureReal_mono fun _ hj => le_trans h hj

/-- **Validity of the upper-tail p-value.** If the count `X` has law `ν` under `μ`, then
`μ {upperTail ν X ≤ s} ≤ s` for every `s ∈ [0, 1]`.

The event `{upperTail ν X ≤ s}` is `{k₀ ≤ X}` for the least cutoff `k₀` whose tail is at most
`s` (or empty if there is none), and `μ {k₀ ≤ X} = ν {j | k₀ ≤ j} ≤ s`.

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem isValidPValue_upperTailPValue {μ : Measure Ω} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {X : Ω → ℕ} (hX : HasLaw X ν μ) : IsValidPValue μ (upperTailPValue ν X) := by
  intro s _
  by_cases hS : ∃ k, upperTail ν k ≤ s
  · classical
    have hset : {ω | upperTailPValue ν X ω ≤ s} = {ω | Nat.find hS ≤ X ω} := by
      ext ω
      simp only [upperTailPValue, Set.mem_ofPred_eq]
      exact ⟨fun h => Nat.find_min' hS h,
        fun h => (upperTail_antitone ν h).trans (Nat.find_spec hS)⟩
    rw [hset, hX.measure_eq (p := (Nat.find hS ≤ ·)) (measurableSet_Ici (a := Nat.find hS)),
      ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (Nat.find_spec hS)
  · have hset : {ω | upperTailPValue ν X ω ≤ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => hS ⟨X ω, h⟩
    simp [hset]

/-- **Survival-function p-values are valid.** If `Y` has law `ν` on `ℝ`, then
`ω ↦ ν [Y ω, ∞)` is a valid p-value, whatever `ν` (atoms allowed).

The event `{ν [Y, ∞) ≤ t}` is `{Y ∈ A}` for an upper set `A`; `A` is covered by an increasing
sequence of half-lines `[c n, ∞)` with each `c n ∈ A`, so `ν A ≤ t` by continuity from below.

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem isValidPValue_survival {μ : Measure Ω} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} (hY : HasLaw Y ν μ) : IsValidPValue μ (fun ω => ν.real (Set.Ici (Y ω))) := by
  intro t _
  set S : ℝ → ℝ := fun y => ν.real (Set.Ici y)
  have hS : Antitone S := fun _ _ hxy => measureReal_mono (Set.Ici_subset_Ici.mpr hxy)
  set A := {y | S y ≤ t}
  have hup : ∀ {y z}, y ∈ A → y ≤ z → z ∈ A := fun hy hyz => (hS hyz).trans hy
  have hA : MeasurableSet A := measurableSet_le hS.measurable measurable_const
  rw [hY.measure_eq (p := fun y => S y ≤ t) hA]
  -- `A` covered by `⋃ n, [c n, ∞)` with `c` antitone and `c n ∈ A` gives `ν A ≤ t`.
  have key : ∀ c : ℕ → ℝ, Antitone c → (∀ n, c n ∈ A) → A ⊆ ⋃ n, Set.Ici (c n) →
      ν A ≤ ENNReal.ofReal t := by
    intro c hc hcA hcov
    have hmono : Monotone fun n => Set.Ici (c n) := fun _ _ hmn =>
      Set.Ici_subset_Ici.mpr (hc hmn)
    refine (measure_mono hcov).trans
      (le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun n => ?_)
    change ν (Set.Ici (c n)) ≤ _
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hcA n)
  rcases Set.eq_empty_or_nonempty A with hE | ⟨y₀, hy₀⟩
  · change ν A ≤ _
    rw [hE]
    simp
  by_cases hb : BddBelow A
  · by_cases hm : sInf A ∈ A
    · exact key (fun _ => sInf A) antitone_const (fun _ => hm) fun y hy =>
        Set.mem_iUnion.mpr ⟨0, csInf_le hb hy⟩
    · refine key (fun n => sInf A + 1 / ((n : ℝ) + 1)) (fun m n hmn => ?_) (fun n => ?_)
        fun y hy => ?_
      · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        simp only [add_le_add_iff_left]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      · obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt ⟨y₀, hy₀⟩
          (lt_add_of_pos_right (sInf A) (Nat.one_div_pos_of_nat (n := n)))
        exact hup hz hzlt.le
      · have hlt : sInf A < y := lt_of_le_of_ne (csInf_le hb hy) fun h => hm (h ▸ hy)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Ici]; linarith⟩
  · rw [not_bddBelow_iff] at hb
    refine key (fun n => -(n : ℝ)) (fun m n hmn => ?_) (fun n => ?_) fun y _ => ?_
    · simp only [neg_le_neg_iff, Nat.cast_le]
      exact hmn
    · obtain ⟨z, hz, hzlt⟩ := hb (-(n : ℝ))
      exact hup hz hzlt.le
    · obtain ⟨n, hn⟩ := exists_nat_ge (-y)
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Ici]; linarith⟩

open Finset in
/-- **Validity of a discrete upper-tail p-value.** For nonnegative masses `q` on a finite set
`s` and a statistic `T`, the upper-tail p-value `p x = ∑_{y ∈ s, T x ≤ T y} q y` satisfies
`∑_{x ∈ s, p x ≤ t} q x ≤ t` for every `t ≥ 0`. -/
theorem sum_upperTail_le {ι : Type*} (s : Finset ι) (q T : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ x ∈ s with ∑ y ∈ s with T x ≤ T y, q y ≤ t, q x ≤ t := by
  classical
  set A := s.filter fun x => ∑ y ∈ s with T x ≤ T y, q y ≤ t with hA
  rcases A.eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
    exact ht
  obtain ⟨x₀, hx₀, hmin⟩ := A.exists_min_image T h
  calc ∑ x ∈ A, q x ≤ ∑ y ∈ s with T x₀ ≤ T y, q y := by
        refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun y hy _ => ?_
        · exact mem_filter.mpr ⟨(mem_filter.mp hx).1, hmin x hx⟩
        · exact hq y (mem_filter.mp hy).1
    _ ≤ t := (mem_filter.mp hx₀).2

end MathlibExt.Probability.Statistics.ExactTests
