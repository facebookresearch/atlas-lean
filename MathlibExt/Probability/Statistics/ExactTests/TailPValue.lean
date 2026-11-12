/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Upper- and lower-tail p-values of discrete tests are valid

Let `X` be a count with null law `ν` on `ℕ`. Rejecting for large values of `X` uses the exact
upper-tail p-value of the observation `X = k`, the null probability `ν {j | k ≤ j}` of a count
at least as extreme; rejecting for small values uses the lower-tail p-value, the null
probability `ν {j | j ≤ k}`. This file shows that both are valid (super-uniform) p-values:
`P(p(X) ≤ s) ≤ s` for every `s ∈ [0, 1]`. Equality fails in general because `ν` has atoms, which
is why discrete exact tests are conservative.

## Main definitions

* `upperTail ν k = ν {j | k ≤ j}`, as a real number.
* `upperTailPValue ν X ω = upperTail ν (X ω)`.
* `lowerTail ν k = ν {j | j ≤ k}`, as a real number.
* `lowerTailPValue ν X ω = lowerTail ν (X ω)`.

## Main results

* `upperTail_antitone`: the upper tail is antitone in the cutoff.
* `isValidPValue_upperTailPValue`: if `X` has law `ν`, the upper-tail p-value is valid.
* `measure_upperTailPValue_le_upperTail`: it is exactly calibrated at every attainable level
  `upperTail ν k`.
* `lowerTail_mono`: the lower tail is monotone in the cutoff.
* `isValidPValue_lowerTailPValue`: if `X` has law `ν`, the lower-tail p-value is valid.

The two-sided and composite-null binomial mirrors live in `ExactTests.BinomialTest`.

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

/-- **Exact calibration at attainable levels.** If the count `X` has law `ν` under `μ`, the
upper-tail p-value is exactly calibrated at every attainable level `s = upperTail ν k`:
`μ {upperTailPValue ν X ≤ s} = s`. Between attainable levels it is conservative
(`isValidPValue_upperTailPValue`).

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem measure_upperTailPValue_le_upperTail {μ : Measure Ω} {ν : Measure ℕ}
    [IsProbabilityMeasure ν] {X : Ω → ℕ} (hX : HasLaw X ν μ) (k : ℕ) :
    μ {ω | upperTailPValue ν X ω ≤ upperTail ν k} = ENNReal.ofReal (upperTail ν k) := by
  refine le_antisymm
    (isValidPValue_upperTailPValue hX _ ⟨measureReal_nonneg, measureReal_le_one⟩) ?_
  calc ENNReal.ofReal (upperTail ν k) = μ {ω | k ≤ X ω} := by
        rw [hX.measure_eq (p := (k ≤ ·)) (measurableSet_Ici (a := k)), ← ofReal_measureReal]
        rfl
    _ ≤ _ := measure_mono fun ω h => upperTail_antitone ν h

/-- The lower tail `ν {j | j ≤ k}` of a measure `ν` on `ℕ` at the cutoff `k`, as a real
number. -/
noncomputable def lowerTail (ν : Measure ℕ) (k : ℕ) : ℝ :=
  ν.real {j | j ≤ k}

/-- The exact lower-tail p-value of a count `X` with null law `ν`: the null probability of a
count at most as large as the observed `X ω`. -/
noncomputable def lowerTailPValue {Ω : Type*} (ν : Measure ℕ) (X : Ω → ℕ) (ω : Ω) : ℝ :=
  lowerTail ν (X ω)

/-- The lower tail of a finite measure on `ℕ` is monotone in the cutoff. -/
theorem lowerTail_mono (ν : Measure ℕ) [IsFiniteMeasure ν] :
    Monotone (lowerTail ν) := by
  intro a b h
  unfold lowerTail
  exact measureReal_mono fun _ hj => le_trans hj h

/-- **Validity of the lower-tail p-value.** If the count `X` has law `ν` under `μ`, then
`μ {lowerTail ν X ≤ s} ≤ s` for every `s ∈ [0, 1]`. -/
theorem isValidPValue_lowerTailPValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {X : Ω → ℕ} (hX : HasLaw X ν μ) :
    IsValidPValue μ (lowerTailPValue ν X) := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
  by_cases hs_lt : s < 1
  · by_cases hS : ∃ k, lowerTail ν k ≤ s
    · classical
      have hmon_seq : Monotone (fun N : ℕ => ({j : ℕ | j ≤ N} : Set ℕ)) :=
        fun _ _ h _ hj => le_trans hj h
      have hunion : (⋃ N : ℕ, ({j : ℕ | j ≤ N} : Set ℕ)) = Set.univ := by
        ext j
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact ⟨j, le_rfl⟩
      have htend :=
        tendsto_measure_iUnion_atTop (μ := ν)
          (s := fun N : ℕ => ({j : ℕ | j ≤ N} : Set ℕ)) hmon_seq
      rw [hunion, measure_univ] at htend
      have hlt1 : ENNReal.ofReal s < 1 := by
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
        exact hs_lt
      have hev := Filter.Tendsto.eventually_const_lt hlt1 htend
      obtain ⟨N, hN⟩ := hev.exists
      have hfin : ν {j : ℕ | j ≤ N} ≠ ⊤ := (measure_lt_top _ _).ne
      have hNs : s < ν.real {j : ℕ | j ≤ N} := by
        have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).mpr hN
        rw [ENNReal.toReal_ofReal hs0] at h
        exact h
      have htailN : s < lowerTail ν N := by
        unfold lowerTail
        exact hNs
      have hbound : ∀ k : ℕ, lowerTail ν k ≤ s → k ≤ N := by
        intro k hk
        by_contra hcon
        have hlt' : N < k := lt_of_not_ge hcon
        have hle : N ≤ k := le_of_lt hlt'
        have hmono : lowerTail ν N ≤ lowerTail ν k := lowerTail_mono ν hle
        have hlt : s < lowerTail ν k := lt_of_lt_of_le htailN hmono
        have hss : s < s := lt_of_lt_of_le hlt hk
        exact lt_irrefl _ hss
      obtain ⟨k, hk⟩ := hS
      have hk_le : k ≤ N := hbound k hk
      have hk₀_spec : lowerTail ν (Nat.findGreatest (fun k => lowerTail ν k ≤ s) N) ≤ s :=
        Nat.findGreatest_spec (P := fun k => lowerTail ν k ≤ s) hk_le hk
      have hset : {ω | lowerTailPValue ν X ω ≤ s} =
          {ω | X ω ≤ Nat.findGreatest (fun k => lowerTail ν k ≤ s) N} := by
        ext ω
        simp only [lowerTailPValue, Set.mem_ofPred_eq]
        constructor
        · intro h
          have hleN : X ω ≤ N := hbound _ h
          exact Nat.le_findGreatest (P := fun k => lowerTail ν k ≤ s) hleN h
        · intro h
          exact le_trans (lowerTail_mono ν h) hk₀_spec
      rw [hset,
        hX.measure_eq (p := (· ≤ Nat.findGreatest (fun k => lowerTail ν k ≤ s) N))
          (measurableSet_Iic (a := Nat.findGreatest (fun k => lowerTail ν k ≤ s) N)),
        ← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal hk₀_spec
    · have hset : {ω | lowerTailPValue ν X ω ≤ s} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω h => hS ⟨X ω, h⟩
      simp [hset]
  · have hs_eq : s = 1 := le_antisymm hs1 (le_of_not_gt hs_lt)
    subst hs_eq
    have hmeas : MeasurableSet {x : ℕ | lowerTail ν x ≤ 1} :=
      MeasurableSet.of_discrete
    have heq : μ {ω | lowerTailPValue ν X ω ≤ 1} = ν {x | lowerTail ν x ≤ 1} :=
      hX.measure_eq hmeas
    rw [heq]
    calc ν {x | lowerTail ν x ≤ 1} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm

end MathlibExt.Probability.Statistics.ExactTests
