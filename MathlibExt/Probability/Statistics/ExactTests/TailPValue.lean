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
* `measure_upperTailPValue_le_upperTail`: it is exactly calibrated at every attainable level
  `upperTail ν k`.

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

end MathlibExt.Probability.Statistics.ExactTests
