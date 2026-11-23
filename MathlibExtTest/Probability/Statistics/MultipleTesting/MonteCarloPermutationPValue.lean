/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.MonteCarloPermutationPValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.MonteCarloPermutationPValue

/-- With no draws (`B = 0`) the Monte Carlo p-value is identically `1`. -/
example (T : ℝ → ℝ) (ω : ℝ) (g : Fin 0 → ℤˣ) : monteCarloPermutationPValue T ω g = 1 := by
  simp [monteCarloPermutationPValue]

/-- The Monte Carlo p-value is never zero: it is at least `1 / (B + 1)`. Here all draws are the
sign flip `-1`, `T = id` and `ω = 1`, so no draw reaches `T ω` and `p = 1/3`. -/
example : monteCarloPermutationPValue (B := 2) id (1 : ℝ) (fun _ => (-1 : ℤˣ)) = 1 / 3 := by
  simp [monteCarloPermutationPValue, Units.smul_def]
  norm_num

/-- Draws equal to the identity always tie with the observed statistic, giving `p = 1`. -/
example (T : ℝ → ℝ) (ω : ℝ) :
    monteCarloPermutationPValue (B := 2) T ω (fun _ => (1 : ℤˣ)) = 1 := by
  simp [monteCarloPermutationPValue]
  norm_num

/-- The sign-flip group `ℤˣ` acting on `ℝ` leaves the uniform law on `[-1/2, 1/2]` invariant. -/
instance : SMulInvariantMeasure ℤˣ ℝ (volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) := by
  refine ⟨fun c s hs => ?_⟩
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · have h : (fun x : ℝ => ((-1 : ℤˣ) • x)) ⁻¹' s = -s := by ext x; simp [Units.smul_def]
    rw [h, Measure.restrict_apply hs.neg, Measure.restrict_apply hs]
    rw [← Measure.measure_neg (μ := volume)]
    congr 1
    ext x; simp [and_comm, neg_le]

/-- The discrete σ-algebra on the sign-flip group. -/
instance : MeasurableSpace ℤˣ := ⊤

instance : DiscreteMeasurableSpace ℤˣ := ⟨fun _ => trivial⟩

/-- Non-vacuity: `B = 5` random sign flips of `T x = x` under the uniform law on
`[-1/2, 1/2]`, a probability measure with nontrivial group invariance. -/
example : IsValidPValue
    ((volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))).prod
      (Measure.pi fun _ : Fin 5 => ProbabilityTheory.uniformOn (Set.univ : Set ℤˣ)))
    (fun x => monteCarloPermutationPValue id x.1 x.2) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) :=
    ⟨by simp; norm_num⟩
  exact isValidPValue_monteCarloPermutationPValue 5 _ (fun g => measurable_const_smul g)
    measurable_id

end MathlibExtTest.Probability.Statistics.MultipleTesting.MonteCarloPermutationPValue
