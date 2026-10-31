/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.PermutationPValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.PermutationPValue

/-- Counting lemma with ties: all values equal, every rank count is `|G| = 2`, so no element
has count at most `1`. -/
example : (Finset.univ.filter fun _h : Multiplicative (ZMod 2) =>
    (Finset.univ.filter fun _g : Multiplicative (ZMod 2) => (0 : ℝ) ≤ 0).card ≤ 1).card = 0 := by
  simp

/-- The counting lemma bound itself, for an arbitrary family on a two-element group. -/
example (t : Multiplicative (ZMod 2) → ℝ) :
    (Finset.univ.filter fun h => (Finset.univ.filter fun g => t h ≤ t g).card ≤ 1).card ≤ 1 :=
  card_filter_rankCount_le _ t 1

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

/-- Non-vacuity: the sign-flip p-value of `T x = x` under the uniform law on `[-1/2, 1/2]`, a
probability measure with nontrivial group invariance. -/
example :
    IsValidPValue (volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) (permutationPValue ℤˣ id) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) :=
    ⟨by simp; norm_num⟩
  exact isValidPValue_permutationPValue _ (fun g => measurable_const_smul g) measurable_id

end MathlibExtTest.Probability.Statistics.MultipleTesting.PermutationPValue
