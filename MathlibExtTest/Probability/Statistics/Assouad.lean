/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Assouad

@[expose] public section

/-!
# Tests for Assouad's lemma

* `exists_measurable_argmin` on two constant functions picks the smaller one.
* With the Hamming loss on the cube itself (`α = 1`, `β = 1`) and an uninformative model
  (`τ = 0`), the minimax expected Hamming error over randomised estimators of `b ∈ {0, 1}^d` is at
  least `d / 4`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open MathlibExt.Probability.TotalVariationDistance MathlibExt.Probability.Statistics.Assouad

namespace MathlibExtTest.Probability.Statistics.Assouad

/-- The measurable argmin of the constants `1` and `0` on `Bool` returns `false`. -/
example : ∃ g : Unit → Bool, (∀ i, MeasurableSet (g ⁻¹' {i})) ∧ ∀ ω, g ω = false := by
  obtain ⟨g, hg, hmin⟩ := exists_measurable_argmin
    (fun (b : Bool) (_ : Unit) => if b then (1 : ℝ≥0∞) else 0) fun _ => measurable_const
  refine ⟨g, hg, fun ω => ?_⟩
  have := hmin ω false
  cases h : g ω
  · rfl
  · simp [h] at this

/-- The Hamming loss on the cube, as an `ℝ≥0∞`-valued loss. -/
def hamming (d : ℕ) (b b' : Fin d → Bool) : ℝ≥0∞ := hammingDist b b'

lemma hamming_tri (d : ℕ) (b₀ b₁ t : Fin d → Bool) :
    hamming d b₀ b₁ ≤ 1 * (hamming d b₀ t + hamming d b₁ t) := by
  simp only [hamming, one_mul]
  have := hammingDist_triangle b₀ t b₁
  rw [hammingDist_comm t b₁] at this
  exact_mod_cast this

/-- An uninformative model on the cube: the minimax Hamming risk is at least `d / 4`. -/
example {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] (d : ℕ) :
    (d : ℝ≥0∞) ≤ 4 * minimaxRisk (hamming d) (Kernel.const (Fin d → Bool) ρ) := by
  have h := mul_one_sub_le_minimax (Kernel.const (Fin d → Bool) ρ) (hamming d)
    (fun _ => measurable_of_countable _) 1 ENNReal.one_ne_top (hamming_tri d) d id 1
    (fun b b' => by simp [hamming]) 0 (fun b b' _ => by simp [totalVariationDist_self])
  simpa using h

end MathlibExtTest.Probability.Statistics.Assouad
