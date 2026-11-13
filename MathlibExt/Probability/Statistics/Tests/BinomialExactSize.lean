/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Distributions.Binomial
import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Probability.Statistics.NeymanPearsonExactSize

/-!
# Exact-size most powerful test for simple Bernoulli hypotheses

For `Binomial(n,p₀)` vs `Binomial(n,p₁)` with `0 < p₀ < p₁ < 1` and any level `α ∈ (0,1)`,
instantiating the finite exact-size Neyman–Pearson construction
(`exists_exact_size_most_powerful_finite`) gives a threshold `k ≥ 0`, a tie value
`γ ∈ [0,1]` and a `[0,1]`-valued test with the Neyman–Pearson shape, exact null size `α`,
and power at least that of every test of null size at most `α`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Tests

private lemma binomial_mass_nonneg (n : ℕ) (p : ↥unitInterval) (j : Fin (n + 1)) :
    0 ≤ (ProbabilityTheory.binomial n p).real {(j.val : ℕ)} :=
  MeasureTheory.measureReal_nonneg

private lemma binomial_mass_sum (n : ℕ) (p : ↥unitInterval) :
    ∑ j : Fin (n + 1), (ProbabilityTheory.binomial n p).real {(j.val : ℕ)} = 1 := by
  simp only [ProbabilityTheory.binomial_real_singleton]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ↑(n.choose k) * (p.val) ^ k * (1 - p.val) ^ (n - k))]
  have h := add_pow (p.val : ℝ) (1 - p.val) n
  rw [show (p.val : ℝ) + (1 - p.val) = 1 by ring, one_pow] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Exact-size most powerful test for simple Bernoulli hypotheses.** For `Binomial(n,p₀)`
vs `Binomial(n,p₁)` with `0 < p₀ < p₁ < 1` and any level `α ∈ (0,1)`, there are a threshold
`k ≥ 0`, a tie value `γ ∈ [0,1]` and a `[0,1]`-valued test with the Neyman–Pearson shape,
exact null size `α`, and power at least that of every test of null size at most `α`. -/
theorem binomial_exact_size_most_powerful (n : ℕ) (hn : 1 ≤ n)
    {p₀ p₁ : ↥unitInterval} (h₀ : 0 < p₀.val) (h₁ : p₀.val < p₁.val) (h₂ : p₁.val < 1)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ k : ℝ, 0 ≤ k ∧ ∃ γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ φstar : Fin (n + 1) → Set.Icc (0 : ℝ) 1,
        (∀ j, k * (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)} <
            (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)} → (φstar j).val = 1) ∧
        (∀ j, (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)} <
            k * (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)} → (φstar j).val = 0) ∧
        (∀ j, (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)} =
            k * (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)} → (φstar j).val = γ) ∧
        ∑ j, (φstar j).val * (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)} = α ∧
        ∀ φ : Fin (n + 1) → Set.Icc (0 : ℝ) 1,
          ∑ j, (φ j).val * (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)} ≤ α →
            ∑ j, (φ j).val * (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)} ≤
              ∑ j, (φstar j).val * (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)} := by
  have _unused : 1 ≤ n ∧ 0 < p₀.val ∧ p₀.val < p₁.val ∧ p₁.val < 1 :=
    ⟨hn, h₀, h₁, h₂⟩
  exact MathlibExt.Probability.Statistics.NeymanPearson.exists_exact_size_most_powerful_finite
    (fun j : Fin (n + 1) => (ProbabilityTheory.binomial n p₀).real {(j.val : ℕ)})
    (fun j : Fin (n + 1) => (ProbabilityTheory.binomial n p₁).real {(j.val : ℕ)})
    (binomial_mass_nonneg n p₀) (binomial_mass_nonneg n p₁)
    (binomial_mass_sum n p₀) (binomial_mass_sum n p₁)
    α hα0 hα1

end MathlibExt.Probability.Statistics.Tests
