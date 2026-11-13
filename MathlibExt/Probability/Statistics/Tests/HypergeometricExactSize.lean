/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Hypergeometric
public import MathlibExt.Probability.Statistics.NeymanPearsonExactSize

/-!
# Exact-size most powerful test for generic hypergeometric laws

For two fully specified hypergeometric laws `H₀ = hypergeometricReal N K₀ m` and
`H₁ = hypergeometricReal N K₁ m` on `{0, …, m}` and any level `α ∈ (0,1)`, instantiating the
finite exact-size Neyman–Pearson construction (`exists_exact_size_most_powerful_finite`) gives
a threshold `k ≥ 0`, a tie value `γ ∈ [0,1]` and a `[0,1]`-valued test with the
Neyman–Pearson shape, exact null size `α`, and power at least that of every test of null size
at most `α`.

This is a generic simple-vs-simple hypergeometric consumer. The null masses coincide in shape
with the Fisher conditional law of a 2×2 table given its margins
(`cond_measureReal_eq_hypergeometricReal`), but varying the margin parameter (`K₀ ≠ K₁`)
changes a fixed margin, so the two laws are not claimed to be two hypotheses inside one Fisher
conditional model, and no derivation from the conditional theorem is claimed. The
unconditional randomized-trial (product-binomial) model is a different probability law and is
not covered.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Tests

/-- Normalization of the hypergeometric masses over `Fin (m+1)`, rewritten from
`sum_hypergeometricReal` (a `Finset.range` sum) via `Fin.sum_univ_eq_sum_range`. -/
private lemma sum_hypergeometricReal_fin (N K m : ℕ) (hK : K ≤ N) (hm : m ≤ N) :
    ∑ j : Fin (m + 1), ProbabilityTheory.hypergeometricReal N K m (j.val : ℕ) = 1 := by
  have h := ProbabilityTheory.sum_hypergeometricReal (N := N) (K := K) (n := m) hK hm
  rw [Fin.sum_univ_eq_sum_range]
  exact h

/-- **Exact-size most powerful test for generic hypergeometric laws.** For two fully
specified hypergeometric laws `H₀ = hypergeometricReal N K₀ m` and
`H₁ = hypergeometricReal N K₁ m` on `{0, …, m}` and any level `α ∈ (0,1)`, there are a
threshold `k ≥ 0`, a tie value `γ ∈ [0,1]` and a `[0,1]`-valued test with the
Neyman–Pearson shape, exact null size `α`, and power at least that of every test of null
size at most `α`. Generic consumer: the two laws are not claimed to live inside one Fisher
conditional model. -/
theorem hypergeometric_exact_size_most_powerful (N K₀ K₁ m : ℕ)
    (hK₀ : K₀ ≤ N) (hK₁ : K₁ ≤ N) (hm : m ≤ N) (hmpos : 0 < m) (hmlt : m < N)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ k : ℝ, 0 ≤ k ∧ ∃ γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ φstar : Fin (m + 1) → Set.Icc (0 : ℝ) 1,
        (∀ j, k * ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) <
            ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) → (φstar j).val = 1) ∧
        (∀ j, ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) <
            k * ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) → (φstar j).val = 0) ∧
        (∀ j, ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) =
            k * ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) → (φstar j).val = γ) ∧
        ∑ j, (φstar j).val * ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) = α ∧
        ∀ φ : Fin (m + 1) → Set.Icc (0 : ℝ) 1,
          ∑ j, (φ j).val * ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) ≤ α →
            ∑ j, (φ j).val * ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) ≤
              ∑ j, (φstar j).val * ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) := by
  have _ := hmpos
  have _ := hmlt
  have hp_nonneg : ∀ j : Fin (m + 1),
      0 ≤ ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) :=
    fun j => ProbabilityTheory.hypergeometricReal_nonneg _ _ _ _
  have hq_nonneg : ∀ j : Fin (m + 1),
      0 ≤ ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) :=
    fun j => ProbabilityTheory.hypergeometricReal_nonneg _ _ _ _
  have hp_sum : ∑ j : Fin (m + 1),
      ProbabilityTheory.hypergeometricReal N K₀ m (j.val : ℕ) = 1 :=
    sum_hypergeometricReal_fin N K₀ m hK₀ hm
  have hq_sum : ∑ j : Fin (m + 1),
      ProbabilityTheory.hypergeometricReal N K₁ m (j.val : ℕ) = 1 :=
    sum_hypergeometricReal_fin N K₁ m hK₁ hm
  exact MathlibExt.Probability.Statistics.NeymanPearson.exists_exact_size_most_powerful_finite
    _ _ hp_nonneg hq_nonneg hp_sum hq_sum α hα0 hα1

end MathlibExt.Probability.Statistics.Tests
