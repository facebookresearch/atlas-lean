/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Blocking
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Tests for blocked randomization

Two-block unbiasedness, single-block reduction, singleton-block impossibility,
and the empty-block zero weight.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Statistics.Experiment

open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

/-- Positive: a two-block fixture on `Fin 6` (blocks of size 4 and 2).
The worker discharges the partition hypotheses and applies
`integral_blockContrast`. -/
example (y₀ y₁ : Fin 6 → ℝ) :
    ∫ S, blockContrast y₀ y₁ ![{0, 1, 2, 3}, {4, 5}] S
      ∂(blockRandomization 2 ![{0, 1, 2, 3}, {4, 5}] ![2, 1]) =
      ate y₀ y₁ := by
  refine integral_blockContrast y₀ y₁ _ _ ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show Disjoint ({0, 1, 2, 3} : Finset (Fin 6)) {4, 5}
      rw [Finset.disjoint_left]
      decide
    · show Disjoint ({4, 5} : Finset (Fin 6)) {0, 1, 2, 3}
      rw [Finset.disjoint_left]
      decide
    · exact absurd rfl hij
  · decide
  · decide
  · decide

/-- Bridge non-vacuity: with `B = 1` and the single block equal to `univ`,
`blockContrast` is the ordinary difference in means of the embedded set. -/
example (y₀ y₁ : Fin 4 → ℝ) (S₀ : Finset ↥(Finset.univ : Finset (Fin 4))) :
    blockContrast y₀ y₁ (fun _ : Fin 1 => Finset.univ) (fun _ => S₀) =
      diffInMeans y₀ y₁ (Finset.image Subtype.val S₀) := by
  have hinj : Function.Injective
      (Subtype.val : ↥(Finset.univ : Finset (Fin 4)) → Fin 4) :=
    Subtype.val_injective
  have hcard : ∀ T : Finset ↥(Finset.univ : Finset (Fin 4)),
      (Finset.image Subtype.val T).card = T.card := fun T =>
    Finset.card_image_of_injective T hinj
  have hcompl : Finset.image Subtype.val S₀ᶜ = (Finset.image Subtype.val S₀)ᶜ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have e : y = x := hinj hxy
      subst e
      exact hx hy
    · intro h
      exact ⟨⟨i, Finset.mem_univ i⟩, fun hm => h ⟨_, hm, rfl⟩, rfl⟩
  have h1 : sampleMean (y₁ ∘ Subtype.val) S₀ =
      sampleMean y₁ (Finset.image Subtype.val S₀) := by
    simp only [sampleMean, Finset.sum_image (fun x _ y _ h => hinj h), hcard,
      Function.comp_apply]
  have h0 : sampleMean (y₀ ∘ Subtype.val) S₀ᶜ =
      sampleMean y₀ (Finset.image Subtype.val S₀)ᶜ := by
    rw [← hcompl]
    simp only [sampleMean, Finset.sum_image (fun x _ y _ h => hinj h), hcard,
      Function.comp_apply]
  unfold blockContrast
  rw [Fin.sum_univ_one]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [diffInMeans, diffInMeans, h1, h0]
  ring

/-- Negative: a one-subject block cannot satisfy both arm hypotheses. -/
example : ¬ ∃ n : Fin 1 → ℕ, (∀ b, 1 ≤ n b) ∧
    (∀ b, n b + 1 ≤ (((fun _ : Fin 1 => ({0} : Finset (Fin 3))) b).card)) := by
  rintro ⟨n, h1, h0⟩
  have h1' := h1 0
  have h0' := h0 0
  simp only [Finset.card_singleton] at h0'
  omega

/-- Degenerate weight: the summand of an empty block is zero for every
per-block statistic value. -/
example (y₀ y₁ : Fin 4 → ℝ) (S₀ : Finset ↥(∅ : Finset (Fin 4))) :
    ((∅ : Finset (Fin 4)).card : ℝ) * diffInMeans (y₀ ∘ Subtype.val)
      (y₁ ∘ Subtype.val) S₀ = 0 := by
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul]

end MathlibExtTest.Probability.Statistics.Experiment
