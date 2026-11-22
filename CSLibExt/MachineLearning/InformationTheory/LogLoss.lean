/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteEntropy

/-!
# The cross-entropy (log) loss of a probabilistic classifier

A probabilistic classifier `f : X → PMF α` predicts a distribution over the labels. On a labelled
sample `D : Fin N → X × α`, its **cross-entropy loss** is the average of `H(δ_y, f x)`, the
cross-entropy of the one-hot label against the prediction (MathlibExt's `crossEntropy`, in bits).

* `crossEntropyLoss_eq`: the loss is the average surprisal `-log₂ f x y` of the labels, i.e. the
  average negative log-likelihood.
* `crossEntropyLoss_eq_top_iff`: the loss is infinite exactly when some label is predicted to have
  probability `0`.
* `crossEntropyLoss_eq_neg_logb_prod`: when every label has positive probability, the loss is
  `-log₂ L / N`, where `L` is the likelihood of the sample.
* `crossEntropyLoss_le_iff` (**minimizing cross-entropy is maximum likelihood**): on a nonempty
  sample, one classifier has smaller loss than another exactly when it gives the labels larger
  likelihood, including classifiers that rule out an observed label (likelihood `0`, loss `∞`).

For one population label distribution `p`, the expected loss of a fixed prediction `q` is
`crossEntropy p q` (`lintegral_surprisal`), minimized only at `q = p`
(`crossEntropy_eq_shannonEntropy_iff`). Both are in
`MathlibExt/InformationTheory/FiniteEntropy.lean`.

## References

* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, §4.2 and
  Chapter 6.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.InformationTheory

open Real _root_.InformationTheory
open scoped ENNReal

variable {α X : Type*} [Fintype α] {N : ℕ}

/-- The average **cross-entropy (log) loss** of a probabilistic classifier `f` on a labelled
sample `D`, in bits. -/
noncomputable def crossEntropyLoss (f : X → PMF α) (D : Fin N → X × α) : ℝ≥0∞ :=
  (∑ n, crossEntropy (PMF.pure (D n).2) (f (D n).1)) / N

/-- **The cross-entropy loss is the average negative log-likelihood**: the average surprisal of the
labels. -/
theorem crossEntropyLoss_eq (f : X → PMF α) (D : Fin N → X × α) :
    crossEntropyLoss f D = (∑ n, surprisal (f (D n).1 (D n).2)) / N := by
  simp only [crossEntropyLoss, crossEntropy_pure]

/-- The loss is infinite exactly when some label is predicted to be impossible. -/
theorem crossEntropyLoss_eq_top_iff (f : X → PMF α) (D : Fin N → X × α) (hN : N ≠ 0) :
    crossEntropyLoss f D = ∞ ↔ ∃ n, f (D n).1 (D n).2 = 0 := by
  rw [crossEntropyLoss_eq, ENNReal.div_eq_top]
  simp [hN, ENNReal.sum_eq_top, surprisal_eq_top_iff]

/-- When every label has positive probability, the loss is `-log₂ L / N` for the likelihood `L`
of the sample. -/
theorem crossEntropyLoss_eq_neg_logb_prod (f : X → PMF α) (D : Fin N → X × α)
    (hpos : ∀ n, f (D n).1 (D n).2 ≠ 0) :
    crossEntropyLoss f D =
      ENNReal.ofReal (-logb 2 (∏ n, (f (D n).1 (D n).2).toReal)) / N := by
  have hne : ∀ n, (f (D n).1 (D n).2).toReal ≠ 0 := fun n ↦
    ENNReal.toReal_ne_zero.mpr ⟨hpos n, PMF.apply_ne_top _ _⟩
  have hnonneg : ∀ n, 0 ≤ -logb 2 (f (D n).1 (D n).2).toReal := fun n ↦ by
    rw [neg_nonneg]
    exact logb_nonpos one_lt_two ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _))
  rw [crossEntropyLoss_eq]
  simp_rw [surprisal_of_ne_zero (hpos _)]
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ ↦ hnonneg n, logb_prod Finset.univ _ fun n _ ↦ hne n,
    Finset.sum_neg_distrib]

/-- The cross-entropy ordering when both classifiers give every label positive probability. -/
theorem crossEntropyLoss_le_iff_of_ne_zero (f g : X → PMF α) (D : Fin N → X × α) (hN : N ≠ 0)
    (hf : ∀ n, f (D n).1 (D n).2 ≠ 0) (hg : ∀ n, g (D n).1 (D n).2 ≠ 0) :
    crossEntropyLoss f D ≤ crossEntropyLoss g D ↔
      ∏ n, (g (D n).1 (D n).2).toReal ≤ ∏ n, (f (D n).1 (D n).2).toReal := by
  have hpos : ∀ h : X → PMF α, (∀ n, h (D n).1 (D n).2 ≠ 0) →
      0 < ∏ n, (h (D n).1 (D n).2).toReal := fun h hh ↦
    Finset.prod_pos fun n _ ↦ ENNReal.toReal_pos (hh n) (PMF.apply_ne_top _ _)
  have hle1 : ∀ h : X → PMF α, ∏ n, (h (D n).1 (D n).2).toReal ≤ 1 := fun h ↦
    Finset.prod_le_one₀ (fun n _ ↦ ENNReal.toReal_nonneg) fun n _ ↦
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)
  have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  have hnn : ∀ h : X → PMF α, (∀ n, h (D n).1 (D n).2 ≠ 0) →
      0 ≤ -logb 2 (∏ n, (h (D n).1 (D n).2).toReal) := fun h hh ↦
    neg_nonneg.mpr (logb_nonpos one_lt_two (hpos h hh).le (hle1 h))
  rw [crossEntropyLoss_eq_neg_logb_prod f D hf, crossEntropyLoss_eq_neg_logb_prod g D hg,
    div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top N))
      (ENNReal.inv_ne_top.mpr hN'),
    ENNReal.ofReal_le_ofReal_iff (hnn g hg), neg_le_neg_iff,
    logb_le_logb one_lt_two (hpos g hg) (hpos f hf)]

/-- **Minimizing cross-entropy is maximum likelihood**: on a nonempty sample, `f` has loss at most
that of `g` exactly when it gives the labels at least as large a likelihood. A label predicted to be
impossible gives likelihood `0` and loss `∞`. -/
theorem crossEntropyLoss_le_iff (f g : X → PMF α) (D : Fin N → X × α) (hN : N ≠ 0) :
    crossEntropyLoss f D ≤ crossEntropyLoss g D ↔
      ∏ n, (g (D n).1 (D n).2).toReal ≤ ∏ n, (f (D n).1 (D n).2).toReal := by
  have hL : ∀ h : X → PMF α,
      ∏ n, (h (D n).1 (D n).2).toReal = 0 ↔ ∃ n, h (D n).1 (D n).2 = 0 := fun h ↦ by
    rw [Finset.prod_eq_zero_iff]
    simp [ENNReal.toReal_eq_zero_iff, PMF.apply_ne_top]
  have hnn : ∀ h : X → PMF α, 0 ≤ ∏ n, (h (D n).1 (D n).2).toReal := fun h ↦
    Finset.prod_nonneg fun n _ ↦ ENNReal.toReal_nonneg
  by_cases hf : ∃ n, f (D n).1 (D n).2 = 0
  · rw [(crossEntropyLoss_eq_top_iff f D hN).mpr hf, (hL f).mpr hf, top_le_iff,
      crossEntropyLoss_eq_top_iff g D hN, ← hL g]
    exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (hnn g)⟩
  by_cases hg : ∃ n, g (D n).1 (D n).2 = 0
  · rw [(crossEntropyLoss_eq_top_iff g D hN).mpr hg, (hL g).mpr hg]
    exact iff_of_true le_top (hnn f)
  push Not at hf hg
  exact crossEntropyLoss_le_iff_of_ne_zero f g D hN hf hg

end Cslib.MachineLearning.InformationTheory
