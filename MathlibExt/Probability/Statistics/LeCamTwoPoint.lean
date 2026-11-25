/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MeasurePinsker
public import MathlibExt.InformationTheory.DobrushinContraction
public import Mathlib.Probability.Decision.Risk.Defs

/-!
# Le Cam's two-point method

Let `P : Kernel Θ Ω` be a statistical model and `ℓ : Θ → Θ → [0, ∞]` a loss satisfying the
`α`-triangle inequality `ℓ(θ₀, θ₁) ≤ α (ℓ(θ₀, t) + ℓ(θ₁, t))`. Le Cam's two-point lower bound
says that the minimax risk over all randomised estimators (Mathlib's `minimaxRisk`, an infimum
over Markov kernels `Ω → Θ`) satisfies

`minimaxRisk ℓ P ≥ sup_{θ₀, θ₁} ℓ(θ₀, θ₁) (1 - TV(P θ₀, P θ₁)) / (2α)`.

Statements are multiplied out (`ℓ (1 - TV) ≤ 2α · risk`) to avoid division in `ℝ≥0∞`, and use
lower Lebesgue integrals, so no integrability hypothesis is needed.

## Main results

* `mul_one_sub_totalVariationDist_le_two_mul_max`: the two-point bound for one deterministic
  estimator `T : Ω → Θ`, from the common part of `P₀` and `P₁`
  (`MeasurePinsker.exists_le_le_measure_univ_eq`, mass `1 - TV`).
* `mul_one_sub_totalVariationDist_le_minimax`: the bound for `minimaxRisk`. A randomised estimator
  `κ` is reduced to the identity estimator on the output laws `κ ∘ P θᵢ`, whose total variation is
  at most `TV(P θ₀, P θ₁)` by the data-processing inequality
  (`DobrushinContraction.totalVariationDist_comp_le_self`).
* `mul_one_sub_sqrt_klDiv_le_minimax`: the same bound with `TV` replaced through Pinsker's
  inequality by `√(D(P θ₀ ‖ P θ₁) / 2)`.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Section 28.3.2 (minimax risk over randomised estimators) and Theorem 31.1
  (two-point lower bound, eq. (31.2)).
* L. Le Cam, *Convergence of estimates under dimensionality restrictions*, Ann. Statist. 1
  (1973), 38-53.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ENNReal
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker
open MathlibExt.InformationTheory.DobrushinContraction

namespace MathlibExt.Probability.Statistics.LeCamTwoPoint

variable {Ω Θ : Type*} [MeasurableSpace Ω]

/-- **Le Cam's two-point lower bound** for one deterministic estimator. Let `P₀`, `P₁` be
probability measures,
`ℓ : Θ → Θ → [0, ∞]` a loss and `α` a constant with
`ℓ(θ₀, θ₁) ≤ α (ℓ(θ₀, t) + ℓ(θ₁, t))` for every `t`. Then every estimator `T : Ω → Θ` whose
losses are measurable satisfies
`ℓ(θ₀, θ₁) (1 - TV(P₀, P₁)) ≤ 2α max(E_{P₀} ℓ(θ₀, T), E_{P₁} ℓ(θ₁, T))`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 31.1, eq. (31.2); the `α`-triangle inequality (31.1) is only
needed at the pair `θ₀, θ₁`. -/
theorem mul_one_sub_totalVariationDist_le_two_mul_max (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (ℓ : Θ → Θ → ℝ≥0∞) (θ₀ θ₁ : Θ)
    (α : ℝ≥0∞) (htri : ∀ t, ℓ θ₀ θ₁ ≤ α * (ℓ θ₀ t + ℓ θ₁ t)) (T : Ω → Θ)
    (hT₀ : Measurable fun ω => ℓ θ₀ (T ω)) (hT₁ : Measurable fun ω => ℓ θ₁ (T ω)) :
    ℓ θ₀ θ₁ * ENNReal.ofReal (1 - totalVariationDist P₀ P₁) ≤
      2 * α * max (∫⁻ ω, ℓ θ₀ (T ω) ∂P₀) (∫⁻ ω, ℓ θ₁ (T ω) ∂P₁) := by
  obtain ⟨m, hm₀, hm₁, hmass⟩ := exists_le_le_measure_univ_eq P₀ P₁
  set R₀ := ∫⁻ ω, ℓ θ₀ (T ω) ∂P₀
  set R₁ := ∫⁻ ω, ℓ θ₁ (T ω) ∂P₁
  calc ℓ θ₀ θ₁ * ENNReal.ofReal (1 - totalVariationDist P₀ P₁)
      = ∫⁻ _, ℓ θ₀ θ₁ ∂m := by rw [lintegral_const, hmass]
    _ ≤ ∫⁻ ω, α * (ℓ θ₀ (T ω) + ℓ θ₁ (T ω)) ∂m := lintegral_mono fun ω => htri (T ω)
    _ = α * (∫⁻ ω, ℓ θ₀ (T ω) ∂m + ∫⁻ ω, ℓ θ₁ (T ω) ∂m) := by
        have hsum : Measurable fun ω => ℓ θ₀ (T ω) + ℓ θ₁ (T ω) := hT₀.add hT₁
        rw [lintegral_const_mul α hsum, lintegral_add_left hT₀]
    _ ≤ α * (R₀ + R₁) := by
        gcongr
        · exact lintegral_mono' hm₀ le_rfl
        · exact lintegral_mono' hm₁ le_rfl
    _ ≤ α * (max R₀ R₁ + max R₀ R₁) := by gcongr <;> simp
    _ = 2 * α * max R₀ R₁ := by ring

/-- **Le Cam's two-point lower bound.** Let `P : Kernel Θ Ω` be a statistical model of
probability measures and `ℓ : Θ → Θ → [0, ∞]` a loss, measurable in its second argument, satisfying
the `α`-triangle inequality `ℓ(θ₀, θ₁) ≤ α (ℓ(θ₀, t) + ℓ(θ₁, t))` with `α < ∞`. For all
`θ₀, θ₁`, `ℓ(θ₀, θ₁) (1 - TV(P θ₀, P θ₁)) ≤ 2α · minimaxRisk ℓ P`, where `minimaxRisk ℓ P` is the
infimum over all randomised estimators (Markov kernels `κ : Ω → Θ`) of
`sup_θ E_{(κ ∘ P)(θ)} ℓ(θ, ·)`. For `0 < α < ∞` the minimax risk is at least
`ℓ(θ₀, θ₁) (1 - TV(P θ₀, P θ₁)) / (2α)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 31.1, eq. (31.2), with the minimax risk of Section 28.3.2. -/
theorem mul_one_sub_totalVariationDist_le_minimax [MeasurableSpace Θ] (P : Kernel Θ Ω)
    [IsMarkovKernel P] (ℓ : Θ → Θ → ℝ≥0∞) (hℓ : ∀ θ, Measurable (ℓ θ)) (α : ℝ≥0∞)
    (hα : α ≠ ⊤) (htri : ∀ θ₀ θ₁ t, ℓ θ₀ θ₁ ≤ α * (ℓ θ₀ t + ℓ θ₁ t)) (θ₀ θ₁ : Θ) :
    ℓ θ₀ θ₁ * ENNReal.ofReal (1 - totalVariationDist (P θ₀) (P θ₁)) ≤
      2 * α * minimaxRisk ℓ P := by
  rcases eq_or_ne α 0 with rfl | hα₀
  · have h0 : ℓ θ₀ θ₁ = 0 := le_antisymm (by simpa using htri θ₀ θ₁ θ₀) bot_le
    simp [h0]
  have h2 : 2 * α ≠ 0 := mul_ne_zero two_ne_zero hα₀
  have h2' : 2 * α ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hα
  unfold minimaxRisk
  rw [ENNReal.mul_iInf_of_ne h2 h2']
  refine le_iInf fun κ => ?_
  rw [ENNReal.mul_iInf_of_ne h2 h2']
  refine le_iInf fun hκ => ?_
  have hmax := mul_one_sub_totalVariationDist_le_two_mul_max (κ ∘ₘ P θ₀) (κ ∘ₘ P θ₁) ℓ θ₀ θ₁ α
    (htri θ₀ θ₁) id (hℓ θ₀) (hℓ θ₁)
  have hdpi := totalVariationDist_comp_le_self κ (P θ₀) (P θ₁)
  calc ℓ θ₀ θ₁ * ENNReal.ofReal (1 - totalVariationDist (P θ₀) (P θ₁))
      ≤ ℓ θ₀ θ₁ * ENNReal.ofReal (1 - totalVariationDist (κ ∘ₘ P θ₀) (κ ∘ₘ P θ₁)) := by
        gcongr
    _ ≤ _ := hmax
    _ ≤ 2 * α * ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := by
        gcongr
        refine max_le ?_ ?_
        · exact le_trans (by rw [Kernel.comp_apply]; rfl)
            (le_iSup (fun θ => ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) θ₀)
        · exact le_trans (by rw [Kernel.comp_apply]; rfl)
            (le_iSup (fun θ => ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) θ₁)

/-- **Le Cam's two-point bound with Pinsker's inequality.** Under the hypotheses of
`mul_one_sub_totalVariationDist_le_minimax`, if `D(P θ₀ ‖ P θ₁) < ∞` then
`ℓ(θ₀, θ₁) (1 - √(D(P θ₀ ‖ P θ₁) / 2)) ≤ 2α · minimaxRisk ℓ P` (natural logarithm). This is the
usual way the two-point method is applied: the divergence tensorizes over i.i.d. samples, while
total variation does not.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 31.1 combined with Pinsker's inequality, Theorem 7.10, as in
Section 31.1. -/
theorem mul_one_sub_sqrt_klDiv_le_minimax [MeasurableSpace Θ] (P : Kernel Θ Ω)
    [IsMarkovKernel P] (ℓ : Θ → Θ → ℝ≥0∞) (hℓ : ∀ θ, Measurable (ℓ θ)) (α : ℝ≥0∞)
    (hα : α ≠ ⊤) (htri : ∀ θ₀ θ₁ t, ℓ θ₀ θ₁ ≤ α * (ℓ θ₀ t + ℓ θ₁ t)) (θ₀ θ₁ : Θ)
    (hfin : InformationTheory.klDiv (P θ₀) (P θ₁) ≠ ⊤) :
    ℓ θ₀ θ₁ * ENNReal.ofReal (1 - Real.sqrt ((InformationTheory.klDiv (P θ₀) (P θ₁)).toReal / 2))
      ≤ 2 * α * minimaxRisk ℓ P := by
  refine le_trans ?_ (mul_one_sub_totalVariationDist_le_minimax P ℓ hℓ α hα htri θ₀ θ₁)
  gcongr
  exact totalVariationDist_le_sqrt_klDiv hfin

end MathlibExt.Probability.Statistics.LeCamTwoPoint
