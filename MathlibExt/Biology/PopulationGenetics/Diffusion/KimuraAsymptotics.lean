/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# New-mutant asymptotics of Kimura's fixation formula

These are asymptotic statements about the diffusion formula
`kimuraFixation σ x`, not about a finite Wright–Fisher chain. Write `M = 2N`
for the number of gene copies, so one new copy has frequency `1/M`, and
`σ = M s = 2N s` for a per-generation selection coefficient `s`.

At fixed scaled selection `α`,
`M * kimuraFixation α (1/M) → kimuraSlope α`. The slope constant satisfies
`kimuraSlope α ~ 2α` as `α → ∞`. Haldane's approximation `2s` is valid in
relative form exactly in the joint regime `s_M → 0` and `M s_M → ∞`. For
fixed `s > 0`, instead,
`kimuraFixation (M * s) (1/M) → 1 - Real.exp (-2 * s) < 2 * s`.

The theorems named `*_of_kimuraForm` are stated for any functions satisfying
the displayed closed forms; the remaining theorems instantiate them at
`kimuraFixation` and `kimuraSlope`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a
  population*, Genetics 47 (1962), 713–719.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

open Filter Topology

/-- Slope of `Real.exp` at `0`: `(e ^ t - 1) / t → 1` as `t → 0` away from `0`. -/
private theorem exp_slope_nhdsWithin :
    Tendsto (fun t : ℝ => (Real.exp t - 1) / t) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope
  rw [Real.exp_zero] at h
  have hfun : slope Real.exp 0 = (fun t : ℝ => (Real.exp t - 1) / t) := by
    funext t
    simp [slope, sub_zero, Real.exp_zero, div_eq_inv_mul]
  rw [hfun] at h
  exact h

/-- Sequential slope limit for `Real.exp` at `0`. -/
private theorem tendsto_exp_sub_one_div (t : ℕ → ℝ) (h0 : Tendsto t atTop (𝓝 0))
    (hne : ∀ᶠ M in atTop, t M ≠ 0) :
    Tendsto (fun M : ℕ => (Real.exp (t M) - 1) / (t M)) atTop (𝓝 1) := by
  have hw : Tendsto t atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h0, ?_⟩
    simpa using hne
  exact exp_slope_nhdsWithin.comp hw

/-- `Real.exp (-2 * σ) → 0` as `σ → ∞`. -/
private theorem tendsto_exp_neg_two_mul_atTop :
    Tendsto (fun σ : ℝ => Real.exp (-2 * σ)) atTop (𝓝 0) := by
  have h : Tendsto (fun σ : ℝ => (-2 : ℝ) * σ) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id
  exact Real.tendsto_exp_atBot.comp h

/-- Sequential version: `Real.exp (-2 * σ M) → 0` when `σ M → ∞`. -/
private theorem tendsto_exp_neg_two_mul_seq (σ : ℕ → ℝ) (h : Tendsto σ atTop atTop) :
    Tendsto (fun M : ℕ => Real.exp (-2 * σ M)) atTop (𝓝 0) :=
  tendsto_exp_neg_two_mul_atTop.comp h

/-- Positivity of `1 - Real.exp (-2 * σ)` for `σ > 0`. -/
private theorem one_sub_exp_neg_two_mul_pos (σ : ℝ) (hσ : 0 < σ) :
    0 < 1 - Real.exp (-2 * σ) := by
  have h : Real.exp (-2 * σ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- `(1 - Real.exp (-t)) / t` is antitone on `(0, ∞)`. -/
private theorem one_sub_exp_div_antitone (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (1 - Real.exp (-v)) / v ≤ (1 - Real.exp (-u)) / u := by
  obtain ⟨w, hw0, rfl⟩ : ∃ w, 0 ≤ w ∧ v = u + w := ⟨v - u, sub_nonneg.mpr huv, by ring⟩
  have hv : 0 < u + w := lt_of_lt_of_le hu (le_add_of_nonneg_right hw0)
  rw [div_le_iff₀ hv, div_mul_eq_mul_div, le_div_iff₀ hu]
  have e1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have e2 : 1 - w ≤ Real.exp (-w) := by
    have h := Real.add_one_le_exp (-w)
    linarith
  have key : u * (1 - Real.exp (-w)) ≤ w * (Real.exp u - 1) := by
    have hA : u * (1 - Real.exp (-w)) ≤ u * w :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hu)
    have hB : u * w ≤ w * (Real.exp u - 1) := by
      rw [mul_comm u w]
      exact mul_le_mul_of_nonneg_left (by linarith) hw0
    linarith
  have hApos : 0 < Real.exp (-u) := Real.exp_pos _
  have hAE : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    have hzero : -u + u = (0 : ℝ) := by ring
    rw [hzero, Real.exp_zero]
  have hexp : Real.exp (-(u + w)) = Real.exp (-u) * Real.exp (-w) := by
    rw [show -(u + w) = -u + -w by ring, Real.exp_add]
  rw [hexp]
  have key2 := mul_le_mul_of_nonneg_left key (le_of_lt hApos)
  have hAE' : Real.exp (-u) * (w * (Real.exp u - 1)) = w * (1 - Real.exp (-u)) := by
    linear_combination w * hAE
  have key3 : Real.exp (-u) * (u * (1 - Real.exp (-w))) ≤ w * (1 - Real.exp (-u)) := by
    rw [← hAE']
    exact key2
  linear_combination key3

/-- The factor `(1 - Real.exp (-2 * s)) / (2 * s)` lies in `(0, 1)` for `s > 0`. -/
private theorem kimura_f_mem (s : ℝ) (hs : 0 < s) :
    0 < (1 - Real.exp (-2 * s)) / (2 * s) ∧ (1 - Real.exp (-2 * s)) / (2 * s) < 1 := by
  have hnum : 0 < 1 - Real.exp (-2 * s) := one_sub_exp_neg_two_mul_pos s hs
  have hden : 0 < (2 : ℝ) * s := by linarith
  refine ⟨div_pos hnum hden, ?_⟩
  rw [div_lt_one hden]
  have h := Real.add_one_lt_exp (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) (ne_of_gt hs))
  linarith

/-- The factor `1 / (1 - Real.exp (-2 * σ))` exceeds `1` for `σ > 0`. -/
private theorem one_div_one_sub_exp_gt_one (σ : ℝ) (hσ : 0 < σ) :
    1 < 1 / (1 - Real.exp (-2 * σ)) := by
  apply one_lt_one_div (one_sub_exp_neg_two_mul_pos σ hσ)
  have hpos : 0 < Real.exp (-2 * σ) := Real.exp_pos _
  linarith

/-- Non-strict antitone comparison for the `g` factor on `(0, ∞)`. -/
private theorem one_div_one_sub_exp_le (σ₁ σ₂ : ℝ) (h1 : 0 < σ₁) (h2 : 0 < σ₂) (hle : σ₁ ≤ σ₂) :
    1 / (1 - Real.exp (-2 * σ₂)) ≤ 1 / (1 - Real.exp (-2 * σ₁)) := by
  have d1 : 0 < 1 - Real.exp (-2 * σ₁) := one_sub_exp_neg_two_mul_pos σ₁ h1
  have d2 : 0 < 1 - Real.exp (-2 * σ₂) := one_sub_exp_neg_two_mul_pos σ₂ h2
  have hle' : 1 - Real.exp (-2 * σ₁) ≤ 1 - Real.exp (-2 * σ₂) := by
    have he : Real.exp (-2 * σ₂) ≤ Real.exp (-2 * σ₁) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  exact (one_div_le_one_div d2 d1).mpr hle'

/-- Strict antitone comparison for the `g` factor on `(0, ∞)`. -/
private theorem one_div_one_sub_exp_lt (σ₁ σ₂ : ℝ) (h1 : 0 < σ₁) (h2 : 0 < σ₂) (hlt : σ₁ < σ₂) :
    1 / (1 - Real.exp (-2 * σ₂)) < 1 / (1 - Real.exp (-2 * σ₁)) := by
  have d1 : 0 < 1 - Real.exp (-2 * σ₁) := one_sub_exp_neg_two_mul_pos σ₁ h1
  have d2 : 0 < 1 - Real.exp (-2 * σ₂) := one_sub_exp_neg_two_mul_pos σ₂ h2
  have hlt' : 1 - Real.exp (-2 * σ₁) < 1 - Real.exp (-2 * σ₂) := by
    have he : Real.exp (-2 * σ₂) < Real.exp (-2 * σ₁) :=
      Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact (one_div_lt_one_div d2 d1).mpr hlt'

/-- The Haldane ratio factors as `f * g` whenever the terms are nonzero. -/
private theorem kimura_ratio_eq (u : ℝ → ℝ → ℝ)
    (hu : ∀ σ x, σ ≠ 0 → u σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)))
    (s : ℕ → ℝ) (M : ℕ) (hM : (M : ℝ) ≠ 0) (hsM : s M ≠ 0) :
    u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)
      = ((1 - Real.exp (-2 * s M)) / (2 * s M)) * (1 / (1 - Real.exp (-2 * ((M : ℝ) * s M)))) := by
  have hσ : (M : ℝ) * s M ≠ 0 := mul_ne_zero hM hsM
  have hD : (1 - Real.exp (-2 * ((M : ℝ) * s M))) ≠ 0 :=
    one_sub_exp_ne_zero hσ
  have h2s : (2 : ℝ) * s M ≠ 0 := mul_ne_zero (by norm_num) hsM
  have hexp : -2 * ((M : ℝ) * s M) * (1 / (M : ℝ)) = -2 * s M := by
    calc -2 * ((M : ℝ) * s M) * (1 / (M : ℝ))
        = -2 * s M * ((M : ℝ) * (1 / (M : ℝ))) := by ring
      _ = -2 * s M := by rw [mul_one_div_cancel hM, mul_one]
  rw [hu _ _ hσ, hexp, div_div, div_mul_div_comm, mul_one, mul_comm (2 * s M) _]

/-- **New-mutant limit at fixed scaled selection.** Let `u` be Kimura's fixation probability
`u σ x = (1 - e^{-2σx}) / (1 - e^{-2σ})` for `σ ≠ 0` and `u 0 x = x`, and let `K` be its slope
constant `K σ = 2σ / (1 - e^{-2σ})` for `σ ≠ 0` and `K 0 = 1`. For every fixed `α`, the scaled
fixation probability of a single new copy among `M` gene copies converges:
`M * u α (1 / M) → K α` as `M → ∞`. -/
theorem tendsto_natCast_mul_one_div_of_kimuraForm (u : ℝ → ℝ → ℝ) (K : ℝ → ℝ)
    (hu : ∀ σ x, σ ≠ 0 → u σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)))
    (hu0 : ∀ x, u 0 x = x)
    (hK : ∀ σ, σ ≠ 0 → K σ = 2 * σ / (1 - Real.exp (-2 * σ))) (hK0 : K 0 = 1) (α : ℝ) :
    Tendsto (fun M : ℕ => (M : ℝ) * u α (1 / (M : ℝ))) atTop (𝓝 (K α)) := by
  by_cases hα : α = 0
  · subst hα
    rw [hK0]
    have heq : (fun M : ℕ => (M : ℝ) * u 0 (1 / (M : ℝ))) =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with M hM
      rw [hu0]
      have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
      exact mul_one_div_cancel hM'
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  · have hD : (1 - Real.exp (-2 * α)) ≠ 0 := one_sub_exp_ne_zero hα
    have ht0 : Tendsto (fun M : ℕ => -2 * α / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (-2 * α)
    have htne : ∀ᶠ (M : ℕ) in atTop, -2 * α / (M : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
      exact div_ne_zero (mul_ne_zero (by norm_num) hα)
        (Nat.cast_ne_zero.mpr (by omega))
    have hslope := tendsto_exp_sub_one_div (fun M : ℕ => -2 * α / (M : ℝ)) ht0 htne
    have hNeq : (fun M : ℕ => (M : ℝ) * (1 - Real.exp (-2 * α / (M : ℝ)))) =ᶠ[atTop]
        (fun M : ℕ => 2 * α * ((Real.exp (-2 * α / (M : ℝ)) - 1) / (-2 * α / (M : ℝ)))) := by
      filter_upwards [eventually_ne_atTop 0] with M hM
      have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
      have ht : (-2 * α / (M : ℝ)) ≠ 0 :=
        div_ne_zero (mul_ne_zero (by norm_num) hα) hM'
      field_simp
      ring
    have hNlim : Tendsto (fun M : ℕ => 2 * α * ((Real.exp (-2 * α / (M : ℝ)) - 1) /
        (-2 * α / (M : ℝ)))) atTop (𝓝 (2 * α * 1)) :=
      tendsto_const_nhds.mul hslope
    rw [mul_one] at hNlim
    have hN : Tendsto (fun M : ℕ => (M : ℝ) * (1 - Real.exp (-2 * α / (M : ℝ)))) atTop
        (𝓝 (2 * α)) :=
      (tendsto_congr' hNeq).mpr hNlim
    have hmain : (fun M : ℕ => (M : ℝ) * u α (1 / (M : ℝ))) =ᶠ[atTop]
        (fun M : ℕ => ((M : ℝ) * (1 - Real.exp (-2 * α / (M : ℝ)))) /
          (1 - Real.exp (-2 * α))) := by
      filter_upwards with M
      rw [hu α _ hα]
      have hexp : -2 * α * (1 / (M : ℝ)) = -2 * α / (M : ℝ) := mul_one_div _ _
      rw [hexp]
      exact (mul_div_assoc _ _ _).symm
    have hKα : K α = 2 * α / (1 - Real.exp (-2 * α)) := hK α hα
    rw [hKα]
    exact (tendsto_congr' hmain).mpr (hN.div tendsto_const_nhds hD)

/-- **Haldane regime of the slope constant.** If `K σ = 2σ / (1 - e^{-2σ})` for `σ ≠ 0`, then
`K α ~ 2α` as `α → ∞`. -/
theorem isEquivalent_two_mul_of_kimuraSlopeForm (K : ℝ → ℝ)
    (hK : ∀ σ, σ ≠ 0 → K σ = 2 * σ / (1 - Real.exp (-2 * σ))) :
    Asymptotics.IsEquivalent atTop K (fun α => 2 * α) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have heq : (fun α : ℝ => K α / (2 * α)) =ᶠ[atTop]
      (fun α : ℝ => 1 / (1 - Real.exp (-2 * α))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    have hα' : α ≠ 0 := ne_of_gt hα
    have hD : (1 - Real.exp (-2 * α)) ≠ 0 := one_sub_exp_ne_zero hα'
    have h2α : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα'
    rw [hK α hα']
    field_simp
  have hlim : Tendsto (fun α : ℝ => 1 / (1 - Real.exp (-2 * α))) atTop (𝓝 1) := by
    have he : Tendsto (fun α : ℝ => Real.exp (-2 * α)) atTop (𝓝 0) :=
      tendsto_exp_neg_two_mul_atTop
    have h1 : Tendsto (fun α : ℝ => 1 - Real.exp (-2 * α)) atTop (𝓝 1) := by
      have hsub : Tendsto (fun α : ℝ => 1 - Real.exp (-2 * α)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub he
      simpa using hsub
    have h1inv := h1.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1inv
  exact (tendsto_congr' heq).mpr hlim

/-- **Haldane's `2s` in the joint regime.** Let `u σ x = (1 - e^{-2σx}) / (1 - e^{-2σ})` for
`σ ≠ 0`. If the per-generation selection coefficients satisfy `s M → 0` and `M * s M → ∞`, then
the fixation probability of a single new copy among `M` gene copies, with scaled selection
`α = M * s M`, is `2 * s M * (1 + o(1))`: `u (M * s M) (1 / M) / (2 * s M) → 1`. -/
theorem tendsto_div_two_mul_of_kimuraForm (u : ℝ → ℝ → ℝ)
    (hu : ∀ σ x, σ ≠ 0 → u σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)))
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (hMs : Tendsto (fun M : ℕ => (M : ℝ) * s M) atTop atTop) :
    Tendsto (fun M : ℕ => u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)) atTop (𝓝 1) := by
  have hpos : ∀ᶠ (M : ℕ) in atTop, 0 < s M := by
    have h1 := hMs.eventually_ge_atTop (1 : ℝ)
    have h2 := eventually_ge_atTop (1 : ℕ)
    filter_upwards [h1, h2] with M hM1 hM2
    have hM0 : 0 < M := by omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    by_contra hcon
    have hcon' : s M ≤ 0 := le_of_not_gt hcon
    have hle : (M : ℝ) * s M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hMpos) hcon'
    linarith
  have heq : (fun M : ℕ => u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)) =ᶠ[atTop]
      (fun M : ℕ => ((1 - Real.exp (-2 * s M)) / (2 * s M)) *
        (1 / (1 - Real.exp (-2 * ((M : ℝ) * s M))))) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ), hpos] with M hM hposM
    exact kimura_ratio_eq u hu s M (Nat.cast_ne_zero.mpr hM) (ne_of_gt hposM)
  have hf : Tendsto (fun M : ℕ => (1 - Real.exp (-2 * s M)) / (2 * s M)) atTop (𝓝 1) := by
    have ht0 : Tendsto (fun M : ℕ => -2 * s M) atTop (𝓝 0) := by
      have hcm : Tendsto (fun M : ℕ => -2 * s M) atTop (𝓝 (-2 * 0)) := hs.const_mul (-2)
      simpa using hcm
    have htne : ∀ᶠ (M : ℕ) in atTop, -2 * s M ≠ 0 := by
      filter_upwards [hpos] with M hM
      exact mul_ne_zero (by norm_num) (ne_of_gt hM)
    have hslope := tendsto_exp_sub_one_div (fun M : ℕ => -2 * s M) ht0 htne
    have heqf : (fun M : ℕ => (Real.exp (-2 * s M) - 1) / (-2 * s M)) =ᶠ[atTop]
        (fun M : ℕ => (1 - Real.exp (-2 * s M)) / (2 * s M)) := by
      filter_upwards [hpos] with M hM
      have h2s : (2 : ℝ) * s M ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hM)
      have ht : -2 * s M ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hM)
      field_simp
      ring
    exact (tendsto_congr' heqf).mp hslope
  have hg : Tendsto (fun M : ℕ => 1 / (1 - Real.exp (-2 * ((M : ℝ) * s M)))) atTop (𝓝 1) := by
    have he : Tendsto (fun M : ℕ => Real.exp (-2 * ((M : ℝ) * s M))) atTop (𝓝 0) :=
      tendsto_exp_neg_two_mul_seq _ hMs
    have h1 : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * s M))) atTop (𝓝 1) := by
      have hsub : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * s M))) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub he
      simpa using hsub
    have h1inv := h1.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1inv
  have hmul := hf.mul hg
  rw [mul_one] at hmul
  exact (tendsto_congr' heq).mpr hmul

/-- **Haldane's `2s` holds only in the joint regime.** Let `u σ x = (1 - e^{-2σx}) / (1 - e^{-2σ})`
for `σ ≠ 0`. If `u (M * s M) (1 / M) / (2 * s M) → 1` as `M → ∞`, then `s M → 0` and
`M * s M → ∞`. -/
theorem tendsto_zero_and_tendsto_atTop_of_kimuraForm (u : ℝ → ℝ → ℝ)
    (hu : ∀ σ x, σ ≠ 0 → u σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)))
    (s : ℕ → ℝ)
    (h : Tendsto (fun M : ℕ => u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)) atTop (𝓝 1)) :
    Tendsto s atTop (𝓝 0) ∧ Tendsto (fun M : ℕ => (M : ℝ) * s M) atTop atTop := by
  have hpos : ∀ᶠ (M : ℕ) in atTop, 0 < s M := by
    have hr : ∀ᶠ (M : ℕ) in atTop,
        (1 / 2 : ℝ) < u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) :=
      h.eventually (lt_mem_nhds (by norm_num))
    have hM1 := eventually_ge_atTop (1 : ℕ)
    filter_upwards [hr, hM1] with M hrM hM1
    by_contra hcon
    have hcon' : s M ≤ 0 := le_of_not_gt hcon
    have hM0 : 0 < M := by omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    rcases eq_or_lt_of_le hcon' with h0 | hneg
    · have hratio : u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) = 0 := by
        simp [h0]
      linarith
    · have hσ : (M : ℝ) * s M < 0 := mul_neg_of_pos_of_neg hMpos hneg
      have hσ' : (M : ℝ) * s M ≠ 0 := ne_of_lt hσ
      have hnum : 1 - Real.exp (-2 * ((M : ℝ) * s M) * (1 / (M : ℝ))) < 0 := by
        have hexp : (0 : ℝ) < -2 * ((M : ℝ) * s M) * (1 / (M : ℝ)) := by
          have h1 : (0 : ℝ) < -2 * ((M : ℝ) * s M) := by linarith
          have h2 : (0 : ℝ) < 1 / (M : ℝ) := one_div_pos.mpr hMpos
          exact mul_pos h1 h2
        have hlt := Real.one_lt_exp_iff.mpr hexp
        linarith
      have hden : 1 - Real.exp (-2 * ((M : ℝ) * s M)) < 0 := by
        have hexp : (0 : ℝ) < -2 * ((M : ℝ) * s M) := by linarith
        have hlt := Real.one_lt_exp_iff.mpr hexp
        linarith
      have hu_pos : 0 < u ((M : ℝ) * s M) (1 / (M : ℝ)) := by
        rw [hu _ _ hσ']
        exact div_pos_of_neg_of_neg hnum hden
      have h2s : (2 : ℝ) * s M < 0 := by linarith
      have hneg_ratio : u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) < 0 :=
        div_neg_of_pos_of_neg hu_pos h2s
      linarith
  have hs0 : Tendsto s atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hfε : (1 - Real.exp (-2 * ε)) / (2 * ε) < 1 := (kimura_f_mem ε hε).2
    have hfεpos : 0 < (1 - Real.exp (-2 * ε)) / (2 * ε) := (kimura_f_mem ε hε).1
    set m : ℝ := (1 + (1 - Real.exp (-2 * ε)) / (2 * ε)) / 2 with hm
    have hfm : (1 - Real.exp (-2 * ε)) / (2 * ε) < m ∧ m < 1 := by
      rw [hm]
      constructor <;> linarith
    have hgM : Tendsto (fun M : ℕ => 1 / (1 - Real.exp (-2 * ((M : ℝ) * ε)))) atTop (𝓝 1) := by
      have hMε : Tendsto (fun M : ℕ => (M : ℝ) * ε) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hε
      have he : Tendsto (fun M : ℕ => Real.exp (-2 * ((M : ℝ) * ε))) atTop (𝓝 0) :=
        tendsto_exp_neg_two_mul_seq _ hMε
      have h1 : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * ε))) atTop (𝓝 1) := by
        have hsub : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * ε))) atTop
            (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub he
        simpa using hsub
      have h1inv := h1.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa using h1inv
    have hB : Tendsto (fun M : ℕ => ((1 - Real.exp (-2 * ε)) / (2 * ε)) *
        (1 / (1 - Real.exp (-2 * ((M : ℝ) * ε))))) atTop
        (𝓝 (((1 - Real.exp (-2 * ε)) / (2 * ε)) * 1)) :=
      tendsto_const_nhds.mul hgM
    rw [mul_one] at hB
    have hr : ∀ᶠ (M : ℕ) in atTop,
        m < u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) :=
      h.eventually (lt_mem_nhds hfm.2)
    have hBlt : ∀ᶠ (M : ℕ) in atTop, ((1 - Real.exp (-2 * ε)) / (2 * ε)) *
        (1 / (1 - Real.exp (-2 * ((M : ℝ) * ε)))) < m :=
      hB.eventually (gt_mem_nhds hfm.1)
    filter_upwards [hr, hBlt, eventually_ge_atTop (1 : ℕ), hpos] with M hrM hBM hM1 hposM
    rw [Real.dist_eq, sub_zero, abs_of_pos hposM]
    by_contra hcon
    have hcon' : ε ≤ s M := le_of_not_gt hcon
    have hM0 : 0 < M := by omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    have hσpos : (0 : ℝ) < (M : ℝ) * s M := mul_pos hMpos hposM
    have hMεpos : (0 : ℝ) < (M : ℝ) * ε := mul_pos hMpos hε
    have hσge : (M : ℝ) * ε ≤ (M : ℝ) * s M :=
      mul_le_mul_of_nonneg_left hcon' (le_of_lt hMpos)
    have hf_le : (1 - Real.exp (-2 * s M)) / (2 * s M) ≤
        (1 - Real.exp (-2 * ε)) / (2 * ε) := by
      have h2s : ∀ t : ℝ, -2 * t = -(2 * t) := fun t => by ring
      have hmain := one_sub_exp_div_antitone (2 * ε) (2 * s M) (by linarith) (by linarith)
      simpa only [h2s] using hmain
    have hg_le : 1 / (1 - Real.exp (-2 * ((M : ℝ) * s M))) ≤
        1 / (1 - Real.exp (-2 * ((M : ℝ) * ε))) :=
      one_div_one_sub_exp_le _ _ hMεpos hσpos hσge
    have hratio_le : u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)
        ≤ ((1 - Real.exp (-2 * ε)) / (2 * ε)) *
          (1 / (1 - Real.exp (-2 * ((M : ℝ) * ε)))) := by
      have hfac := kimura_ratio_eq u hu s M (ne_of_gt hMpos) (ne_of_gt hposM)
      rw [hfac]
      exact mul_le_mul hf_le hg_le
        (le_of_lt (one_div_pos.mpr (one_sub_exp_neg_two_mul_pos _ hσpos)))
        (le_of_lt hfεpos)
    linarith
  have hMs : Tendsto (fun M : ℕ => (M : ℝ) * s M) atTop atTop := by
    rw [tendsto_atTop]
    intro C
    have hC'pos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have hC'ge : C ≤ max C 1 := le_max_left C 1
    have hgC' := one_div_one_sub_exp_gt_one (max C 1) hC'pos
    set m' : ℝ := (1 + 1 / (1 - Real.exp (-2 * max C 1))) / 2 with hm'
    have hm' : 1 < m' ∧ m' < 1 / (1 - Real.exp (-2 * max C 1)) := by
      rw [hm']
      constructor <;> linarith
    have hf1 : Tendsto (fun M : ℕ => (1 - Real.exp (-2 * s M)) / (2 * s M)) atTop (𝓝 1) := by
      have ht0 : Tendsto (fun M : ℕ => -2 * s M) atTop (𝓝 0) := by
        have hcm : Tendsto (fun M : ℕ => -2 * s M) atTop (𝓝 (-2 * 0)) :=
          hs0.const_mul (-2)
        simpa using hcm
      have htne : ∀ᶠ (M : ℕ) in atTop, -2 * s M ≠ 0 := by
        filter_upwards [hpos] with M hM
        exact mul_ne_zero (by norm_num) (ne_of_gt hM)
      have hslope := tendsto_exp_sub_one_div (fun M : ℕ => -2 * s M) ht0 htne
      have heqf : (fun M : ℕ => (Real.exp (-2 * s M) - 1) / (-2 * s M)) =ᶠ[atTop]
          (fun M : ℕ => (1 - Real.exp (-2 * s M)) / (2 * s M)) := by
        filter_upwards [hpos] with M hM
        have h2s : (2 : ℝ) * s M ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hM)
        have ht : -2 * s M ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hM)
        field_simp
        ring
      exact (tendsto_congr' heqf).mp hslope
    have hfg : Tendsto (fun M : ℕ => ((1 - Real.exp (-2 * s M)) / (2 * s M)) *
        (1 / (1 - Real.exp (-2 * max C 1)))) atTop
        (𝓝 (1 * (1 / (1 - Real.exp (-2 * max C 1))))) :=
      hf1.mul tendsto_const_nhds
    rw [one_mul] at hfg
    have hrlt : ∀ᶠ (M : ℕ) in atTop,
        u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) < m' :=
      h.eventually (gt_mem_nhds hm'.1)
    have hfggt : ∀ᶠ (M : ℕ) in atTop, m' <
        ((1 - Real.exp (-2 * s M)) / (2 * s M)) * (1 / (1 - Real.exp (-2 * max C 1))) :=
      hfg.eventually (lt_mem_nhds hm'.2)
    filter_upwards [hrlt, hfggt, eventually_ge_atTop (1 : ℕ), hpos] with M hrM hgM hM1 hposM
    by_contra hcon
    have hcon' : (M : ℝ) * s M < C := lt_of_not_ge hcon
    have hM0 : 0 < M := by omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    have hσpos : (0 : ℝ) < (M : ℝ) * s M := mul_pos hMpos hposM
    have hltC' : (M : ℝ) * s M < max C 1 := lt_of_lt_of_le hcon' hC'ge
    have hg_lt : 1 / (1 - Real.exp (-2 * max C 1)) <
        1 / (1 - Real.exp (-2 * ((M : ℝ) * s M))) :=
      one_div_one_sub_exp_lt _ _ hσpos hC'pos hltC'
    have hfspos : 0 < (1 - Real.exp (-2 * s M)) / (2 * s M) :=
      (kimura_f_mem (s M) hposM).1
    have hratio_gt : ((1 - Real.exp (-2 * s M)) / (2 * s M)) *
        (1 / (1 - Real.exp (-2 * max C 1)))
        < u ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M) := by
      have hfac := kimura_ratio_eq u hu s M (ne_of_gt hMpos) (ne_of_gt hposM)
      rw [hfac]
      exact mul_lt_mul_of_pos_left hg_lt hfspos
    linarith
  exact ⟨hs0, hMs⟩

/-- **Fixed selection coefficient: the limit is `1 - e^{-2s}`, not `2s`.** Let
`u σ x = (1 - e^{-2σx}) / (1 - e^{-2σ})` for `σ ≠ 0`. For fixed `s > 0`, the fixation probability
of a single new copy among `M` gene copies with scaled selection `α = M * s` tends to
`1 - e^{-2s}` as `M → ∞`, and `1 - e^{-2s} < 2s`. -/
theorem tendsto_one_sub_exp_of_kimuraForm (u : ℝ → ℝ → ℝ)
    (hu : ∀ σ x, σ ≠ 0 → u σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun M : ℕ => u ((M : ℝ) * s) (1 / (M : ℝ))) atTop (𝓝 (1 - Real.exp (-2 * s))) ∧
      1 - Real.exp (-2 * s) < 2 * s := by
  have hMs : Tendsto (fun M : ℕ => (M : ℝ) * s) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hs
  have heq : (fun M : ℕ => u ((M : ℝ) * s) (1 / (M : ℝ))) =ᶠ[atTop]
      (fun M : ℕ => (1 - Real.exp (-2 * s)) / (1 - Real.exp (-2 * ((M : ℝ) * s)))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hM0 : 0 < M := by omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    have hσ : (M : ℝ) * s ≠ 0 := ne_of_gt (mul_pos hMpos hs)
    rw [hu _ _ hσ]
    have hexp : -2 * ((M : ℝ) * s) * (1 / (M : ℝ)) = -2 * s := by
      have hM' : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      calc -2 * ((M : ℝ) * s) * (1 / (M : ℝ))
          = -2 * s * ((M : ℝ) * (1 / (M : ℝ))) := by ring
        _ = -2 * s := by rw [mul_one_div_cancel hM', mul_one]
    rw [hexp]
  have he : Tendsto (fun M : ℕ => Real.exp (-2 * ((M : ℝ) * s))) atTop (𝓝 0) :=
    tendsto_exp_neg_two_mul_seq _ hMs
  have hden : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * s))) atTop (𝓝 1) := by
    have hsub : Tendsto (fun M : ℕ => 1 - Real.exp (-2 * ((M : ℝ) * s))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub he
    simpa using hsub
  have hlim : Tendsto (fun M : ℕ => (1 - Real.exp (-2 * s)) /
      (1 - Real.exp (-2 * ((M : ℝ) * s)))) atTop (𝓝 ((1 - Real.exp (-2 * s)) / 1)) :=
    tendsto_const_nhds.div hden (by norm_num)
  rw [div_one] at hlim
  refine ⟨(tendsto_congr' heq).mpr hlim, ?_⟩
  have h := Real.add_one_lt_exp
    (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) (ne_of_gt hs))
  linarith

/-! ### Atlas's Kimura formula -/

/-- Atlas's `kimuraFixation` has the closed form the core lemmas assume (definition unfolding). -/
theorem kimuraFixation_eq_of_ne_zero (σ x : ℝ) (hσ : σ ≠ 0) :
    kimuraFixation σ x = (1 - Real.exp (-2 * σ * x)) / (1 - Real.exp (-2 * σ)) := by
  simp [kimuraFixation, hσ]

/-- Atlas's `kimuraSlope` has the closed form the core lemmas assume (definition unfolding). -/
theorem kimuraSlope_eq_of_ne_zero (σ : ℝ) (hσ : σ ≠ 0) :
    kimuraSlope σ = 2 * σ / (1 - Real.exp (-2 * σ)) := by
  simp [kimuraSlope, hσ]

/-- (i) `M u_α(1/M) → kimuraSlope α` at fixed `α`. -/
theorem tendsto_natCast_mul_kimuraFixation_one_div (α : ℝ) :
    Tendsto (fun M : ℕ => (M : ℝ) * kimuraFixation α (1 / (M : ℝ))) atTop
      (𝓝 (kimuraSlope α)) :=
  tendsto_natCast_mul_one_div_of_kimuraForm kimuraFixation kimuraSlope kimuraFixation_eq_of_ne_zero
    kimuraFixation_neutral kimuraSlope_eq_of_ne_zero (by simp [kimuraSlope]) α

/-- (ii) `kimuraSlope α ~ 2α` as `α → ∞`. -/
theorem kimuraSlope_isEquivalent_two_mul :
    Asymptotics.IsEquivalent atTop kimuraSlope (fun α => 2 * α) :=
  isEquivalent_two_mul_of_kimuraSlopeForm kimuraSlope kimuraSlope_eq_of_ne_zero

/-- (ii) Haldane's `2s` in the joint regime `s_M → 0`, `M s_M → ∞`. -/
theorem tendsto_kimuraFixation_div_two_mul {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hMs : Tendsto (fun M : ℕ => (M : ℝ) * s M) atTop atTop) :
    Tendsto (fun M : ℕ => kimuraFixation ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M)) atTop
      (𝓝 1) :=
  tendsto_div_two_mul_of_kimuraForm kimuraFixation kimuraFixation_eq_of_ne_zero s hs hMs

/-- (ii) "only when": Haldane's `2s` forces `s_M → 0` and `M s_M → ∞`. -/
theorem tendsto_zero_and_tendsto_atTop_of_tendsto_kimuraFixation_div {s : ℕ → ℝ}
    (h : Tendsto (fun M : ℕ => kimuraFixation ((M : ℝ) * s M) (1 / (M : ℝ)) / (2 * s M))
      atTop (𝓝 1)) :
    Tendsto s atTop (𝓝 0) ∧ Tendsto (fun M : ℕ => (M : ℝ) * s M) atTop atTop :=
  tendsto_zero_and_tendsto_atTop_of_kimuraForm kimuraFixation kimuraFixation_eq_of_ne_zero s h

/-- (iii) fixed `s > 0`: `u_{Ms}(1/M) → 1 - e^{-2s}`, and `1 - e^{-2s} < 2s`. -/
theorem tendsto_kimuraFixation_natCast_mul_one_div {s : ℝ} (hs : 0 < s) :
    Tendsto (fun M : ℕ => kimuraFixation ((M : ℝ) * s) (1 / (M : ℝ))) atTop
      (𝓝 (1 - Real.exp (-2 * s))) ∧ 1 - Real.exp (-2 * s) < 2 * s :=
  tendsto_one_sub_exp_of_kimuraForm kimuraFixation kimuraFixation_eq_of_ne_zero hs

end MathlibExt.Biology.PopulationGenetics.Diffusion
