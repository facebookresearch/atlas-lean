/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.OptionPayoffs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Deductible, limit and coinsurance as a capped call spread

For a nonnegative loss and deductible, a layer of width `L ≥ 0` attaches at loss `d` and is
exhausted at loss `d + L`. The width caps the excess loss **before** the share `ρ ∈ [0, 1]`
is applied, so the largest ceded payment is `ρ * L`.
Subtracting the call at exhaustion from the call at attachment accounts for exactly the
portion inside the layer. Integrating this pointwise identity gives the expected payment;
it does not price the contract.

## References

* R. Kaas, M. Goovaerts, J. Dhaene and M. Denuit, *Modern Actuarial Risk Theory*,
  2nd ed., Springer, 2008. The companion
  [cheatsheet](https://www1feb-uva.nl/ke/act/people/kaas/Recap123456.pdf)
  (© 2011 R. Kaas and J. Dhaene), sheet 1, “Stop-loss premiums”, defines the stop-loss
  transform `π(t) = E[(S - t)⁺]`. The capped spread and its expectation below are deductions.
-/

@[expose] public section

namespace Domains.Economics.Actuarial

open MathlibExt.Probability.Finance.OptionPayoffs MeasureTheory

/-- The loss ceded at loss `s`: apply the deductible `d`, cap the excess at width `L`,
then cede a share `ρ` of that layer. -/
noncomputable def cededLoss (d L ρ s : ℝ) : ℝ :=
  ρ * min (europeanCallPayoff s d) L

/-- The part of the loss not ceded to the layer. -/
noncomputable def retainedLoss (d L ρ s : ℝ) : ℝ := s - cededLoss d L ρ s

/-- For any real loss `s`, deductible `d`, share `ρ` and width `L ≥ 0`, the ceded loss equals
`ρ * ((s - d)⁺ - (s - (d + L))⁺)`: a long call at `d` and a short call at `d + L`,
both scaled by `ρ`. -/
theorem cededLoss_eq_callSpread (d : ℝ) {L : ℝ} (hL : 0 ≤ L) (ρ s : ℝ) :
    cededLoss d L ρ s = ρ * (europeanCallPayoff s d - europeanCallPayoff s (d + L)) := by
  unfold cededLoss europeanCallPayoff
  congr 1
  grind

/-- For a nonnegative loss and deductible, a nonnegative layer width and a share in `[0, 1]`,
the payment is nonnegative and bounded by both the whole loss and `ρ * L`. -/
theorem cededLoss_bounds {d L ρ s : ℝ} (hd : 0 ≤ d) (hL : 0 ≤ L) (hρ₀ : 0 ≤ ρ)
    (hρ₁ : ρ ≤ 1) (hs : 0 ≤ s) :
    0 ≤ cededLoss d L ρ s ∧ cededLoss d L ρ s ≤ min s (ρ * L) := by
  have h := le_min (europeanCallPayoff_nonneg s d) hL
  have hcall : europeanCallPayoff s d ≤ s := max_le (sub_le_self _ hd) hs
  refine ⟨mul_nonneg hρ₀ h, le_min ?_ (mul_le_mul_of_nonneg_left (min_le_right _ _) hρ₀)⟩
  calc
    cededLoss d L ρ s ≤ min (europeanCallPayoff s d) L := mul_le_of_le_one_left h hρ₁
    _ ≤ europeanCallPayoff s d := min_le_left _ _
    _ ≤ s := hcall

/-- If the loss `s`, deductible `d` and width `L` are nonnegative and the share `ρ ∈ [0, 1]`,
then the retained loss `s - ρ * min ((s - d)⁺) L` is nonnegative. -/
theorem retainedLoss_nonneg {d L ρ s : ℝ} (hd : 0 ≤ d) (hL : 0 ≤ L) (hρ₀ : 0 ≤ ρ)
    (hρ₁ : ρ ≤ 1) (hs : 0 ≤ s) : 0 ≤ retainedLoss d L ρ s :=
  sub_nonneg.mpr ((cededLoss_bounds hd hL hρ₀ hρ₁ hs).2.trans (min_le_left _ _))

/-- Retained and ceded losses account for the entire loss, without double counting. -/
theorem retainedLoss_add_cededLoss (d L ρ s : ℝ) :
    retainedLoss d L ρ s + cededLoss d L ρ s = s := sub_add_cancel _ _

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The stop-loss transform of `S` at retention `t`: the integral of its call payoff.
For an integrable loss under a probability measure this is the expected excess over `t`. -/
noncomputable def stopLossTransform (μ : Measure Ω) (S : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, europeanCallPayoff (S ω) t ∂μ

variable {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → ℝ}

/-- If `μ` is a finite measure and the real-valued loss `S` is integrable with respect to `μ`,
then for every real retention `t` the call payoff `ω ↦ (S ω - t)⁺` is integrable under `μ`. -/
theorem integrable_callPayoff (hS : Integrable S μ) (t : ℝ) :
    Integrable (fun ω ↦ europeanCallPayoff (S ω) t) μ :=
  (hS.sub (integrable_const t)).pos_part

/-- Let `S` be a real-valued loss integrable with respect to a finite measure `μ`.
For real `d` and `ρ` and width `L ≥ 0`, the layer payment
`ω ↦ ρ * min ((S ω - d)⁺) L` is integrable with respect to `μ`. -/
theorem integrable_cededLoss (hS : Integrable S μ) (d : ℝ) {L : ℝ} (hL : 0 ≤ L) (ρ : ℝ) :
    Integrable (fun ω ↦ cededLoss d L ρ (S ω)) μ := by
  simp only [cededLoss_eq_callSpread d hL]
  exact ((integrable_callPayoff hS d).sub (integrable_callPayoff hS (d + L))).const_mul ρ

/-- Let `S` be real-valued and integrable under a finite measure `μ`. For real `d` and `ρ`
and width `L ≥ 0`, write `π(t) = ∫ ω, (S ω - t)⁺ ∂μ`. Then
`∫ ω, cededLoss d L ρ (S ω) ∂μ = ρ * (π(d) - π(d + L))`.
When `μ` is a probability measure, this is the expected ceded payment. -/
theorem integral_cededLoss (hS : Integrable S μ) (d : ℝ) {L : ℝ} (hL : 0 ≤ L) (ρ : ℝ) :
    ∫ ω, cededLoss d L ρ (S ω) ∂μ =
      ρ * (stopLossTransform μ S d - stopLossTransform μ S (d + L)) := by
  simp only [cededLoss_eq_callSpread d hL, stopLossTransform, integral_const_mul,
    integral_sub (integrable_callPayoff hS d) (integrable_callPayoff hS (d + L))]

end Domains.Economics.Actuarial
