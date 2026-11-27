/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import PhyslibExt.Engineering.Process.CSTR

import Mathlib.Tactic.Ring

/-!
# Step response of an ideal stirred tank

For an initially tracer-free, perfectly mixed tank, the conservative step response normalized by
its inlet concentration is the exponential CDF. Positive linear loss makes this normalization
converge to less than one instead.
-/

public section

open Engineering.Process.CSTR Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Chemistry.Transport

private lemma normalized_solution_eq {V Q k cin : ℝ} (hcin : cin ≠ 0) (t : ℝ) :
    solution V Q k cin 0 t / cin =
      Q / (Q + k * V) * (1 - Real.exp (-((Q / V + k) * t))) := by
  calc
    _ = cin * (Q / (Q + k * V)) * (1 - Real.exp (-(Q / V + k) * t)) / cin := by
      rw [solution_eq, ← mul_div_assoc cin Q, mul_comm cin Q]
      congr 1
      ring
    _ = _ := by rw [mul_assoc, mul_div_cancel_left₀ _ hcin, neg_mul]

/-- In the ideal well-mixed model with fixed volume `V`, flow `Q` and positive step inlet
concentration `cin`, extend the normalized response of an initially tracer-free tank by zero to
negative times. Without loss, it is the CDF of the exponential probability measure of rate `Q / V`.
This PDF representative agrees with the derivative for positive times and with the right
derivative at zero. The CDF is not two-sided differentiable at zero. With positive linear loss
`k`, the inlet-normalized response tends to `Q / (Q + k * V) < 1` and is not a probability CDF.

Section 8.2.3 of Rawlings and Ekerdt's *Chemical Reactor Analysis and Design Fundamentals* gives
the conservative step response and its residence-time interpretation. The endpoint and loss
conclusions are deductions here. -/
theorem stirredTankStepResponse {V Q cin : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hcin : 0 < cin) :
    let r := Q / V
    let response : ℝ → ℝ → ℝ := fun k t ↦ if 0 ≤ t then solution V Q k cin 0 t / cin else 0
    IsProbabilityMeasure (expMeasure r) ∧
      response 0 = (cdf (expMeasure r) : ℝ → ℝ) ∧
      (∀ t, exponentialPDFReal r t = if 0 ≤ t then r * Real.exp (-(r * t)) else 0) ∧
      (∀ t, 0 < t → HasDerivAt (response 0) (exponentialPDFReal r t) t) ∧
      HasDerivWithinAt (response 0) (exponentialPDFReal r 0) (Ici 0) 0 ∧
      ¬ DifferentiableAt ℝ (response 0) 0 ∧
      ∀ k : ℝ, 0 < k →
        Tendsto (response k) atTop (𝓝 (Q / (Q + k * V))) ∧ Q / (Q + k * V) < 1 ∧
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], response k ≠ (cdf μ : ℝ → ℝ) := by
  intro r response
  have hr : 0 < r := div_pos hQ hV
  have hconservative (t : ℝ) (ht : 0 ≤ t) : response 0 t = 1 - Real.exp (-(r * t)) := by
    change (if 0 ≤ t then solution V Q 0 cin 0 t / cin else 0) = _
    rw [ite_eq_left ht, normalized_solution_eq hcin.ne']
    simp [r, hQ.ne']
  have hcdf : response 0 = (cdf (expMeasure r) : ℝ → ℝ) := by
    ext t
    rw [cdf_expMeasure_eq hr]
    by_cases ht : 0 ≤ t
    · rw [ite_eq_left ht, hconservative t ht]
    · simp [response, ht]
  have hpdf (t : ℝ) :
      exponentialPDFReal r t = if 0 ≤ t then r * Real.exp (-(r * t)) else 0 := by
    simp [exponentialPDFReal, gammaPDFReal]
  have hbranch (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun s ↦ 1 - Real.exp (-(r * s))) (exponentialPDFReal r t) t := by
    rw [hpdf, ite_eq_left ht]
    simpa only [sub_eq_add_neg] using
      (hasDerivAt_neg_exp_mul_exp (r := r) (x := t)).const_add 1
  have hright : HasDerivWithinAt (response 0) (exponentialPDFReal r 0) (Ici 0) 0 :=
    (hbranch 0 le_rfl).hasDerivWithinAt.congr_of_mem hconservative le_rfl
  refine ⟨isProbabilityMeasure_expMeasure hr, hcdf, hpdf, ?_, hright, ?_, ?_⟩
  · intro t ht
    apply (hbranch t ht.le).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hconservative s hs.le
  · have hleft : HasDerivWithinAt (response 0) 0 (Iic 0) 0 := by
      apply (hasDerivWithinAt_const 0 (Iic 0) (0 : ℝ)).congr_of_mem _ le_rfl
      intro t ht
      rcases lt_or_eq_of_le (mem_Iic.mp ht) with ht | rfl
      · simp [response, ht.not_ge]
      · simp [hconservative 0 le_rfl]
    intro hdiff
    have h₁ := hleft.derivWithin (uniqueDiffWithinAt_Iic 0)
    have h₂ := hright.derivWithin (uniqueDiffWithinAt_Ici 0)
    rw [hdiff.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 0)] at h₁
    rw [hdiff.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)] at h₂
    have hzero : exponentialPDFReal r 0 = 0 := h₂.symm.trans h₁
    exact hr.ne' (by simpa [hpdf] using hzero)
  · intro k hk
    have harg : Tendsto (fun t : ℝ ↦ -((r + k) * t)) atTop atBot := by
      refine tendsto_atBot.2 fun b ↦ ?_
      filter_upwards [eventually_ge_atTop (-b / (r + k))] with t ht
      rw [mul_comm (r + k) t]
      exact neg_le.mp ((div_le_iff₀ (add_pos hr hk)).mp ht)
    have hexp := Real.tendsto_exp_atBot.comp harg
    have hlim : Tendsto (response k) atTop (𝓝 (Q / (Q + k * V))) := by
      have hmodel := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul (Q / (Q + k * V))
      simp only [sub_zero, mul_one] at hmodel
      refine hmodel.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      change _ = if 0 ≤ t then solution V Q k cin 0 t / cin else 0
      rw [ite_eq_left ht, normalized_solution_eq hcin.ne']
      rfl
    have hlt : Q / (Q + k * V) < 1 :=
      (div_lt_one (add_pos hQ (mul_pos hk hV))).2 (lt_add_of_pos_right Q (mul_pos hk hV))
    refine ⟨hlim, hlt, ?_⟩
    intro μ _ heq
    rw [heq] at hlim
    exact hlt.ne (tendsto_nhds_unique hlim (tendsto_cdf_atTop μ))

end Chemistry.Transport
