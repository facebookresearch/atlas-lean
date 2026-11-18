/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import MathlibExt.Biology.Biophysics.CompartmentKinetics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Oral absorption budget

The administered-depot budget: total amount change splits into
the absorption loss `(1 - F)` and central elimination, in both
derivative and integrated forms.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

/-- The administered depot amount, as the canonical bolus
amount `amount ka 0 D t`. -/
noncomputable def depotAmount (D ka t : ℝ) : ℝ :=
  MathlibExt.Biology.Biophysics.CompartmentKinetics.amount ka 0 D t

/-- The depot amount in exponential form. -/
lemma depotAmount_eq_exp (D ka t : ℝ) :
    depotAmount D ka t = D * Real.exp (-ka * t) :=
  MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus ka D t

/-- The distinct-rate central amount formula. -/
noncomputable def centralAmountDistinct (F D ka k t : ℝ) : ℝ :=
  F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)

/-- The equal-rate central amount formula. -/
noncomputable def centralAmountEqual (F D ka t : ℝ) : ℝ :=
  F * D * ka * t * Real.exp (-ka * t)

/-- Derivative of the depot amount. -/
theorem hasDerivAt_depotAmount (D ka s : ℝ) :
    HasDerivAt (fun t => depotAmount D ka t) (-ka * depotAmount D ka s) s := by
  have h1 : HasDerivAt (fun t : ℝ => -ka * t) (-ka * 1) s :=
    (hasDerivAt_id' s).const_mul (-ka)
  have h3 := h1.exp.const_mul D
  have hval : D * (Real.exp (-ka * s) * (-ka * 1)) = -ka * (D * Real.exp (-ka * s)) := by
    ring
  simp only [depotAmount_eq_exp]
  rwa [hval] at h3

/-- Derivative of the central amount. -/
theorem hasDerivAt_centralAmountDistinct (F D ka k s : ℝ) :
    HasDerivAt (fun t => centralAmountDistinct F D ka k t)
      ((F * D * ka) * (Real.exp (-k * s) * (-k * 1) - Real.exp (-ka * s) * (-ka * 1)) /
        (ka - k)) s := by
  have e1 : HasDerivAt (fun t : ℝ => Real.exp (-k * t)) (Real.exp (-k * s) * (-k * 1)) s :=
    ((hasDerivAt_id' s).const_mul (-k)).exp
  have e2 : HasDerivAt (fun t : ℝ => Real.exp (-ka * t)) (Real.exp (-ka * s) * (-ka * 1)) s :=
    ((hasDerivAt_id' s).const_mul (-ka)).exp
  have hdiv := (e1.sub e2).const_mul (F * D * ka) |>.div_const (ka - k)
  unfold centralAmountDistinct
  exact hdiv

/-- Derivative of the total amount. -/
theorem hasDerivAt_totalAmount {F D ka k s : ℝ} (h : ka ≠ k) :
    HasDerivAt (fun t => depotAmount D ka t + centralAmountDistinct F D ka k t)
      (-(1 - F) * ka * depotAmount D ka s - k * centralAmountDistinct F D ka k s) s := by
  have htot := (hasDerivAt_depotAmount D ka s).add (hasDerivAt_centralAmountDistinct F D ka k s)
  have hk : ka - k ≠ 0 := sub_ne_zero.mpr h
  have hval : (-ka * depotAmount D ka s) +
        ((F * D * ka) * (Real.exp (-k * s) * (-k * 1) - Real.exp (-ka * s) * (-ka * 1)) /
          (ka - k))
      = (-(1 - F) * ka * depotAmount D ka s - k * centralAmountDistinct F D ka k s) := by
    simp only [depotAmount_eq_exp, centralAmountDistinct]
    field_simp
    ring
  rw [hval] at htot
  exact htot

/-- **Budget derivative.** The total amount derivative is the
absorption loss `-(1 - F) * ka * Ag` plus central elimination
`-k * Ac`. -/
theorem budget_deriv {F D ka k t : ℝ} (h : ka ≠ k) :
    deriv (fun t => depotAmount D ka t + centralAmountDistinct F D ka k t) t =
      -(1 - F) * ka * depotAmount D ka t - k * centralAmountDistinct F D ka k t := by
  exact (hasDerivAt_totalAmount h).deriv

/-- **Integrated budget.** The finite-interval change in total
amount equals the integral of the two loss terms. -/
theorem budget_integral {F D ka k t : ℝ} (h : ka ≠ k) :
    (∫ s in (0:ℝ)..t, (-(1 - F) * ka * depotAmount D ka s -
      k * centralAmountDistinct F D ka k s)) =
      (depotAmount D ka t + centralAmountDistinct F D ka k t) -
        (depotAmount D ka 0 + centralAmountDistinct F D ka k 0) := by
  have hderiv : deriv (fun t => depotAmount D ka t + centralAmountDistinct F D ka k t) =
      (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmountDistinct F D ka k s) := by
    funext s
    exact (hasDerivAt_totalAmount h).deriv
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) t, DifferentiableAt ℝ
      (fun t => depotAmount D ka t + centralAmountDistinct F D ka k t) x := by
    intro x _
    exact (hasDerivAt_totalAmount h).differentiableAt
  have hcont : ContinuousOn
      (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmountDistinct F D ka k s)
      (Set.uIcc (0:ℝ) t) := by
    have e1 : Continuous (fun s : ℝ => Real.exp (-k * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have e2 : Continuous (fun s : ℝ => Real.exp (-ka * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hAg : Continuous (fun s : ℝ => depotAmount D ka s) := by
      simp only [depotAmount_eq_exp]
      exact continuous_const.mul e2
    have hAc : Continuous (fun s : ℝ => centralAmountDistinct F D ka k s) := by
      unfold centralAmountDistinct
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        (e1.sub e2)).div continuous_const (fun _ => sub_ne_zero.mpr h)
    have htot : Continuous
        (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmountDistinct F D ka k s) :=
      ((continuous_const.mul continuous_const).mul hAg).sub (continuous_const.mul hAc)
    exact htot.continuousOn
  exact integral_deriv_eq_sub' _ hderiv hdiff hcont

/-- **Full bioavailability bookkeeping.** At `F = 1` the
absorption-loss term vanishes from the budget derivative. -/
theorem budget_deriv_full {D ka k t : ℝ} (h : ka ≠ k) :
    deriv (fun t => depotAmount D ka t + centralAmountDistinct 1 D ka k t) t =
      -k * centralAmountDistinct 1 D ka k t := by
  have h1 := @budget_deriv 1 D ka k t h
  rw [h1]
  ring

/-- Derivative of the equal-rate central amount. -/
theorem hasDerivAt_centralAmountEqual (F D ka s : ℝ) :
    HasDerivAt (fun t => centralAmountEqual F D ka t)
      (F * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s) s := by
  have hlin : HasDerivAt (fun t => -ka * t) (-ka * 1) s :=
    HasDerivAt.const_mul (-ka) (hasDerivAt_id s)
  have hexp : HasDerivAt (fun t => Real.exp (-ka * t))
      (Real.exp (-ka * s) * (-ka * 1)) s :=
    HasDerivAt.exp hlin
  have hid : HasDerivAt (fun t => t) (1 : ℝ) s := hasDerivAt_id s
  have hC : HasDerivAt (fun t => (F * D * ka) * t) ((F * D * ka) * 1) s :=
    HasDerivAt.const_mul (F * D * ka) hid
  have hprod : HasDerivAt ((fun t => (F * D * ka) * t) * (fun t => Real.exp (-ka * t)))
      ((F * D * ka) * 1 * Real.exp (-ka * s) + (F * D * ka) * s * (Real.exp (-ka * s) * (-ka * 1))) s :=
    HasDerivAt.mul hC hexp
  have hval : ((F * D * ka) * 1 * Real.exp (-ka * s) + (F * D * ka) * s * (Real.exp (-ka * s) * (-ka * 1))) =
      F * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s := by
    simp only [depotAmount_eq_exp, centralAmountEqual]
    ring
  rwa [hval] at hprod

/-- **Equal-rate budget derivative.** At `ka = k` the total
amount derivative is the same absorption loss plus central
elimination at rate `ka`. -/
theorem budget_deriv_equal {F D ka t : ℝ} :
    deriv (fun t => depotAmount D ka t + centralAmountEqual F D ka t) t =
      -(1 - F) * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t := by
  have htot := (hasDerivAt_depotAmount D ka t).add (hasDerivAt_centralAmountEqual F D ka t)
  rw [← Pi.add_def, htot.deriv]
  ring

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget
