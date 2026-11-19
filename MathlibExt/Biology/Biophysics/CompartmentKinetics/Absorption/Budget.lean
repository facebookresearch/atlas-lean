/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-!
# Oral absorption budget

The administered-depot budget over the shared absorption model:
total amount change splits into the absorption loss `(1 - F)`
and central elimination, in derivative and integrated forms,
for distinct rates, equal rates, and the canonical amount.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-- Derivative of the distinct-rate total amount. -/
theorem hasDerivAt_totalAmount {F D ka k s : ℝ} (h : ka ≠ k) :
    HasDerivAt (fun t => depotAmount D ka t + centralAmount F D ka k t)
      (-(1 - F) * ka * depotAmount D ka s - k * centralAmount F D ka k s) s := by
  have htot := (depot_hasDerivAt D ka s).add (central_hasDerivAt_distinct (F := F) (D := D) (t := s) h)
  convert htot using 1
  ring

/-- **Budget derivative.** The total amount derivative is the
absorption loss `-(1 - F) * ka * Ag` plus central elimination
`-k * Ac`. -/
theorem budget_deriv {F D ka k t : ℝ} (h : ka ≠ k) :
    deriv (fun t => depotAmount D ka t + centralAmount F D ka k t) t =
      -(1 - F) * ka * depotAmount D ka t - k * centralAmount F D ka k t :=
  (hasDerivAt_totalAmount h).deriv

/-- **Integrated budget.** The finite-interval change in total
amount equals the integral of the two loss terms. -/
theorem budget_integral {F D ka k t : ℝ} (h : ka ≠ k) :
    (∫ s in (0:ℝ)..t, (-(1 - F) * ka * depotAmount D ka s -
      k * centralAmount F D ka k s)) =
      (depotAmount D ka t + centralAmount F D ka k t) -
        (depotAmount D ka 0 + centralAmount F D ka k 0) := by
  have hderiv : deriv (fun t => depotAmount D ka t + centralAmount F D ka k t) =
      (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmount F D ka k s) := by
    funext s
    exact (hasDerivAt_totalAmount h).deriv
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) t, DifferentiableAt ℝ
      (fun t => depotAmount D ka t + centralAmount F D ka k t) x := by
    intro x _
    exact (hasDerivAt_totalAmount h).differentiableAt
  have hcont : ContinuousOn
      (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmount F D ka k s)
      (Set.uIcc (0:ℝ) t) := by
    have e1 : Continuous (fun s : ℝ => Real.exp (-k * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have e2 : Continuous (fun s : ℝ => Real.exp (-ka * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hAg : Continuous (fun s : ℝ => depotAmount D ka s) := by
      unfold depotAmount
      exact continuous_const.mul e2
    have hAc : Continuous (fun s : ℝ => centralAmount F D ka k s) := by
      unfold centralAmount
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        (e1.sub e2)).div continuous_const (fun _ => sub_ne_zero.mpr h)
    have htot : Continuous
        (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmount F D ka k s) :=
      ((continuous_const.mul continuous_const).mul hAg).sub (continuous_const.mul hAc)
    exact htot.continuousOn
  exact integral_deriv_eq_sub' _ hderiv hdiff hcont

/-- **Full bioavailability bookkeeping.** At `F = 1` the
absorption-loss term vanishes from the budget derivative. -/
theorem budget_deriv_full {D ka k t : ℝ} (h : ka ≠ k) :
    deriv (fun t => depotAmount D ka t + centralAmount 1 D ka k t) t =
      -k * centralAmount 1 D ka k t := by
  have h1 := @budget_deriv 1 D ka k t h
  rw [h1]
  ring

/-- Derivative of the equal-rate total amount. -/
theorem hasDerivAt_totalAmountEqual {F D ka s : ℝ} :
    HasDerivAt (fun t => depotAmount D ka t + centralAmountEqual F D ka t)
      (-(1 - F) * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s) s := by
  have htot := (depot_hasDerivAt D ka s).add (central_hasDerivAt_equal (F := F) (D := D) (ka := ka) (t := s))
  convert htot using 1
  ring

/-- **Equal-rate budget derivative.** -/
theorem budget_deriv_equal {F D ka t : ℝ} :
    deriv (fun t => depotAmount D ka t + centralAmountEqual F D ka t) t =
      -(1 - F) * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t :=
  hasDerivAt_totalAmountEqual.deriv

/-- **Equal-rate integrated budget.** -/
theorem budget_integral_equal {F D ka t : ℝ} :
    (∫ s in (0:ℝ)..t, (-(1 - F) * ka * depotAmount D ka s -
      ka * centralAmountEqual F D ka s)) =
      (depotAmount D ka t + centralAmountEqual F D ka t) -
        (depotAmount D ka 0 + centralAmountEqual F D ka 0) := by
  have hderiv : deriv (fun t => depotAmount D ka t + centralAmountEqual F D ka t) =
      (fun s => -(1 - F) * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s) := by
    funext s
    exact hasDerivAt_totalAmountEqual.deriv
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) t, DifferentiableAt ℝ
      (fun t => depotAmount D ka t + centralAmountEqual F D ka t) x := by
    intro x _
    exact hasDerivAt_totalAmountEqual.differentiableAt
  have hcont : ContinuousOn
      (fun s => -(1 - F) * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s)
      (Set.uIcc (0:ℝ) t) := by
    have e2 : Continuous (fun s : ℝ => Real.exp (-ka * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hAg : Continuous (fun s : ℝ => depotAmount D ka s) := by
      unfold depotAmount
      exact continuous_const.mul e2
    have hAc : Continuous (fun s : ℝ => centralAmountEqual F D ka s) := by
      unfold centralAmountEqual
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        continuous_id).mul e2
    have htot : Continuous
        (fun s => -(1 - F) * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s) :=
      ((continuous_const.mul continuous_const).mul hAg).sub (continuous_const.mul hAc)
    exact htot.continuousOn
  exact integral_deriv_eq_sub' _ hderiv hdiff hcont

/-- **Canonical budget derivative.** Against the canonical
central amount the budget holds at all rates. -/
theorem budget_deriv_canonical {F D ka k t : ℝ} :
    deriv (fun t => depotAmount D ka t + centralAmountCanonical F D ka k t) t =
      -(1 - F) * ka * depotAmount D ka t - k * centralAmountCanonical F D ka k t := by
  have htot := (depot_hasDerivAt D ka t).add (hasDerivAt_centralAmountCanonical F D ka k t)
  rw [← Pi.add_def, htot.deriv]
  ring

/-- **Canonical integrated budget.** -/
theorem budget_integral_canonical {F D ka k t : ℝ} :
    (∫ s in (0:ℝ)..t, (-(1 - F) * ka * depotAmount D ka s -
      k * centralAmountCanonical F D ka k s)) =
      (depotAmount D ka t + centralAmountCanonical F D ka k t) -
        (depotAmount D ka 0 + centralAmountCanonical F D ka k 0) := by
  rcases eq_or_ne ka k with rfl | h
  · have hInt : (fun s => -(1 - F) * ka * depotAmount D ka s - ka * centralAmountCanonical F D ka ka s) =
        (fun s => -(1 - F) * ka * depotAmount D ka s - ka * centralAmountEqual F D ka s) := by
      funext s
      rw [centralAmountCanonical_eq_equal]
    rw [hInt, centralAmountCanonical_eq_equal t, centralAmountCanonical_eq_equal 0]
    exact budget_integral_equal
  · have hInt : (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmountCanonical F D ka k s) =
        (fun s => -(1 - F) * ka * depotAmount D ka s - k * centralAmount F D ka k s) := by
      funext s
      rw [centralAmountCanonical_eq_distinct h]
    rw [hInt, centralAmountCanonical_eq_distinct h t, centralAmountCanonical_eq_distinct h 0]
    exact budget_integral h

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget
