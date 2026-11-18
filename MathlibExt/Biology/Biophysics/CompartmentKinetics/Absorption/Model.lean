/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Oral absorption model

The depot and central amounts for first-order absorption, in
both the distinct-rate and equal-rate closed forms, with their
derivative equations and nonnegativity.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-- The administered depot amount `D * exp (-ka * t)`. -/
noncomputable def depotAmount (D ka t : ℝ) : ℝ := D * Real.exp (-ka * t)

/-- The central amount for distinct rates. -/
noncomputable def centralAmount (F D ka k t : ℝ) : ℝ :=
  F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)

/-- The central amount for equal rates. -/
noncomputable def centralAmountEqual (F D ka t : ℝ) : ℝ :=
  F * D * ka * t * Real.exp (-ka * t)

/-- **Depot derivative.** The depot decays at rate `ka`. -/
theorem depot_hasDerivAt (D ka t : ℝ) :
    HasDerivAt (depotAmount D ka) (-ka * depotAmount D ka t) t := by
  have hlin : HasDerivAt (fun t => -ka * t) (-ka * 1) t :=
    HasDerivAt.const_mul (-ka) (hasDerivAt_id t)
  have hexp : HasDerivAt (fun t => Real.exp (-ka * t))
      (Real.exp (-ka * t) * (-ka * 1)) t :=
    HasDerivAt.exp hlin
  have hmul : HasDerivAt (fun t => D * Real.exp (-ka * t))
      (D * (Real.exp (-ka * t) * (-ka * 1))) t :=
    HasDerivAt.const_mul D hexp
  have hval : D * (Real.exp (-ka * t) * (-ka * 1)) =
      -ka * depotAmount D ka t := by
    simp [depotAmount]
    ring
  rw [hval] at hmul
  exact hmul

/-- **Distinct-rate central equation.** The central amount
starts at zero and solves `Ac' = F * ka * Ag - k * Ac`. -/
theorem central_deriv_distinct {F D ka k t : ℝ} (h : ka ≠ k) :
    deriv (centralAmount F D ka k) t =
      F * ka * depotAmount D ka t - k * centralAmount F D ka k t := by
  have hlin_k : HasDerivAt (fun t => -k * t) (-k * 1) t :=
    HasDerivAt.const_mul (-k) (hasDerivAt_id t)
  have hlin_ka : HasDerivAt (fun t => -ka * t) (-ka * 1) t :=
    HasDerivAt.const_mul (-ka) (hasDerivAt_id t)
  have hexp_k : HasDerivAt (fun t => Real.exp (-k * t))
      (Real.exp (-k * t) * (-k * 1)) t :=
    HasDerivAt.exp hlin_k
  have hexp_ka : HasDerivAt (fun t => Real.exp (-ka * t))
      (Real.exp (-ka * t) * (-ka * 1)) t :=
    HasDerivAt.exp hlin_ka
  have hsub : HasDerivAt ((fun t => Real.exp (-k * t)) - (fun t => Real.exp (-ka * t)))
      (Real.exp (-k * t) * (-k * 1) - Real.exp (-ka * t) * (-ka * 1)) t :=
    HasDerivAt.sub hexp_k hexp_ka
  have hcm : HasDerivAt (fun y => (F * D * ka) * (((fun t => Real.exp (-k * t)) - (fun t => Real.exp (-ka * t))) y))
      ((F * D * ka) * (Real.exp (-k * t) * (-k * 1) - Real.exp (-ka * t) * (-ka * 1))) t :=
    HasDerivAt.const_mul (F * D * ka) hsub
  have hdiv : HasDerivAt (fun x => ((F * D * ka) * (((fun t => Real.exp (-k * t)) - (fun t => Real.exp (-ka * t))) x)) / (ka - k))
      (((F * D * ka) * (Real.exp (-k * t) * (-k * 1) - Real.exp (-ka * t) * (-ka * 1))) / (ka - k)) t :=
    HasDerivAt.div_const hcm (ka - k)
  have hmain : HasDerivAt (centralAmount F D ka k)
      (((F * D * ka) * (Real.exp (-k * t) * (-k * 1) - Real.exp (-ka * t) * (-ka * 1))) / (ka - k)) t :=
    hdiv
  rw [hmain.deriv]
  have hne : ka - k ≠ 0 := sub_ne_zero.mpr h
  simp only [depotAmount, centralAmount]
  field_simp
  ring

/-- **Distinct-rate initial value.** -/
theorem central_zero (F D ka k : ℝ) : centralAmount F D ka k 0 = 0 := by
  simp [centralAmount]

/-- **Equal-rate central equation.** -/
theorem central_deriv_equal {F D ka t : ℝ} :
    deriv (centralAmountEqual F D ka) t =
      F * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t := by
  have hlin : HasDerivAt (fun t => -ka * t) (-ka * 1) t :=
    HasDerivAt.const_mul (-ka) (hasDerivAt_id t)
  have hexp : HasDerivAt (fun t => Real.exp (-ka * t))
      (Real.exp (-ka * t) * (-ka * 1)) t :=
    HasDerivAt.exp hlin
  have hid : HasDerivAt (fun t => t) (1 : ℝ) t := hasDerivAt_id t
  have hC : HasDerivAt (fun t => (F * D * ka) * t) ((F * D * ka) * 1) t :=
    HasDerivAt.const_mul (F * D * ka) hid
  have hprod : HasDerivAt ((fun t => (F * D * ka) * t) * (fun t => Real.exp (-ka * t)))
      ((F * D * ka) * 1 * Real.exp (-ka * t) + (F * D * ka) * t * (Real.exp (-ka * t) * (-ka * 1))) t :=
    HasDerivAt.mul hC hexp
  have hmain : HasDerivAt (centralAmountEqual F D ka)
      ((F * D * ka) * 1 * Real.exp (-ka * t) + (F * D * ka) * t * (Real.exp (-ka * t) * (-ka * 1))) t :=
    hprod
  rw [hmain.deriv]
  simp only [depotAmount, centralAmountEqual]
  ring

/-- **Distinct-rate nonnegativity.** For admissible parameters
and `t ≥ 0`, the central amount is nonnegative. -/
theorem central_nonneg {F D ka k t : ℝ} (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hka : 0 < ka) (hk : 0 ≤ k) (ht : 0 ≤ t) (h : ka ≠ k) :
    0 ≤ centralAmount F D ka k t := by
  have hC : 0 ≤ F * D * ka := by positivity
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hdenom : ka - k ≤ 0 := sub_nonpos.mpr (le_of_lt hlt)
    have hkt : ka * t ≤ k * t := mul_le_mul_of_nonneg_right (le_of_lt hlt) ht
    have hle : -k * t ≤ -ka * t := by linarith
    have hexp : Real.exp (-k * t) ≤ Real.exp (-ka * t) := Real.exp_le_exp.mpr hle
    have hdiff : Real.exp (-k * t) - Real.exp (-ka * t) ≤ 0 := sub_nonpos.mpr hexp
    have hnum : F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hC hdiff
    show 0 ≤ F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)
    exact div_nonneg_of_nonpos hnum hdenom
  · have hdenom : 0 ≤ ka - k := sub_nonneg.mpr (le_of_lt hgt)
    have hkt : k * t ≤ ka * t := mul_le_mul_of_nonneg_right (le_of_lt hgt) ht
    have hle : -ka * t ≤ -k * t := by linarith
    have hexp : Real.exp (-ka * t) ≤ Real.exp (-k * t) := Real.exp_le_exp.mpr hle
    have hdiff : 0 ≤ Real.exp (-k * t) - Real.exp (-ka * t) := sub_nonneg.mpr hexp
    have hnum : 0 ≤ F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) :=
      mul_nonneg hC hdiff
    show 0 ≤ F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)
    exact div_nonneg hnum hdenom

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model
