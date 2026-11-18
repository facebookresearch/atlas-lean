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
public import MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion

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

/-- **Distinct-rate central derivative.** The central amount
has derivative `F * ka * Ag - k * Ac`. -/
theorem central_hasDerivAt_distinct {F D ka k t : ℝ} (h : ka ≠ k) :
    HasDerivAt (centralAmount F D ka k)
      (F * ka * depotAmount D ka t - k * centralAmount F D ka k t) t := by
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
  have hne : ka - k ≠ 0 := sub_ne_zero.mpr h
  have hval : (((F * D * ka) * (Real.exp (-k * t) * (-k * 1) - Real.exp (-ka * t) * (-ka * 1))) / (ka - k)) =
      F * ka * depotAmount D ka t - k * centralAmount F D ka k t := by
    simp only [depotAmount, centralAmount]
    field_simp
    ring
  rwa [hval] at hmain

/-- **Distinct-rate central equation.** The central amount
solves `Ac' = F * ka * Ag - k * Ac`. -/
theorem central_deriv_distinct {F D ka k t : ℝ} (h : ka ≠ k) :
    deriv (centralAmount F D ka k) t =
      F * ka * depotAmount D ka t - k * centralAmount F D ka k t :=
  (central_hasDerivAt_distinct h).deriv

/-- **Distinct-rate initial value.** -/
theorem central_zero (F D ka k : ℝ) : centralAmount F D ka k 0 = 0 := by
  simp [centralAmount]

/-- **Equal-rate central derivative.** -/
theorem central_hasDerivAt_equal {F D ka t : ℝ} :
    HasDerivAt (centralAmountEqual F D ka)
      (F * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t) t := by
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
  have hval : ((F * D * ka) * 1 * Real.exp (-ka * t) + (F * D * ka) * t * (Real.exp (-ka * t) * (-ka * 1))) =
      F * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t := by
    simp only [depotAmount, centralAmountEqual]
    ring
  rwa [hval] at hmain

/-- **Equal-rate central equation.** -/
theorem central_deriv_equal {F D ka t : ℝ} :
    deriv (centralAmountEqual F D ka) t =
      F * ka * depotAmount D ka t - ka * centralAmountEqual F D ka t :=
  central_hasDerivAt_equal.deriv

/-- **Distinct-rate nonnegativity.** For admissible parameters
and `t ≥ 0`, the central amount is nonnegative. -/
theorem central_nonneg {F D ka k t : ℝ} (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hka : 0 < ka) (hk : 0 ≤ k) (ht : 0 ≤ t) (h : ka ≠ k) :
    0 ≤ centralAmount F D ka k t := by
  have hC : 0 ≤ F * D * ka := mul_nonneg (mul_nonneg hF hD) hka.le
  show 0 ≤ F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)
  exact MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion.decay_expansion_nonneg
    hC hka.le hk ht h

/-- **Equal-rate nonnegativity.** For admissible parameters and
`t ≥ 0`, the equal-rate central amount is nonnegative. -/
theorem centralEqual_nonneg {F D ka t : ℝ} (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hka : 0 ≤ ka) (ht : 0 ≤ t) :
    0 ≤ centralAmountEqual F D ka t := by
  have hC : 0 ≤ F * D * ka := mul_nonneg (mul_nonneg hF hD) hka
  show 0 ≤ F * D * ka * t * Real.exp (-ka * t)
  exact MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion.decay_equal_rate_nonneg
    hC hka ht

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model
