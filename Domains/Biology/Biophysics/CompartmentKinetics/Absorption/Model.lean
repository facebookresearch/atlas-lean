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
public import Domains.Biology.Dynamics.FeedForwardLoop
public import Domains.Biology.Biophysics.CompartmentKinetics
public import Domains.Biology.Biophysics.CompartmentKinetics.DecayExpansion

/-!
# Oral absorption model

The depot and central amounts for first-order absorption, in
both the distinct-rate and equal-rate closed forms, with their
derivative equations and nonnegativity.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-- The administered depot amount `D * exp (-ka * t)`, defined for all real inputs; the intended
domain is `D ≥ 0`, `ka > 0` and `t ≥ 0`. -/
noncomputable def depotAmount (D ka t : ℝ) : ℝ := D * Real.exp (-ka * t)

/-- The central amount for distinct rates. With the convention `x / 0 = 0` it is `0` when `ka = k`,
where the equal-rate formula `centralAmountEqual` applies. The intended domain is `ka ≠ k` with
`0 ≤ F ≤ 1`, `D ≥ 0`, `ka > 0`, `k ≥ 0` and `t ≥ 0`. -/
noncomputable def centralAmount (F D ka k t : ℝ) : ℝ :=
  F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)

/-- The central amount for equal rates, defined for all real inputs; the intended domain is
`0 ≤ F ≤ 1`, `D ≥ 0`, `ka > 0` and `t ≥ 0`. -/
noncomputable def centralAmountEqual (F D ka t : ℝ) : ℝ :=
  F * D * ka * t * Real.exp (-ka * t)

/-- **Depot derivative.** For all real `D`, `ka` and `t`, the depot amount has derivative
`-ka * depotAmount D ka t` at `t`; for `ka > 0` the depot decays at rate `ka`. -/
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

/-- **Distinct-rate nonnegativity.** For `F ≥ 0`, `D ≥ 0`, `ka > 0`, `k ≥ 0` with `ka ≠ k`, and
`t ≥ 0`, the central amount is nonnegative. -/
theorem central_nonneg {F D ka k t : ℝ} (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hka : 0 < ka) (hk : 0 ≤ k) (ht : 0 ≤ t) (h : ka ≠ k) :
    0 ≤ centralAmount F D ka k t := by
  have hC : 0 ≤ F * D * ka := mul_nonneg (mul_nonneg hF hD) hka.le
  show 0 ≤ F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k)
  exact MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion.decay_expansion_nonneg
    hC hka.le hk ht h

/-- **Equal-rate nonnegativity.** For `F ≥ 0`, `D ≥ 0`, `ka ≥ 0` and `t ≥ 0`, the equal-rate central
amount is nonnegative. -/
theorem centralEqual_nonneg {F D ka t : ℝ} (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hka : 0 ≤ ka) (ht : 0 ≤ t) :
    0 ≤ centralAmountEqual F D ka t := by
  have hC : 0 ≤ F * D * ka := mul_nonneg (mul_nonneg hF hD) hka
  show 0 ≤ F * D * ka * t * Real.exp (-ka * t)
  exact MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion.decay_equal_rate_nonneg
    hC hka ht

/-- The depot amount as the canonical bolus amount. -/
lemma depotAmount_eq_amount (D ka t : ℝ) :
    depotAmount D ka t =
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount ka 0 D t := by
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus]
  rfl

/-- The canonical central amount: the relaxation solution with elimination rate `k` and input
`F * ka * Ag`, for all rates without a distinct-rate side condition (an oriented integral for
`t < 0`). The intended domain is `0 ≤ F ≤ 1`, `D ≥ 0`, `ka > 0`, `k ≥ 0` and `t ≥ 0`. -/
noncomputable def centralAmountCanonical (F D ka k t : ℝ) : ℝ :=
  MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation k
    (fun s => F * ka * depotAmount D ka s) 0 t

/-- The canonical central amount solves the central equation. -/
theorem hasDerivAt_centralAmountCanonical (F D ka k s : ℝ) :
    HasDerivAt (fun t => centralAmountCanonical F D ka k t)
      (F * ka * depotAmount D ka s - k * centralAmountCanonical F D ka k s) s := by
  have hcont : Continuous (fun s : ℝ => depotAmount D ka s) := by
    unfold depotAmount
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h := MathlibExt.Biology.Dynamics.FeedForwardLoop.hasDerivAt_relaxation
    (α := k) (P := fun s => F * ka * depotAmount D ka s) (t := s) 0
    (fun a b => (hcont.continuousOn).intervalIntegrable.const_mul _)
    ((hcont.continuousAt (x := s)).const_mul _)
  have h2 : centralAmountCanonical F D ka k =
      MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation k
        (fun s => F * ka * depotAmount D ka s) 0 := rfl
  rw [h2]
  exact h

/-- The canonical central amount starts at zero. -/
theorem centralAmountCanonical_zero (F D ka k : ℝ) :
    centralAmountCanonical F D ka k 0 = 0 := by
  unfold centralAmountCanonical MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation
  simp [intervalIntegral.integral_same]

/-- Solutions of the central equation from zero agree with the
canonical amount: the exponential-factor difference has
derivative zero. -/
theorem centralAmountCanonical_eq_of_forall_hasDerivAt {F D ka k : ℝ} {y : ℝ → ℝ}
    (hy : ∀ t, HasDerivAt y (F * ka * depotAmount D ka t - k * y t) t)
    (hy0 : y 0 = 0) (t : ℝ) :
    centralAmountCanonical F D ka k t = y t := by
  have hdiff : ∀ s, HasDerivAt (fun u => centralAmountCanonical F D ka k u - y u)
      (-k * (centralAmountCanonical F D ka k s - y s)) s := by
    intro s
    have h := (hasDerivAt_centralAmountCanonical F D ka k s).sub (hy s)
    convert h using 1
    ring
  have hw : ∀ s, HasDerivAt (fun u => Real.exp (k * u) *
      (centralAmountCanonical F D ka k u - y u)) 0 s := by
    intro s
    have hexp : HasDerivAt (fun u => Real.exp (k * u)) (k * Real.exp (k * s)) s := by
      have h1 : HasDerivAt (fun u : ℝ => k * u) (k * 1) s :=
        HasDerivAt.const_mul k (hasDerivAt_id s)
      have h2 := HasDerivAt.exp h1
      convert h2 using 1
      ring
    have h := hexp.mul (hdiff s)
    convert h using 1
    ring
  have hconst : ∀ a b : ℝ, Real.exp (k * a) * (centralAmountCanonical F D ka k a - y a) =
      Real.exp (k * b) * (centralAmountCanonical F D ka k b - y b) :=
    is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt)
      (fun s => (hw s).deriv)
  have h0 := hconst t 0
  rw [centralAmountCanonical_zero, hy0] at h0
  simp only [sub_zero, mul_zero] at h0
  have hsub : centralAmountCanonical F D ka k t - y t = 0 := by
    rcases mul_eq_zero.mp h0 with he | hd
    · exact absurd he (Real.exp_ne_zero _)
    · exact hd
  linarith [hsub]

/-- **Distinct-rate formula.** The canonical central amount is
the distinct-rate closed form when `ka ≠ k`. -/
theorem centralAmountCanonical_eq_distinct {F D ka k : ℝ} (h : ka ≠ k) (t : ℝ) :
    centralAmountCanonical F D ka k t = centralAmount F D ka k t :=
  centralAmountCanonical_eq_of_forall_hasDerivAt (fun s => central_hasDerivAt_distinct h)
    (central_zero F D ka k) t

/-- **Equal-rate formula.** The canonical central amount is
the equal-rate closed form when the rates agree. -/
theorem centralAmountCanonical_eq_equal {F D ka : ℝ} (t : ℝ) :
    centralAmountCanonical F D ka ka t = centralAmountEqual F D ka t :=
  centralAmountCanonical_eq_of_forall_hasDerivAt (fun s => central_hasDerivAt_equal)
    (by simp [centralAmountEqual]) t

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model
