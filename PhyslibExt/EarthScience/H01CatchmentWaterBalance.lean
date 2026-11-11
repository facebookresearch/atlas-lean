/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Linear-reservoir catchment: explicit storage, ODE, and closed water budget

## i. Overview

A linear reservoir with constant inflow `I` and recession coefficient `k > 0`
obeys `S' = I - k * S`. Its storage is the explicit profile
`S(t) = I / k + (S0 - I / k) * exp (-k * t)`, and the integrated budget
`S(t) - S0 = I * t - k * ∫₀ᵗ S` closes exactly. Storage is a volume,
`I` a volume per time, and a depth flux would be converted by area; no
empirical validation is claimed.

## ii. Key results

- `EarthScience.storage_initial`: the profile starts at `S0`.
- `EarthScience.hasDerivAt_storage_solution`: the profile satisfies `S' = I - k * S`.
- `EarthScience.integrated_water_budget`: the time integral of storage in closed
  form, and the storage change equals inflow minus `k` times that integral.

## iii. Table of contents

- A. Explicit profile and its derivative
- B. Integrated water budget

## iv. References

- `HasDerivAt.exp` and `HasDerivAt.const_mul` / `const_add` in Mathlib
  (derivative of the exponential profile).
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in Mathlib (FTC for the
  integrated budget).
-/

@[expose] public section

namespace EarthScience

/-- Storage at time `0` is the initial storage `S0`. -/
theorem storage_initial (I k S0 : ℝ) :
    (fun t => I / k + (S0 - I / k) * Real.exp (-k * t)) 0 = S0 := by
  simp only [mul_zero, Real.exp_zero, mul_one]
  ring

/-- The explicit profile `S(t) = I/k + (S0 - I/k) * exp (-k t)` satisfies
the linear-reservoir ODE `S' = I - k * S` at every time `t`. -/
theorem hasDerivAt_storage_solution {I k S0 : ℝ} (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun t => I / k + (S0 - I / k) * Real.exp (-k * t))
      (I - k * (I / k + (S0 - I / k) * Real.exp (-k * t))) t := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hlin : HasDerivAt (fun t : ℝ => -k * t) (-k) t := by
    simpa using (hasDerivAt_id t).const_mul (-k)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-k * t))
      (Real.exp (-k * t) * (-k)) t := hlin.exp
  have hmul : HasDerivAt (fun t : ℝ => (S0 - I / k) * Real.exp (-k * t))
      ((S0 - I / k) * (Real.exp (-k * t) * (-k))) t :=
    hexp.const_mul (S0 - I / k)
  have hfull : HasDerivAt (fun t : ℝ => I / k + (S0 - I / k) * Real.exp (-k * t))
      ((S0 - I / k) * (Real.exp (-k * t) * (-k))) t :=
    hmul.const_add (I / k)
  have heq : (S0 - I / k) * (Real.exp (-k * t) * (-k))
      = I - k * (I / k + (S0 - I / k) * Real.exp (-k * t)) := by
    field_simp
    ring
  rw [heq] at hfull
  exact hfull

set_option linter.unusedVariables false in
/-- Integrated water budget: the time integral of storage has the closed
form below, and the storage change closes the budget
`S(t) - S0 = I * t - k * ∫₀ᵗ S`. -/
theorem integrated_water_budget {I k S0 : ℝ} (hk : 0 < k) (hI : 0 ≤ I)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, (I / k + (S0 - I / k) * Real.exp (-k * u)))
        = I * t / k + (S0 - I / k) * (1 - Real.exp (-k * t)) / k ∧
      (I / k + (S0 - I / k) * Real.exp (-k * t)) - S0
        = I * t - k * (∫ u in (0 : ℝ)..t,
            (I / k + (S0 - I / k) * Real.exp (-k * u))) := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hderiv : ∀ x : ℝ, HasDerivAt
      ((fun u : ℝ => (I / k) * u) + fun u : ℝ =>
        (-((S0 - I / k) * (1 / k))) * Real.exp (-k * u))
      (I / k + (S0 - I / k) * Real.exp (-k * x)) x := by
    intro x
    have hlin : HasDerivAt (fun u : ℝ => -k * u) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-k * u))
        (Real.exp (-k * x) * (-k)) x := hlin.exp
    have hmul : HasDerivAt
        (fun u : ℝ => (-((S0 - I / k) * (1 / k))) * Real.exp (-k * u))
        ((-((S0 - I / k) * (1 / k))) * (Real.exp (-k * x) * (-k))) x :=
      hexp.const_mul (-((S0 - I / k) * (1 / k)))
    have h1 : HasDerivAt (fun u : ℝ => (I / k) * u) ((I / k) * 1) x := by
      simpa using (hasDerivAt_id x).const_mul (I / k)
    have hadd := h1.add hmul
    have heq : (I / k) * 1 + (-((S0 - I / k) * (1 / k))) * (Real.exp (-k * x) * (-k))
        = I / k + (S0 - I / k) * Real.exp (-k * x) := by
      field_simp
    rw [heq] at hadd
    exact hadd
  have hInt : IntervalIntegrable
      (fun u : ℝ => I / k + (S0 - I / k) * Real.exp (-k * u))
      MeasureTheory.volume 0 t :=
    (by fun_prop :
      Continuous fun u : ℝ => I / k + (S0 - I / k) * Real.exp (-k * u)).intervalIntegrable
      0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hInt
  have hval : ((fun u : ℝ => (I / k) * u) + fun u : ℝ =>
          (-((S0 - I / k) * (1 / k))) * Real.exp (-k * u)) t
        - ((fun u : ℝ => (I / k) * u) + fun u : ℝ =>
          (-((S0 - I / k) * (1 / k))) * Real.exp (-k * u)) 0
        = I * t / k + (S0 - I / k) * (1 - Real.exp (-k * t)) / k := by
    simp only [Pi.add_apply, mul_zero, Real.exp_zero]
    field_simp
    ring
  have hclosed : (∫ u in (0 : ℝ)..t, (I / k + (S0 - I / k) * Real.exp (-k * u)))
      = I * t / k + (S0 - I / k) * (1 - Real.exp (-k * t)) / k :=
    hFTC.trans hval
  refine ⟨hclosed, ?_⟩
  rw [hclosed]
  field_simp
  ring

end EarthScience
