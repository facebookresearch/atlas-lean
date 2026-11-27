/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.ZoneQuadraticDissipation
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Thermal quadratic dissipation checks

Focused checks for `PhyslibExt.Engineering.ZoneQuadraticDissipation`:
a two-zone fixture with conductance `3 / 2`, temperatures
`(1 + exp (-3s), 1 - exp (-3s))`, where the dissipation derivative at `s = 0` is
`-6`; and one isolated zone (no inter-zone conductance) whose
derivative is the boundary term only.

These are elaboration and non-vacuity checks, not new results.
-/

open ZoneHeatInventory

/-- One zone with boundary conductance `3 / 2` to the outside
reference and exact solution `T s = 5 * exp (-(3/2) * s)`: the
dissipation derivative at time `0` is `-(3/2) * 25 = -75 / 2`. -/
example : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * ∑ i : Fin 1,
      (1 : ℝ) * ((fun _ : Fin 1 => 5 * Real.exp (-(3 / 2) * s)) i
        - 0) ^ 2) (-75 / 2) 0 := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (-(3 / 2) * s))
      (Real.exp (-(3 / 2) * t) * -(3 / 2)) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (-(3 / 2 : ℝ))).exp
    simp only [id_eq, mul_one, ← neg_mul] at h
    exact h
  have h := (quadratic_dissipation_nonpos (fun _ : Fin 1 => (1 : ℝ))
    (fun _ _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (3 / 2 : ℝ)) 0
    (fun _ s => 5 * Real.exp (-(3 / 2) * s))
    (fun _ s => 5 * (Real.exp (-(3 / 2) * s) * -(3 / 2)))
    (by simp) (by simp) (by intro i; norm_num)
    (by
      intro i t
      fin_cases i
      simpa using (hexp t).const_mul (5 : ℝ))
    (by
      intro i t
      fin_cases i
      simp
      ring) 0)
  have hval : -((1 / 2 : ℝ) * ∑ i : Fin 1, ∑ j : Fin 1,
        (0 : ℝ) * (5 * Real.exp (-(3 / 2) * (0 : ℝ))
          - 5 * Real.exp (-(3 / 2) * (0 : ℝ))) ^ 2
        + ∑ i : Fin 1, (3 / 2 : ℝ)
          * (5 * Real.exp (-(3 / 2) * (0 : ℝ)) - 0) ^ 2) = -75 / 2 := by
    simp
    norm_num
  rw [hval] at h
  exact h.1

/-- One isolated zone: with no inter-zone conductance, no boundary
conductance, and no power, the derivative is `0`. -/
example : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * ∑ i : Fin 1,
      (1 : ℝ) * ((fun _ : Fin 1 => (5 : ℝ)) i - 0) ^ 2) 0 0 := by
  have h := (quadratic_dissipation_nonpos (fun _ : Fin 1 => (1 : ℝ))
    (fun _ _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) 0
    (fun _ _ => (5 : ℝ)) (fun _ _ => (0 : ℝ))
    (by simp) (by simp) (by simp)
    (by intro i t; simpa using hasDerivAt_const t (5 : ℝ))
    (by intro i t; simp) 0)
  simpa using h.1

/-- Two zones with reciprocal conductance `3 / 2` and exact
solution `T s = (1 + exp (-3s), 1 - exp (-3s))`: the dissipation
derivative at time `0` is `-6`, exercising the reciprocal edge
term and its `1 / 2` factor. -/
example : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * ∑ i : Fin 2,
      (1 : ℝ) * ((![1 + Real.exp (-3 * s), 1 - Real.exp (-3 * s)]
        : Fin 2 → ℝ) i - 0) ^ 2) (-6) 0 := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (-3 * s))
      (Real.exp (-3 * t) * -3) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (-3 : ℝ)).exp
    simpa using h
  have h := (quadratic_dissipation_nonpos (fun _ : Fin 2 => (1 : ℝ))
    (fun i j : Fin 2 => if i = j then 0 else 3 / 2)
    (fun _ : Fin 2 => (0 : ℝ)) 0
    (fun i s => (![1 + Real.exp (-3 * s), 1 - Real.exp (-3 * s)]
      : Fin 2 → ℝ) i)
    (fun i s => (![Real.exp (-3 * s) * -3, Real.exp (-3 * s) * 3]
      : Fin 2 → ℝ) i)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num)
    (by intro i; simp)
    (by
      intro i t
      fin_cases i
      · have h1 := (hasDerivAt_const t (1 : ℝ)).add (hexp t)
        simp only [zero_add] at h1
        exact h1
      · have h1 := (hasDerivAt_const t (1 : ℝ)).sub (hexp t)
        convert h1 using 1
        · funext s
          simp
        · simp)
    (by
      intro i t
      fin_cases i <;>
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;>
        ring) 0)
  have hval : -((1 / 2 : ℝ) * ∑ i : Fin 2, ∑ j : Fin 2,
        (if i = j then (0 : ℝ) else 3 / 2)
          * ((![1 + Real.exp (-3 * (0 : ℝ)), 1 - Real.exp (-3 * (0 : ℝ))]
              : Fin 2 → ℝ) j
            - (![1 + Real.exp (-3 * (0 : ℝ)), 1 - Real.exp (-3 * (0 : ℝ))]
              : Fin 2 → ℝ) i) ^ 2
        + ∑ i : Fin 2, (0 : ℝ)
          * ((![1 + Real.exp (-3 * (0 : ℝ)), 1 - Real.exp (-3 * (0 : ℝ))]
              : Fin 2 → ℝ) i - 0) ^ 2) = -6 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    norm_num
  rw [hval] at h
  exact h.1
