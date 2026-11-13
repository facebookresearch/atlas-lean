/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.LyapunovStability

/-!
# Capstone: planetary energy and two-box warming

## i. Overview

Synthetic nondimensional two-box model with `Cs = Cd = lam = γ = F = 1`.
The ODE, stated directly in the lemmas below, is
`Ts' = 1 - Ts - (Ts - Td)`, `Td' = Ts - Td`. Equilibrium observations
`T = 1, F = 1` identify `lam = 1` only under this model. This is a
nondimensional teaching example; synthetic agreement does not validate
a climate model. The exponential bound applies the existing estimate
`le_exp_mul_of_hasDerivWithinAt_Ici` to the anomaly energy; the capstone
does not depend on any sibling development and does not re-prove or
assume any "K02" (`ClimateFeedback`) theorem.

## ii. Key results

- `EarthScience.two_box_warming_equilibrium`: `(1, 1)` is an equilibrium.
- `EarthScience.two_box_combined_budget`: `(Ts + Td)' = 1 - Ts`.
- `EarthScience.two_box_energy_derivative`: the anomaly-energy derivative
  identity along the flow.
- `EarthScience.two_box_energy_differential_inequality`: `E' ≤ -(2 / 3) * E`.
- `EarthScience.two_box_energy_bound`: `E t ≤ exp (-(2 / 3) * t)` for
  `t ≥ 0` from `Ts 0 = Td 0 = 0` (so `E 0 = 1`).

## iii. Table of contents

- A. Equilibrium, budget, energy identity and inequality
- B. Exponential energy bound

## iv. References

- `le_exp_mul_of_hasDerivWithinAt_Ici` in `MathlibExt.Analysis.ODE.LyapunovStability`.

## A. Equilibrium, budget, energy identity and inequality
-/

@[expose] public section

namespace EarthScience


/-- Capstone (two-box model, `Cs = Cd = lam = γ = F = 1`):
equilibrium `(Ts, Td) = (1, 1)` annihilates both right-hand sides:
`1 - 1 - (1 - 1) = 0` and `1 - 1 = 0`. -/
lemma two_box_warming_equilibrium :
    (1 : ℝ) - 1 - (1 - 1) = 0 ∧ (1 : ℝ) - 1 = 0 := by
  constructor <;> norm_num

/-- Combined budget: if `Ts' = 1 - Ts - (Ts - Td)` and `Td' = Ts - Td`
then `(Ts + Td)' = Ts' + Td' = 1 - Ts`. -/
lemma two_box_combined_budget {Ts Td Ts' Td' : ℝ}
    (hTs : Ts' = 1 - Ts - (Ts - Td)) (hTd : Td' = Ts - Td) :
    Ts' + Td' = 1 - Ts := by
  linarith [hTs, hTd]

/-- Anomaly-energy derivative identity: with `a = Ts - 1`, the
derivative of `E = ((Ts - 1) ^ 2 + (Td - 1) ^ 2) / 2` along the flow,
`(Ts - 1) * Ts' + (Td - 1) * Td'`, equals
`-((Ts - 1) ^ 2 + (Ts - Td) ^ 2)`. -/
lemma two_box_energy_derivative {Ts Td Ts' Td' : ℝ}
    (hTs : Ts' = 1 - Ts - (Ts - Td)) (hTd : Td' = Ts - Td) :
    (Ts - 1) * Ts' + (Td - 1) * Td'
      = -((Ts - 1) ^ 2 + (Ts - Td) ^ 2) := by
  rw [hTs, hTd]
  ring

/-- Differential energy inequality: the same derivative is at most
`-(2 / 3) * E`, where `E = ((Ts - 1) ^ 2 + (Td - 1) ^ 2) / 2`. -/
lemma two_box_energy_differential_inequality {Ts Td Ts' Td' : ℝ}
    (hTs : Ts' = 1 - Ts - (Ts - Td)) (hTd : Td' = Ts - Td) :
    (Ts - 1) * Ts' + (Td - 1) * Td'
      ≤ -(2 / 3) * (((Ts - 1) ^ 2 + (Td - 1) ^ 2) / 2) := by
  have h3 := two_box_energy_derivative hTs hTd
  rw [h3]
  nlinarith [sq_nonneg (Ts - Td), sq_nonneg (2 * (Ts - 1) - (Td - 1))]

/-! ## B. Exponential energy bound -/

/-- Exponential energy bound: if `Ts, Td` satisfy the two-box ODE at
every `t` and start at `Ts 0 = Td 0 = 0` (so `E 0 = 1`), then for
`t ≥ 0`, `E t ≤ exp (-(2 / 3) * t)`, i.e.
`E t ≤ E 0 * exp (-(2 / 3) * t)`. This is
`le_exp_mul_of_hasDerivWithinAt_Ici` with `u = E` and `a = 2 / 3`. -/
lemma two_box_energy_bound {Ts Td : ℝ → ℝ}
    (hODE : ∀ t : ℝ, HasDerivAt Ts (1 - Ts t - (Ts t - Td t)) t ∧
      HasDerivAt Td (Ts t - Td t) t)
    (hTs0 : Ts 0 = 0) (hTd0 : Td 0 = 0) :
    ∀ t : ℝ, 0 ≤ t →
      ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 ≤ Real.exp (-(2 / 3) * t) := by
  have hE : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt
      (fun t => ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2)
      ((Ts t - 1) * (1 - Ts t - (Ts t - Td t)) + (Td t - 1) * (Ts t - Td t))
      (Set.Ici 0) t := by
    intro t _
    have hTs1 := (hODE t).1.sub_const 1
    have hTd1 := (hODE t).2.sub_const 1
    convert (((hTs1.mul hTs1).add (hTd1.mul hTd1)).div_const 2).hasDerivWithinAt using 1
    · funext s
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    · ring
  intro t ht
  calc ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2
      ≤ Real.exp (-(2 / 3) * t) * (((Ts 0 - 1) ^ 2 + (Td 0 - 1) ^ 2) / 2) :=
        le_exp_mul_of_hasDerivWithinAt_Ici hE
          (fun s _ => two_box_energy_differential_inequality (Ts := Ts s) (Td := Td s)
            (Ts' := 1 - Ts s - (Ts s - Td s)) (Td' := Ts s - Td s) rfl rfl) ht
    _ = Real.exp (-(2 / 3) * t) := by
        rw [hTs0, hTd0]
        norm_num

end EarthScience
