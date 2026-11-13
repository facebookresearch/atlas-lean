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
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Capstone: planetary energy and two-box warming

## i. Overview

Synthetic nondimensional two-box model with `Cs = Cd = lam = γ = F = 1`.
The ODE, stated directly in the lemmas below, is
`Ts' = 1 - Ts - (Ts - Td)`, `Td' = Ts - Td`. Equilibrium observations
`T = 1, F = 1` identify `lam = 1` only under this model. This is a
nondimensional teaching example; synthetic agreement does not validate
a climate model. This capstone is proved self-contained from Mathlib
primitives; it does not depend on any sibling development and does not
re-prove or assume any unmerged "K02" theorem.

## ii. Key results

- `EarthScience.two_box_equilibrium`: `(1, 1)` is an equilibrium.
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

- `antitoneOn_of_deriv_nonpos`, `HasDerivAt.exp`, `Real.exp_add` in Mathlib.

## A. Equilibrium, budget, energy identity and inequality
-/

@[expose] public section

namespace EarthScience


/-- Capstone (two-box model, `Cs = Cd = lam = γ = F = 1`):
equilibrium `(Ts, Td) = (1, 1)` annihilates both right-hand sides:
`1 - 1 - (1 - 1) = 0` and `1 - 1 = 0`. -/
lemma two_box_equilibrium :
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
`E t ≤ E 0 * exp (-(2 / 3) * t)`. -/
lemma two_box_energy_bound {Ts Td : ℝ → ℝ}
    (hODE : ∀ t : ℝ, HasDerivAt Ts (1 - Ts t - (Ts t - Td t)) t ∧
      HasDerivAt Td (Ts t - Td t) t)
    (hTs0 : Ts 0 = 0) (hTd0 : Td 0 = 0) :
    ∀ t : ℝ, 0 ≤ t →
      ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 ≤ Real.exp (-(2 / 3) * t) := by
  have hE : ∀ t : ℝ, HasDerivAt
      (fun t => ((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
      (((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
        + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
        + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2) t := by
    intro t
    have hTs1 : HasDerivAt (fun t => Ts t - 1) (1 - Ts t - (Ts t - Td t)) t :=
      (hODE t).1.sub_const 1
    have hTd1 : HasDerivAt (fun t => Td t - 1) (Ts t - Td t) t :=
      (hODE t).2.sub_const 1
    exact ((hTs1.mul hTs1).add (hTd1.mul hTd1)).div_const 2
  have hexp : ∀ t : ℝ, HasDerivAt (fun t => Real.exp ((2 / 3) * t))
      (Real.exp ((2 / 3) * t) * ((2 / 3) * 1)) t := by
    intro t
    exact (HasDerivAt.const_mul (2 / 3 : ℝ) (hasDerivAt_id' t)).exp
  have hφ : ∀ t : ℝ, HasDerivAt
      (fun t => (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t))
      ((((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
        + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
        + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2)
        * Real.exp ((2 / 3) * t)
        + (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
          * (Real.exp ((2 / 3) * t) * ((2 / 3) * 1))) t := by
    intro t
    exact (hE t).mul (hexp t)
  have hnonpos : ∀ t : ℝ, 0 ≤ t →
      ((((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
        + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
        + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2)
        * Real.exp ((2 / 3) * t)
        + (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
          * (Real.exp ((2 / 3) * t) * ((2 / 3) * 1))) ≤ 0 := by
    intro t _
    have h4 := two_box_energy_differential_inequality (Ts := Ts t) (Td := Td t)
      (Ts' := 1 - Ts t - (Ts t - Td t)) (Td' := Ts t - Td t) rfl rfl
    have hK : 0 < Real.exp ((2 / 3) * t) := Real.exp_pos _
    have hfactor : ((((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
          + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
          + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2)
          * Real.exp ((2 / 3) * t)
          + (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
            * (Real.exp ((2 / 3) * t) * ((2 / 3) * 1)))
        = (((((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
          + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
          + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2)
          + (2 / 3) * (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2))
          * Real.exp ((2 / 3) * t)) := by
      ring
    rw [hfactor]
    refine mul_nonpos_of_nonpos_of_nonneg ?_ hK.le
    have heq1 : (((1 - Ts t - (Ts t - Td t)) * (Ts t - 1)
          + (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
          + ((Ts t - Td t) * (Td t - 1) + (Td t - 1) * (Ts t - Td t))) / 2)
        = (Ts t - 1) * (1 - Ts t - (Ts t - Td t))
          + (Td t - 1) * (Ts t - Td t) := by
      ring
    have heq2 : (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        = ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 := by
      ring
    linarith [h4, heq1, heq2]
  have hcont : ContinuousOn
      (fun t => (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) (Set.Ici 0) := by
    intro x _
    exact (hφ x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (fun t => (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) (interior (Set.Ici 0)) := by
    intro x _
    exact (hφ x).differentiableAt.differentiableWithinAt
  have hderiv_nonpos : ∀ x ∈ interior (Set.Ici 0),
      deriv (fun t => (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) x ≤ 0 := by
    intro x hx
    rw [interior_Ici] at hx
    rw [(hφ x).deriv]
    exact hnonpos x (le_of_lt (Set.mem_Ioi.mp hx))
  have hmono : AntitoneOn
      (fun t => (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hderiv_nonpos
  intro t ht
  have hle : ((((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t))
      ≤ ((((Ts 0 - 1) * (Ts 0 - 1) + (Td 0 - 1) * (Td 0 - 1)) / 2)
        * Real.exp ((2 / 3) * 0)) :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hφ0 : ((((Ts 0 - 1) * (Ts 0 - 1) + (Td 0 - 1) * (Td 0 - 1)) / 2)
      * Real.exp ((2 / 3) * 0)) = 1 := by
    rw [hTs0, hTd0, mul_zero, Real.exp_zero, mul_one]
    norm_num
  rw [hφ0] at hle
  have hK2 : 0 < Real.exp (-(2 / 3) * t) := Real.exp_pos _
  have hexp_add : Real.exp ((2 / 3) * t) * Real.exp (-(2 / 3) * t) = 1 := by
    rw [← Real.exp_add]
    have harg : (2 / 3 : ℝ) * t + (-(2 / 3)) * t = 0 := by ring
    rw [harg, Real.exp_zero]
  have hsplit : (((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 : ℝ)
      = (((((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) * Real.exp (-(2 / 3) * t)) := by
    calc (((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 : ℝ)
        = (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2) := by ring
      _ = (((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
          * (Real.exp ((2 / 3) * t) * Real.exp (-(2 / 3) * t)) := by
          rw [hexp_add, mul_one]
      _ = (((((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
        * Real.exp ((2 / 3) * t)) * Real.exp (-(2 / 3) * t)) := by ring
  rw [hsplit]
  calc (((((Ts t - 1) * (Ts t - 1) + (Td t - 1) * (Td t - 1)) / 2)
      * Real.exp ((2 / 3) * t)) * Real.exp (-(2 / 3) * t) : ℝ)
      ≤ 1 * Real.exp (-(2 / 3) * t) := mul_le_mul_of_nonneg_right hle hK2.le
    _ = Real.exp (-(2 / 3) * t) := one_mul _

end EarthScience
