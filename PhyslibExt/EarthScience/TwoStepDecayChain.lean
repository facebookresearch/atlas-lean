/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two-step decay chain (Bateman): parent and daughter satisfy both ODEs

A parent `P` decays with rate `l1` and feeds a daughter `D` that decays
with rate `l2`:
`P' = -l1 * P`, `D' = l1 * P - l2 * D`.

## i. Overview

The parent inventory is `P(t) = P0 * exp (-l1 * t)`. For distinct rates
`l1 ≠ l2` the daughter is
`D(t) = D0 * exp (-l2 * t)
  + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`,
the Bateman solution. For the repeated rate `l1 = l2 = l` the
distinct-rate formula has a zero denominator, so that case is treated
separately with
`D(t) = (D0 + P0 * l * t) * exp (-l * t)`,
the limit of the distinct-rate formula as `l2 → l1`. Each formula starts
at its stated initial inventory and satisfies its ODE at every time.

## ii. Key results

- `EarthScience.chainParent`, `EarthScience.chainDaughterDistinct`,
  `EarthScience.chainDaughterRepeated`: the three inventory formulas.
- `EarthScience.chain_initial`, `EarthScience.chain_repeated_initial`:
  the initial values.
- `EarthScience.chain_parent_hasDerivAt`: the parent ODE.
- `EarthScience.chain_daughter_distinct_hasDerivAt`: the daughter ODE for
  distinct rates.
- `EarthScience.chain_daughter_repeated_hasDerivAt`: the daughter ODE for
  the repeated rate.

## iii. References

- `HasDerivAt.exp`, `HasDerivAt.const_mul`, `HasDerivAt.add/sub/mul` in
  Mathlib (derivatives of the exponential formulas).
- `field_simp` with `l2 - l1 ≠ 0` for the distinct-rate derivative algebra.
-/

@[expose] public section

namespace EarthScience

/-- Parent inventory in a two-step chain: `P0 * exp (-l1 * t)`. -/
noncomputable def chainParent (l1 P0 t : ℝ) : ℝ := P0 * Real.exp (-l1 * t)

/-- Daughter inventory for distinct rates `l1 ≠ l2`:
`D0 * exp (-l2 * t) + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`. -/
noncomputable def chainDaughterDistinct (l1 l2 P0 D0 t : ℝ) : ℝ :=
  D0 * Real.exp (-l2 * t)
    + P0 * l1 / (l2 - l1) * (Real.exp (-l1 * t) - Real.exp (-l2 * t))

/-- Daughter inventory for the repeated rate `l1 = l2 = l`:
`(D0 + P0 * l * t) * exp (-l * t)`. -/
noncomputable def chainDaughterRepeated (l P0 D0 t : ℝ) : ℝ :=
  (D0 + P0 * l * t) * Real.exp (-l * t)

/-- Derivative of `t ↦ Real.exp (-l * t)`. -/
private theorem chain_hasDerivAt_exp_neg_mul (l t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-l * t)) (Real.exp (-l * t) * (-l * 1)) t := by
  have hlin : HasDerivAt (fun t : ℝ => -l * t) (-l * 1) t :=
    (hasDerivAt_id t).const_mul (-l)
  exact hlin.exp

/-- Parent starts at `P0` and the distinct-rate daughter at `D0`. -/
theorem chain_initial (l1 l2 P0 D0 : ℝ) :
    chainParent l1 P0 0 = P0 ∧ chainDaughterDistinct l1 l2 P0 D0 0 = D0 := by
  constructor
  · simp [chainParent]
  · simp [chainDaughterDistinct]

/-- The repeated-rate daughter starts at `D0`. -/
theorem chain_repeated_initial (l P0 D0 : ℝ) :
    chainDaughterRepeated l P0 D0 0 = D0 := by
  simp [chainDaughterRepeated]

/-- Parent satisfies `P' = -l1 * P`. -/
theorem chain_parent_hasDerivAt (l1 P0 t : ℝ) :
    HasDerivAt (chainParent l1 P0) (-l1 * chainParent l1 P0 t) t := by
  have h : HasDerivAt (chainParent l1 P0)
      (P0 * (Real.exp (-l1 * t) * (-l1 * 1))) t :=
    (chain_hasDerivAt_exp_neg_mul l1 t).const_mul P0
  convert h using 1
  simp only [chainParent]
  ring

/-- Distinct rates: daughter satisfies `D' = l1 * P - l2 * D`. -/
theorem chain_daughter_distinct_hasDerivAt (l1 l2 P0 D0 t : ℝ) (hne : l1 ≠ l2) :
    HasDerivAt (chainDaughterDistinct l1 l2 P0 D0)
      (l1 * chainParent l1 P0 t - l2 * chainDaughterDistinct l1 l2 P0 D0 t) t := by
  have h1 : HasDerivAt (fun t : ℝ => D0 * Real.exp (-l2 * t))
      (D0 * (Real.exp (-l2 * t) * (-l2 * 1))) t :=
    (chain_hasDerivAt_exp_neg_mul l2 t).const_mul D0
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-l1 * t) - Real.exp (-l2 * t))
      (Real.exp (-l1 * t) * (-l1 * 1) - Real.exp (-l2 * t) * (-l2 * 1)) t :=
    (chain_hasDerivAt_exp_neg_mul l1 t).sub (chain_hasDerivAt_exp_neg_mul l2 t)
  have h3 : HasDerivAt
      (fun t : ℝ => P0 * l1 / (l2 - l1) * (Real.exp (-l1 * t) - Real.exp (-l2 * t)))
      (P0 * l1 / (l2 - l1) *
        (Real.exp (-l1 * t) * (-l1 * 1) - Real.exp (-l2 * t) * (-l2 * 1))) t :=
    h2.const_mul (P0 * l1 / (l2 - l1))
  have h : HasDerivAt (chainDaughterDistinct l1 l2 P0 D0)
      (D0 * (Real.exp (-l2 * t) * (-l2 * 1)) +
        P0 * l1 / (l2 - l1) *
          (Real.exp (-l1 * t) * (-l1 * 1) - Real.exp (-l2 * t) * (-l2 * 1))) t :=
    h1.add h3
  convert h using 1
  have hne' : l2 - l1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [chainParent, chainDaughterDistinct]
  field_simp
  ring

/-- Repeated rate: daughter satisfies `D' = l * P - l * D` with `l1 = l2 = l`. -/
theorem chain_daughter_repeated_hasDerivAt (l P0 D0 t : ℝ) :
    HasDerivAt (chainDaughterRepeated l P0 D0)
      (l * chainParent l P0 t - l * chainDaughterRepeated l P0 D0 t) t := by
  have hlin : HasDerivAt (fun t : ℝ => D0 + P0 * l * t) (P0 * l * 1) t :=
    ((hasDerivAt_id t).const_mul (P0 * l)).const_add D0
  have h : HasDerivAt (chainDaughterRepeated l P0 D0)
      (P0 * l * 1 * Real.exp (-l * t) +
        (D0 + P0 * l * t) * (Real.exp (-l * t) * (-l * 1))) t :=
    hlin.mul (chain_hasDerivAt_exp_neg_mul l t)
  convert h using 1
  simp only [chainParent, chainDaughterRepeated]
  ring

end EarthScience
