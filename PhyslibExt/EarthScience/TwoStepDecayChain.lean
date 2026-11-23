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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.RadioactiveDecay

/-!
# Two-step decay chain (Bateman): parent and daughter satisfy both ODEs

A parent `P` decays with rate `l1` and feeds a daughter `D` that decays
with rate `l2`:
`P' = -l1 * P`, `D' = l1 * P - l2 * D`.

## i. Overview

The parent inventory is `P(t) = P0 * exp (-l1 * t)`. For distinct rates
`l1 ≠ l2` the daughter is
`D(t) = D0 * exp (-l2 * t)
  + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`:
Bateman (1910) solved these decay-chain equations for distinct decay
constants, and this file treats the two-member chain with an initial
daughter inventory `D0`. For the repeated rate `l1 = l2 = l` the
distinct-rate formula has a zero denominator, so that case is treated
separately with
`D(t) = (D0 + P0 * l * t) * exp (-l * t)`,
the limit of the distinct-rate formula as `l2 → l1`
(`tendsto_chainDaughterDistinct`). Each formula starts at its stated
initial inventory and satisfies its ODE at every time.

The physical domain is decay constants `l1, l2 > 0`, initial inventories
`P0, D0 ≥ 0` and elapsed time `t ≥ 0`, with `l1 ≠ l2` for the
distinct-rate formula. The definitions accept arbitrary reals, and the
theorems are proved for all real parameters (only
`chain_daughter_distinct_hasDerivAt` assumes `l1 ≠ l2`): an algebraic
extension beyond that domain, where `l1 < 0` gives exponential growth and
a negative `P0` or `D0` is not an inventory. At `l1 = l2` Lean's division
by zero makes `chainDaughterDistinct l l P0 D0 t = D0 * exp (-l * t)`,
which drops the feeding term and solves the daughter ODE only when
`l * P0 = 0`; `chain_daughter_distinct_hasDerivAt` therefore assumes
`l1 ≠ l2`, and `chainDaughterRepeated` covers equal rates.

## ii. Key results

- `EarthScience.chainParent`, `EarthScience.chainDaughterDistinct`,
  `EarthScience.chainDaughterRepeated`: the three inventory formulas.
- `EarthScience.chain_initial`, `EarthScience.chain_repeated_initial`:
  the initial values.
- `EarthScience.chain_parent_hasDerivAt`: the parent ODE, from
  `EarthScience.decay_hasDerivAt`.
- `EarthScience.chain_daughter_distinct_hasDerivAt`: the daughter ODE for
  distinct rates.
- `EarthScience.chain_daughter_repeated_hasDerivAt`: the daughter ODE for
  the repeated rate.
- `EarthScience.tendsto_chainDaughterDistinct`: the repeated-rate formula is
  the `l2 → l1` limit of the distinct-rate formula.

## iii. References

- H. Bateman, *The solution of a system of differential equations occurring
  in the theory of radioactive transformations*, Proc. Cambridge Philos.
  Soc. 15 (1910) 423–427: the decay-chain solution for distinct decay
  constants.
- `EarthScience.decay_hasDerivAt` (`PhyslibExt.EarthScience.RadioactiveDecay`)
  for the parent ODE.
- `HasDerivAt.exp`, `HasDerivAt.const_mul`, `HasDerivAt.add/sub/mul` in
  Mathlib (derivatives of the exponential formulas), and
  `hasDerivAt_iff_tendsto_slope` for the repeated-rate limit.
- `field_simp` with `l2 - l1 ≠ 0` for the distinct-rate derivative algebra.
-/

@[expose] public section

namespace EarthScience

/-- Parent inventory in a two-step chain: `P0 * exp (-l1 * t)`. Physically `l1 > 0`, `P0 ≥ 0`
and `t ≥ 0`; the formula is defined for all reals. -/
noncomputable def chainParent (l1 P0 t : ℝ) : ℝ := P0 * Real.exp (-l1 * t)

/-- Daughter inventory for distinct rates `l1 ≠ l2`:
`D0 * exp (-l2 * t) + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`.
At `l1 = l2` Lean's division by zero drops the feeding term, and the result solves the daughter
ODE only when `l1 * P0 = 0`; use `chainDaughterRepeated` for equal rates. -/
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

/-- Parent satisfies `P' = -l1 * P`: the decay law `EarthScience.decay_hasDerivAt`. -/
theorem chain_parent_hasDerivAt (l1 P0 t : ℝ) :
    HasDerivAt (chainParent l1 P0) (-l1 * chainParent l1 P0 t) t :=
  decay_hasDerivAt l1 P0 t

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

open Filter Topology in
/-- **Repeated-rate limit.** As `l2 → l1` with `l2 ≠ l1`, the distinct-rate daughter formula tends
to the repeated-rate formula with `l = l1`. -/
theorem tendsto_chainDaughterDistinct (l1 P0 D0 t : ℝ) :
    Tendsto (fun l2 => chainDaughterDistinct l1 l2 P0 D0 t) (𝓝[≠] l1)
      (𝓝 (chainDaughterRepeated l1 P0 D0 t)) := by
  -- the difference quotient of `l ↦ exp (-l * t)` tends to its derivative at `l1`
  have hg : HasDerivAt (fun l : ℝ => Real.exp (-l * t)) (Real.exp (-l1 * t) * (-1 * t)) l1 :=
    ((hasDerivAt_neg l1).mul_const t).exp
  have hslope := hasDerivAt_iff_tendsto_slope.1 hg
  have hc : Continuous fun l2 : ℝ => D0 * Real.exp (-l2 * t) := by fun_prop
  have hlim := ((hc.tendsto l1).mono_left nhdsWithin_le_nhds).add
    (hslope.const_mul (-(P0 * l1)))
  have heq : D0 * Real.exp (-l1 * t) + -(P0 * l1) * (Real.exp (-l1 * t) * (-1 * t)) =
      chainDaughterRepeated l1 P0 D0 t := by
    simp only [chainDaughterRepeated]
    ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l2 hl2
  have hne : l2 - l1 ≠ 0 := sub_ne_zero.2 hl2
  simp only [chainDaughterDistinct, slope_def_field]
  field_simp
  ring

end EarthScience
