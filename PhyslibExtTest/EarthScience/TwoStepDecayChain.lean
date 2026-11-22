/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.TwoStepDecayChain

/-!
# Two-step-decay-chain checks

Concrete consumers of `PhyslibExt.EarthScience.TwoStepDecayChain`: with
`P0 = 5`, `D0 = 2`, both formulas start at their initial inventories, the
parent satisfies its ODE at `t = 1`, and the distinct- and repeated-rate
daughter formulas satisfy theirs at `t = 1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The boundary
case is `t = 0`, where both daughter formulas return `D0`, and the
repeated-rate case is checked with `l = 1/2`, where it does not coincide
with a distinct-rate formula. Two last checks: at equal rates the
distinct-rate formula fails the daughter ODE (Lean's division by zero
drops the feeding term), and the repeated-rate formula at `l = 1/2` is the
limit of the distinct-rate formulas as `l2 → 1/2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.TwoStepDecayChain`
-/

open EarthScience

/-- Boundary case: at `t = 0` the parent is `P0 = 5` and the distinct-rate
daughter is `D0 = 2`. -/
example : chainParent (3 / 10) 5 0 = 5 ∧
    chainDaughterDistinct (3 / 10) (8 / 10) 5 2 0 = 2 :=
  chain_initial (3 / 10) (8 / 10) 5 2

/-- Boundary case: at `t = 0` the repeated-rate daughter is `D0 = 2`. -/
example : chainDaughterRepeated (1 / 2) 5 2 0 = 2 :=
  chain_repeated_initial (1 / 2) 5 2

/-- Parent ODE at `t = 1`, with `l1 = 3/10`, `P0 = 5`. -/
example : HasDerivAt (chainParent (3 / 10) 5)
    (-(3 / 10) * chainParent (3 / 10) 5 1) 1 :=
  chain_parent_hasDerivAt (3 / 10) 5 1

/-- Distinct-rate daughter ODE at `t = 1`, with `l1 = 3/10`, `l2 = 8/10`. -/
example : HasDerivAt (chainDaughterDistinct (3 / 10) (8 / 10) 5 2)
    ((3 / 10) * chainParent (3 / 10) 5 1
      - (8 / 10) * chainDaughterDistinct (3 / 10) (8 / 10) 5 2 1) 1 :=
  chain_daughter_distinct_hasDerivAt (3 / 10) (8 / 10) 5 2 1 (by norm_num)

/-- Repeated-rate daughter ODE at `t = 1`, with `l = 1/2`. -/
example : HasDerivAt (chainDaughterRepeated (1 / 2) 5 2)
    ((1 / 2) * chainParent (1 / 2) 5 1
      - (1 / 2) * chainDaughterRepeated (1 / 2) 5 2 1) 1 :=
  chain_daughter_repeated_hasDerivAt (1 / 2) 5 2 1

/-- The distinct-rate daughter at `t = 0` is `D0` even when `P0 = 0`:
the feeding term vanishes at the initial time. -/
example : chainDaughterDistinct (3 / 10) (8 / 10) 0 2 0 = 2 :=
  (chain_initial (3 / 10) (8 / 10) 0 2).2

/-- Equal rates: with `l1 = l2 = 1`, `P0 = 1`, `D0 = 0` Lean's division by
zero makes the distinct-rate formula identically `0`, but the daughter ODE
asks for slope `1` at `t = 0`. -/
example : ¬ HasDerivAt (chainDaughterDistinct 1 1 1 0)
    (1 * chainParent 1 1 0 - 1 * chainDaughterDistinct 1 1 1 0 0) 0 := by
  have h0 : chainDaughterDistinct 1 1 1 0 = fun _ => 0 := by
    funext t
    simp [chainDaughterDistinct]
  rw [h0]
  intro h
  have := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  norm_num [chainParent] at this

open Filter Topology in
/-- Repeated-rate limit at `l = 1/2`, `P0 = 5`, `D0 = 2`, `t = 1`. -/
example : Tendsto (fun l2 => chainDaughterDistinct (1 / 2) l2 5 2 1) (𝓝[≠] (1 / 2))
    (𝓝 (chainDaughterRepeated (1 / 2) 5 2 1)) :=
  tendsto_chainDaughterDistinct (1 / 2) 5 2 1
