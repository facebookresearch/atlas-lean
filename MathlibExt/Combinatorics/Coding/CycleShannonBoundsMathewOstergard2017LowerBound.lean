/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.PolakSchrijver
import Mathlib.Tactic.NormNum

/-!
# The Mathew–Östergård lower bound for the seven-cycle

The rate bound follows from the stronger Polak–Schrijver rate bound by comparing fifth roots.
-/

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- **Mathew–Östergård lower bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at least $350^{1/5}$, as an inequality in $[0, \infty]$.

Source: Mathew--Östergård (2017), exact rate row; no unprinted code is supplied. -/
public theorem mathewOstergard2017LowerBound :
  ENNReal.rpow 350 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  calc
    ENNReal.rpow 350 ((5 : ℝ)⁻¹) ≤ ENNReal.rpow 367 ((5 : ℝ)⁻¹) := by
      exact (ENNReal.rpow_lt_rpow (by norm_num) (by norm_num)).le
    _ ≤ shannonCapacityCycle 7 := polakSchrijverRateLowerBound

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
