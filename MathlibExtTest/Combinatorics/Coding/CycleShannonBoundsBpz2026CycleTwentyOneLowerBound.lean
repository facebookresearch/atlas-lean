/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneLowerBound
import Mathlib.Tactic.NormNum

/-!
# A consequence of the twenty-one-cycle capacity bound

The BPZ root-rate bound implies that the twenty-one-cycle capacity is at least ten.

Source: Pjotr Buys, Sven Polak and Jeroen Zuiddam,
*Lean-verified lower bounds for the Shannon capacity of odd cycles*, arXiv:2607.29681v1
(2026).
-/

namespace MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneLowerBound

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

example : (10 : ENNReal) ≤ shannonCapacityCycle 21 := by
  have hcard : 10 ^ 4096 ≤ bpzC21Pi1024.code.toNat := by decide +kernel
  calc
    (10 : ENNReal) = ((10 : ENNReal) ^ 4096) ^ ((4096 : ℝ)⁻¹) :=
      (ENNReal.pow_rpow_inv_natCast (by decide : (4096 : ℕ) ≠ 0) (10 : ENNReal)).symm
    _ ≤ (bpzC21Pi1024.code.toNat : ENNReal) ^ ((4096 : ℝ)⁻¹) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact_mod_cast hcard
    _ ≤ shannonCapacityCycle 21 := by
      simpa only [ENNReal.rpow_eq_pow] using bpz2026CycleTwentyOneLowerBound

end MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneLowerBound
