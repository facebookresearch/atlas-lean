/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifferenceCycles

open MetaMathlibExt

-- Squaring modulo 7 sends the tail vertex 3 to the two-cycle 2 → 4 → 2.
example : ∃ m r : ℕ, 0 < r ∧ ((3 : ZMod 7) ^ (2 : ℕ) ^ m) ^ (2 : ℕ) ^ r =
    (3 : ZMod 7) ^ (2 : ℕ) ^ m := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (powMap_component_unique_cycle 7 2).1 3

-- The two periodic vertices meet after different positive numbers of steps.
example : ∃ m : ℕ, (2 : ZMod 7) ^ (2 : ℕ) ^ m = 4 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (powMap_component_unique_cycle 7 2).2 2 4
    ⟨2, by decide, by decide⟩ ⟨2, by decide, by decide⟩ ⟨2, 1, by decide⟩

-- At exponent zero, even zero flows into the fixed point 1.
example : ∃ m r : ℕ, 0 < r ∧ ((0 : ZMod 2) ^ (0 : ℕ) ^ m) ^ (0 : ℕ) ^ r =
    (0 : ZMod 2) ^ (0 : ℕ) ^ m := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact (powMap_component_unique_cycle 2 0).1 0
