/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskRows

/-! Exact XOR parent evaluation stays in the bounded finite mask domain. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- XOR of bounded indexed columns cannot introduce a discarded high coordinate bit. -/
theorem generatedAxisGlobalMaskRowsAction_lt (n : ℕ) (rows : List (ℕ × ℕ))
    (hrows : ∀ p ∈ rows, p.2 < 2 ^ n) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction rows b < 2 ^ n := by
  induction rows with
  | nil => exact Nat.two_pow_pos n
  | cons p rows ih =>
      have hp : p.2 < 2 ^ n := hrows p (by simp)
      have hr : ∀ q ∈ rows, q.2 < 2 ^ n := by
        intro q hq
        exact hrows q (by simp [hq])
      cases h : b.testBit p.1
      · simpa [generatedAxisGlobalMaskRowsAction, h] using ih hr
      · simp only [generatedAxisGlobalMaskRowsAction, h, ↓reduceIte]
        exact Nat.xor_lt_two_pow hp (ih hr)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
