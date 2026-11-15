/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.HopcroftBound

@[expose] public section

/-- After 4 halvings from 16, at most 1 element remains. -/
example (a : ℕ → ℕ) (h0 : a 0 ≤ 16) (hstep : ∀ k, a (k + 1) ≤ a k / 2) :
    a 4 ≤ 1 := smaller_half_bound a 16 h0 hstep 4

/-- A block still positive after 4 rounds from 16 respects the log bound. -/
example (a : ℕ → ℕ) (h0 : a 0 ≤ 16) (hstep : ∀ k, a (k + 1) ≤ a k / 2)
    (hk : 0 < a 4) : 4 ≤ Nat.log 2 16 :=
  smaller_half_rounds a 16 (by norm_num) h0 hstep 4 hk

end
