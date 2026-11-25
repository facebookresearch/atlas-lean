/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem728
import Mathlib.Tactic.Linarith

open Filter
open scoped Nat Topology

namespace MathlibExtTest.NumberTheory.ErdosProblem728

open MathlibExt.NumberTheory.ErdosProblem728Wanted

-- Specialize the window and recover strict bounds on the natural-number excess itself.
example : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ a b n : ℕ, 1 < n ∧ ε * n < a ∧ ε * n < b ∧
    a ! * b ! ∣ n ! * (a + b - n)! ∧
    Real.log n < (a + b - n : ℕ) ∧ ((a + b - n : ℕ) : ℝ) < 2 * Real.log n := by
  filter_upwards [conjecture_holds] with ε hε
  obtain ⟨a, b, n, hn, ha, hb, hdiv, hl, hu⟩ :=
    hε 1 (by norm_num) 2 (by norm_num)
  have hn' : 1 < n := by
    by_contra! h
    have : n = 1 := by omega
    subst n
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero] at hl hu
    exact hl.asymm hu
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn')
  have hsum : n ≤ a + b := by
    exact_mod_cast (show (n : ℝ) ≤ a + b by linarith)
  refine ⟨a, b, n, hn', ha, hb, hdiv, ?_, ?_⟩ <;>
    rw [Nat.cast_sub hsum, Nat.cast_add] <;> linarith

end MathlibExtTest.NumberTheory.ErdosProblem728
