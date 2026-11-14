/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Growth
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for growth bounds in the Selberg class
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

/-- `ζ` is bounded on the line `Re s = 2`. -/
example : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re = 2 → ‖riemannZeta s‖ ≤ B :=
  isLSeriesContinuation_zeta.exists_norm_le_of_re_eq_two (Ca := 1) fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simpa [hn.ne'] using Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The entire member `1` has polynomial growth in the critical strip. -/
example : ∃ A > (0 : ℝ), ∃ C, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1 ≤ |s.im| →
    ‖(fun _ : ℂ => (1 : ℂ)) s‖ ≤ C * |s.im| ^ A :=
  exists_norm_le_mul_rpow_of_differentiable 1 one_mem_selbergClass _ isLSeriesContinuation_one
    (differentiable_const _)

end SelbergClassTest
