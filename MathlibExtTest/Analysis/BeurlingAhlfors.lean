/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.BeurlingAhlfors

@[expose] public section

namespace MathlibExtTest.BeurlingAhlfors

open MathlibExt.Analysis.BeurlingAhlfors

/-- The conjugate-exponent factor at the self-dual exponent. -/
example : pstar 2 = 2 := pstar_two

/-- Boundary behavior of `p*` on both sides of `2`. -/
example : (2:ℝ) ≤ pstar (3 / 2) := two_le_pstar (by norm_num)

example : (2:ℝ) ≤ pstar 3 := two_le_pstar (by norm_num)

example : (1:ℝ) ≤ pstar (5 / 4) - 1 := one_le_pstar_sub_one (by norm_num)

/-- Admissible constants are upward closed. -/
example {p C : ℝ} (h : IsBound p C) : IsBound p (C + 1) :=
  h.mono (by linarith)

/-- An actual admissible bound yields the norm inequality for the
totalized infimum, via the characteristic lemma. -/
example {p : ℝ} (hp : 1 < p)
    (h : IsBound p ((1575 / 1000 : ℝ) * (pstar p - 1))) :
    beurlingNorm p ≤ (1575 / 1000 : ℝ) * (pstar p - 1) := by
  apply beurlingNorm_le_of_isBound _ h
  have h2 : (2:ℝ) ≤ pstar p := two_le_pstar hp
  exact mul_nonneg (by norm_num) (by linarith)

end MathlibExtTest.BeurlingAhlfors
