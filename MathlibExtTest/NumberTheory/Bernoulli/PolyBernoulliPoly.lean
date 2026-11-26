/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliPoly
import Mathlib.Tactic.NormNum

open MetaMathlibExt

example (n : ℕ) (p : ℤ) : polyBernoulliPoly n p 0 = polyBernoulli n p :=
  polyBernoulliPoly_zero n p

example (p : ℤ) (x : ℚ) : polyBernoulliPoly 0 p x = 1 :=
  polyBernoulliPoly_zero_index p x

example : polyBernoulliPoly 2 (-(2 : ℤ)) (-1) = 7 := by
  unfold polyBernoulliPoly polyBernoulli
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond_self,
    Nat.stirlingSecond_one_right]
