/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.WallisPrimeFactor
import Mathlib.Tactic.NormNum

open MetaMathlibExt

example :
    (((3 : ℕ) : ℝ) - ZMod.χ₄ ((3 : ℕ) : ZMod 4)) /
      (((3 : ℕ) : ℝ) + ZMod.χ₄ ((3 : ℕ) : ZMod 4)) = 2 := by
  rw [wallis_prime_factor_eq 3 (by decide) ⟨1, by decide⟩,
    ZMod.χ₄_nat_three_mod_four (by decide : 3 % 4 = 3)]
  norm_num

example :
    (((5 : ℕ) : ℝ) - ZMod.χ₄ ((5 : ℕ) : ZMod 4)) /
      (((5 : ℕ) : ℝ) + ZMod.χ₄ ((5 : ℕ) : ZMod 4)) = 2 / 3 := by
  rw [wallis_prime_factor_eq 5 (by decide) ⟨2, by decide⟩,
    ZMod.χ₄_nat_one_mod_four (by decide : 5 % 4 = 1)]
  norm_num
