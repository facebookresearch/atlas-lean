/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentities
import Mathlib.Tactic.NormNum

open MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted

-- At zero the first derivative counts the three transpositions with negative sign.
example :
    (∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      Fintype.card (Function.fixedPoints σ) * 0 ^ (Fintype.card (Function.fixedPoints σ) - 1)) =
      -3 := by
  have h := sum_perm_sign_falling_fixedPoints_mul_pow 3 1 (by decide) (by decide) (by decide) 0
  norm_num [Nat.factorial, Finset.prod_range_succ] at h
  exact h

-- At one the extreme derivative order k = n - 1 gives n!, including the zero exponent.
example :
    (∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ((Fintype.card (Function.fixedPoints σ) : ℝ) *
        (Fintype.card (Function.fixedPoints σ) - (1 : ℝ)))) = 6 := by
  have h := sum_perm_sign_falling_fixedPoints_mul_pow 3 2 (by decide) (by decide) (by decide) 1
  norm_num [Nat.factorial, Finset.prod_range_succ] at h
  exact h
