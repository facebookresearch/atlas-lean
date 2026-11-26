/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DucciSequence

open MathlibExt.NumberTheory.DucciWanted

-- The range starts at zero even for the smallest exponent.
example : (Nat.choose 4 0 : ZMod 5) = 1 :=
  (choose_prime_pow_sub_one_mod 5 1 0 (by decide) (by decide) (by decide)).trans (pow_zero _)

-- An odd interior index can itself be divisible by the modulus.
example : (Nat.choose 8 3 : ZMod 3) = -1 :=
  (choose_prime_pow_sub_one_mod 3 2 3 (by decide) (by decide) (by decide)).trans (by decide)

-- At the upper endpoint for p = 2 the odd power of -1 has residue one.
example : (Nat.choose 7 7 : ZMod 2) = 1 :=
  (choose_prime_pow_sub_one_mod 2 3 7 (by decide) (by decide) (by decide)).trans (by decide)

-- The endpoints of the first admissible row both have residue one.
example : (Nat.choose 6 0 : ZMod 3) = 1 :=
  (choose_prime_pow_sub_mod 3 2 0 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

example : (Nat.choose 6 6 : ZMod 3) = 1 :=
  (choose_prime_pow_sub_mod 3 2 6 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- With k = 3, divisibility by p alone does not give a nonzero residue.
example : (Nat.choose 18 3 : ZMod 3) = 0 :=
  (choose_prime_pow_sub_mod 3 3 3 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

example : (Nat.choose 18 9 : ZMod 3) = -1 :=
  (choose_prime_pow_sub_mod 3 3 9 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- Three different indices contribute to the same cyclic coefficient.
example : ducciCoeff 2 4 1 = 1 + 6 + 1 := by decide

-- The alternating sum 4 - 0 + 2 - 0 vanishes modulo six.
example : ∃ y : Fin 4 → ZMod 6, ducciMap 6 4 y = ![4, 0, 2, 0] := by
  obtain ⟨y, hy⟩ := (ducci_pred_iff 6 4 (by decide) ![4, 0, 2, 0]).2 (by decide)
  exact ⟨y, funext hy⟩

-- At modulus zero the alternating sum is an integer, even at the smallest admissible length.
example : ¬ ∃ y : Fin 2 → ZMod 0, ducciMap 0 2 y = ![1, -1] := by
  rintro ⟨y, hy⟩
  have h := (ducci_pred_iff 0 2 (by decide) ![1, -1]).1 ⟨y, congrFun hy⟩
  exact (by decide : ¬ ∑ i : Fin 2, (-1 : ZMod 0) ^ i.val * ![1, -1] i = 0) h
