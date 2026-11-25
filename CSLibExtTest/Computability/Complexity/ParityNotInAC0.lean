/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import all CSLibExt.Computability.Complexity.ParityNotInAC0

/-! # Tests for `CSLibExt.Computability.Complexity.ParityNotInAC0` -/

namespace MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

-- The moved theorem is available with the original statement from the new module alone.
example : parityDec ∉ AC0 := parity_not_in_ac0

-- `AC0` contains every language that depends only on the input length (an existing test), but
-- not parity, so `AC0` is a proper class of decision problems.
example : AC0 ≠ Set.univ := fun h => parity_not_in_ac0 (h ▸ Set.mem_univ _)

-- Parity counts the true entries modulo two, including on the empty word.
example : parityDec [] = false ∧ parityDec [true] = true ∧ parityDec [true, false, true] = false :=
  by decide

-- In the `±1` basis over `ZMod 3`, parity is the full character `χ_univ`.
example : chi Finset.univ ![true, false, true] = 1 ∧ chi Finset.univ ![true, true, true] = -1 :=
  by decide

-- Razborov's OR approximation with one set: on three true inputs of an OR gate, a set meeting
-- all three of them sees a multiple of three and the approximation fails (it outputs `0`, while
-- the OR is true); a set meeting two of them gives the correct value `1`.
example : orApprox (fun _ : Fin 1 => ({0, 1, 2} : Finset ℕ)) {0, 1, 2} (fun _ => 1) = 0 := by
  decide
example : orApprox (fun _ : Fin 1 => ({0, 1} : Finset ℕ)) {0, 1, 2} (fun _ => 1) = 1 := by
  decide

-- The failure bound is sharp: for `T = {0}` inside `U = {0, 1, 2}`, exactly half of the eight
-- subsets of `U` meet `T` in a multiple of three elements.
example : 2 * (({0, 1, 2} : Finset ℕ).powerset.filter
    fun S => (({0} : Finset ℕ) ∩ S).card % 3 = 0).card ≤ 2 ^ ({0, 1, 2} : Finset ℕ).card :=
  two_mul_card_bad_le {0, 1, 2} {0} (by decide) ⟨0, by simp⟩
example : (({0, 1, 2} : Finset ℕ).powerset.filter
    fun S => (({0} : Finset ℕ) ∩ S).card % 3 = 0).card = 4 := by
  decide

-- The central binomial estimate `C(2m, m)² (2m + 1) ≤ 16 ^ m` at `m = 3`: `20² · 7 ≤ 16³`.
example : (3 : ℕ).centralBinom ^ 2 * (2 * 3 + 1) ≤ 16 ^ 3 := centralBinom_sq_mul_le 3

-- With `m = 8` and degree `D = 0`, subsets of size at most `8` of a 16-element set are fewer
-- than three quarters of all subsets.
example : 4 * (Finset.univ.filter fun I : Finset (Fin (2 * 8)) => I.card ≤ 8 + 0).card <
    3 * 4 ^ 8 :=
  four_mul_card_small_lt 8 0 (by norm_num)

-- Smolensky's bound for the constant function `0` on two variables: it never agrees with the
-- character `χ_univ`, whose values are `±1`.
example : (Finset.univ.filter fun x : Fin 2 → Bool =>
    (0 : (Fin 2 → Bool) → ZMod 3) x = chi Finset.univ x).card ≤
    (Finset.univ.filter fun I : Finset (Fin 2) => I.card ≤ 2 / 2 + 0).card :=
  card_agree_le 0 (Submodule.zero_mem _)

end MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0
