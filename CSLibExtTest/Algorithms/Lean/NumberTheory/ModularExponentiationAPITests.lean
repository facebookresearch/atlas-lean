/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.ModularExponentiation

/-!
# Ordinary-import recursive modular exponentiation API

This consumer checks the ordinary public interface. The recursive child-count
construction is private proof scaffolding, not a second public recursion.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ModularExponentiationAPITests

open Cslib.Algorithms.Lean.ModularExponentiation

#check @modularExponentiation
#check @modularExponentiation_zero
#check @modularExponentiation_even
#check @modularExponentiation_odd
#check @modularExponentiation_ret_zero
#check @modularExponentiation_time_zero
#check @modularExponentiation_ret_even
#check @modularExponentiation_time_even
#check @modularExponentiation_ret_odd
#check @modularExponentiation_time_odd
#check @modularExponentiation_ret_mod
#check @modularExponentiation_ret_mod_base
#check @modularExponentiation_ret_is_reduced
#check @modularExponentiation_correct
#check @modularExponentiation_lt
#check @modularExponentiation_is_leastResidue
#check @modularExponentiation_zero_is_leastResidue
#check @modularExponentiation_zero_modulus_one
#check @modularExponentiation_time_independent
#check @modularExponentiation_time_bounds

example (a b n : Nat) (hn : 0 < n) :
    (modularExponentiation a b n).ret % n = a ^ b % n :=
  modularExponentiation_ret_mod a b n hn

example (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret = a ^ b % n :=
  modularExponentiation_correct a b n hb hn

example (a n : Nat) : modularExponentiation a 0 n = ⟨1, 0⟩ :=
  modularExponentiation_zero a n

example (a : Nat) : (modularExponentiation a 0 1).ret = 1 ∧ a ^ 0 % 1 = 0 :=
  modularExponentiation_zero_modulus_one a

example (a b n : Nat) (hb : 0 < b) :
    let β := Nat.log2 b + 1
    β ≤ (modularExponentiation a b n).time ∧
      (modularExponentiation a b n).time ≤ 2 * β - 1 :=
  modularExponentiation_time_bounds a b n hb

example (a a' b n n' : Nat) :
    (modularExponentiation a b n).time = (modularExponentiation a' b n').time :=
  modularExponentiation_time_independent a a' b n n'

end Cslib.Algorithms.Lean.ModularExponentiationAPITests
