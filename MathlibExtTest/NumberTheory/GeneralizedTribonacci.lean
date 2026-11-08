/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTribonacci

@[expose] public section

namespace MetaMathlibExt

-- Initial positions with signed parameters.
example : generalizedTribonacci 2 (-3) 5 0 = 2 := rfl
example : generalizedTribonacci 2 (-3) 5 1 = -3 := rfl
example : generalizedTribonacci 2 (-3) 5 2 = 5 := rfl

-- The named equation lemmas recover the initial values generically.
example (a b c : ℤ) : generalizedTribonacci a b c 0 = a :=
  generalizedTribonacci_zero a b c
example (a b c : ℤ) : generalizedTribonacci a b c 1 = b :=
  generalizedTribonacci_one a b c
example (a b c : ℤ) : generalizedTribonacci a b c 2 = c :=
  generalizedTribonacci_two a b c

-- The named recurrence lemma holds generically.
example (a b c : ℤ) (n : ℕ) :
    generalizedTribonacci a b c (n + 3) = generalizedTribonacci a b c (n + 2) +
      generalizedTribonacci a b c (n + 1) + generalizedTribonacci a b c n :=
  generalizedTribonacci_add_three a b c n

-- First recurrence values over `0, 0, 1`: `1, 2, 4`.
example : generalizedTribonacci 0 0 1 3 = 1 := rfl
example : generalizedTribonacci 0 0 1 4 = 2 := rfl
example : generalizedTribonacci 0 0 1 5 = 4 := rfl

-- Signed initial values of the kind arising in Komatsu-type convolution
-- identities, which are unavailable over `ℕ`: `1, -1, 1, 1, 1, 3, …`.
example : generalizedTribonacci 1 (-1) 1 3 = 1 := rfl
example : generalizedTribonacci 1 (-1) 1 4 = 1 := rfl
example : generalizedTribonacci 1 (-1) 1 5 = 3 := rfl

-- Bridges to the existing special-case APIs.
example (n : ℕ) :
    generalizedTribonacci 0 0 1 n = (tribonacci n : ℤ) :=
  generalizedTribonacci_zero_zero_one_eq_tribonacci n
example (n : ℕ) :
    generalizedTribonacci 1 1 1 n = (tribonacciWithInitialValues111 n : ℤ) :=
  generalizedTribonacci_one_one_one_eq_tribonacciWithInitialValues111 n
-- The `0, 1, 1` bridge: ordinary Tribonacci convention up to the index shift.
example (n : ℕ) : generalizedTribonacci 0 1 1 n = (tribonacci (n + 1) : ℤ) :=
  generalizedTribonacci_zero_one_one_eq_tribonacci_succ n
example : generalizedTribonacci 0 1 1 4 = 4 := rfl
example : generalizedTribonacci 1 1 1 5 = 9 := rfl

#print axioms generalizedTribonacci
#print axioms generalizedTribonacci_zero_zero_one_eq_tribonacci
#print axioms generalizedTribonacci_one_one_one_eq_tribonacciWithInitialValues111
#print axioms generalizedTribonacci_zero_one_one_eq_tribonacci_succ

end MetaMathlibExt
