/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSumNotIsEulerPrimeOfMod165Eq
namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MetaMathlibExt

example (n : ℕ) : ¬ IsEulerPrime n 164 :=
  not_isEulerPrime_of_mod_165_eq n 164 (by decide)

example (n : ℕ) : ¬ IsEulerPrime n 329 :=
  not_isEulerPrime_of_mod_165_eq n 329 (by decide)

theorem mod_165_ne_of_isEulerPrime {n q : ℕ} (h : IsEulerPrime n q) : q % 165 ≠ 164 :=
  fun heq => not_isEulerPrime_of_mod_165_eq n q heq h

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
