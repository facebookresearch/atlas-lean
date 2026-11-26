/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerIsSZumkellerEvenProps

/-! # Tests for properties of even s-Zumkeller numbers -/

namespace MathlibExtTest.NumberTheory.SZumkellerIsSZumkellerEvenProps

open MetaMathlibExt

example : Even (ArithmeticFunction.sigma 2 60) :=
  (isSZumkeller_even_props 60 isSZumkeller_sixty (by decide)).1

example (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    ∃ p, p.Prime ∧ 2 < p ∧ p ∣ n := by
  obtain ⟨p, hp, hodd, _⟩ := (isSZumkeller_even_props n h he).2.1
  have hprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨p, hprime, ?_, Nat.dvd_of_mem_primeFactors hp⟩
  have := hprime.two_le
  have := Nat.odd_iff.mp hodd
  omega

example : 5400 ≤ ArithmeticFunction.sigma 2 60 := by
  have := (isSZumkeller_even_props 60 isSZumkeller_sixty (by decide)).2.2
  omega

end MathlibExtTest.NumberTheory.SZumkellerIsSZumkellerEvenProps
