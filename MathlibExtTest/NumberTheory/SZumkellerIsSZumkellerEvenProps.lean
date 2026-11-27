/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerIsSZumkellerEvenProps
import Mathlib.Tactic.Simproc.Factors

/-! # Tests for properties of even s-Zumkeller numbers -/

namespace MathlibExtTest.NumberTheory.SZumkellerIsSZumkellerEvenProps

open MetaMathlibExt

example : Even (ArithmeticFunction.sigma 2 60) :=
  (isSZumkeller_even_props 60 isSZumkeller_sixty (by decide)).1

/-- `180 = 2² · 3² · 5` is s-Zumkeller: the proper divisors `1, 5, 6, 9, 20, 90` and the other
eleven proper divisors both have squared sum `8643`. -/
private theorem isSZumkeller_oneEighty : IsSZumkeller 180 :=
  ⟨{1, 5, 6, 9, 20, 90}, by decide, by decide, by decide, by decide⟩

-- For `180 = 2² · 3² · 5` the odd prime with an odd exponent must be `5`: the other odd prime
-- factor, `3`, has the even exponent `2`.
example : ∃ p ∈ (180 : ℕ).primeFactors, Odd p ∧ Odd ((180 : ℕ).factorization p) ∧ p = 5 := by
  obtain ⟨p, hp, hodd, hexp⟩ :=
    (isSZumkeller_even_props 180 isSZumkeller_oneEighty (by decide)).2.1
  refine ⟨p, hp, hodd, hexp, ?_⟩
  have hlist : (180 : ℕ).primeFactorsList = [2, 2, 3, 3, 5] := by
    simp only [Nat.primeFactorsList_ofNat]
  have hfactors : (180 : ℕ).primeFactors = {2, 3, 5} := by
    rw [← Nat.toFinset_factors, hlist]
    decide
  rw [← Nat.primeFactorsList_count_eq, hlist] at hexp
  rw [hfactors] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact absurd hodd (by decide)
  · exact absurd hexp (by decide)
  · rfl

example : 5400 ≤ ArithmeticFunction.sigma 2 60 := by
  have := (isSZumkeller_even_props 60 isSZumkeller_sixty (by decide)).2.2
  omega

end MathlibExtTest.NumberTheory.SZumkellerIsSZumkellerEvenProps
