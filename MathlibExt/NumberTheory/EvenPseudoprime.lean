/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Even pseudoprimes
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace MathlibExt.NumberTheory

/-- An even pseudoprime is an even natural number `N > 2` satisfying
`2 ^ N ≡ 2 [MOD N]`. -/
def IsEvenPseudoprime (N : ℕ) : Prop :=
  Even N ∧ 2 < N ∧ 2 ^ N ≡ 2 [MOD N]

/-- The set of all even pseudoprimes. -/
def evenPseudoprimes : Set ℕ :=
  {N | IsEvenPseudoprime N}

@[simp]
theorem mem_evenPseudoprimes {N : ℕ} :
    N ∈ evenPseudoprimes ↔ IsEvenPseudoprime N :=
  Iff.rfl

/-- An even pseudoprime is even. -/
theorem IsEvenPseudoprime.even {N : ℕ} (h : IsEvenPseudoprime N) :
    Even N :=
  h.1

/-- An even pseudoprime is greater than `2`. -/
theorem IsEvenPseudoprime.two_lt {N : ℕ} (h : IsEvenPseudoprime N) :
    2 < N :=
  h.2.1

/-- An even pseudoprime satisfies the base-two Fermat congruence. -/
theorem IsEvenPseudoprime.modeq {N : ℕ} (h : IsEvenPseudoprime N) :
    2 ^ N ≡ 2 [MOD N] :=
  h.2.2

/-- An even pseudoprime is not prime: the only even prime is `2`, and an
even pseudoprime is strictly greater than `2`. -/
theorem IsEvenPseudoprime.not_prime {N : ℕ} (h : IsEvenPseudoprime N) :
    ¬ Nat.Prime N := by
  intro hp
  rcases hp.eq_two_or_odd' with htwo | hodd
  · have hN : 2 < N := h.two_lt
    omega
  · exact (Nat.not_odd_iff_even.mpr h.even) hodd

end MathlibExt.NumberTheory
