/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EvenPseudoprime

open MathlibExt.NumberTheory

#check @MathlibExt.NumberTheory.IsEvenPseudoprime
#check @MathlibExt.NumberTheory.evenPseudoprimes
#check @MathlibExt.NumberTheory.mem_evenPseudoprimes
#check @MathlibExt.NumberTheory.IsEvenPseudoprime.not_prime

example : ¬ IsEvenPseudoprime 2 := by
  intro h
  exact lt_irrefl 2 h.two_lt

example : ¬ IsEvenPseudoprime 9 := by
  intro h
  rcases h.even with ⟨k, hk⟩
  omega

example : ¬ IsEvenPseudoprime 4 := by
  intro h
  have hnot : ¬ (2 ^ 4 ≡ 2 [MOD 4]) := by decide
  exact hnot h.modeq

example {N : ℕ} (h : IsEvenPseudoprime N) : N ∈ evenPseudoprimes :=
  mem_evenPseudoprimes.mpr h

example {N : ℕ} (h : IsEvenPseudoprime N) : ¬ Nat.Prime N :=
  h.not_prime

example {N : ℕ} (h : IsEvenPseudoprime N) :
    Even N ∧ 2 < N ∧ 2 ^ N ≡ 2 [MOD N] :=
  ⟨h.even, h.two_lt, h.modeq⟩
