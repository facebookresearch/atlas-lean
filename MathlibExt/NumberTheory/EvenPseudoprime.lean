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

/-- **Even pseudoprime.** A natural number $N$ is an even pseudoprime if $N$ is even, $N > 2$
and $2^N \equiv 2 \pmod{N}$. -/
def IsEvenPseudoprime (N : ℕ) : Prop :=
  Even N ∧ 2 < N ∧ 2 ^ N ≡ 2 [MOD N]

/-- **The set of even pseudoprimes.** The set of even pseudoprimes is the set of natural
numbers $N$ such that $N$ is even, $N > 2$ and $2^N \equiv 2 \pmod{N}$. -/
def evenPseudoprimes : Set ℕ :=
  {N | IsEvenPseudoprime N}

@[simp]
theorem mem_evenPseudoprimes {N : ℕ} :
    N ∈ evenPseudoprimes ↔ IsEvenPseudoprime N :=
  Iff.rfl

/-- **Even pseudoprimes are even.** Every even pseudoprime $N$ is an even natural number. -/
theorem IsEvenPseudoprime.even {N : ℕ} (h : IsEvenPseudoprime N) :
    Even N :=
  h.1

/-- **Even pseudoprimes exceed two.** Every even pseudoprime $N$ satisfies $N > 2$. -/
theorem IsEvenPseudoprime.two_lt {N : ℕ} (h : IsEvenPseudoprime N) :
    2 < N :=
  h.2.1

/-- **Fermat congruence for even pseudoprimes.** If $N$ is an even pseudoprime, then
$2^N \equiv 2 \pmod{N}$. -/
theorem IsEvenPseudoprime.modeq {N : ℕ} (h : IsEvenPseudoprime N) :
    2 ^ N ≡ 2 [MOD N] :=
  h.2.2

/-- **Even pseudoprimes are not prime.** No even pseudoprime is a prime number: the only even
prime is $2$, and every even pseudoprime is greater than $2$. -/
theorem IsEvenPseudoprime.not_prime {N : ℕ} (h : IsEvenPseudoprime N) :
    ¬ Nat.Prime N := by
  intro hp
  rcases hp.eq_two_or_odd' with htwo | hodd
  · have hN : 2 < N := h.two_lt
    omega
  · exact (Nat.not_odd_iff_even.mpr h.even) hodd

end MathlibExt.NumberTheory
