/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

/-!
# Wieferich primes to base two

A prime `p` is Wieferich to base two when `p ^ 2` divides `2 ^ (p - 1) - 1`.

## References

* Olivier Rozier, *Are the Collatz and abc conjectures related?*, arXiv:2306.15284v2
-/

namespace Nat

/-- **Wieferich primes.** A natural number $p$ is a Wieferich prime (to base $2$) if $p$ is
prime and $p^2$ divides $2^{p-1} - 1$. -/
def IsWieferichPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

instance decidableIsWieferichPrime (p : ℕ) : Decidable p.IsWieferichPrime := by
  unfold IsWieferichPrime
  infer_instance

/-- **Wieferich primes via congruences.** For every natural number $p$, $p$ is a Wieferich prime
if and only if $p$ is prime and $2^{p-1} \equiv 1 \pmod{p^2}$. -/
theorem isWieferichPrime_iff_modEq (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  rw [IsWieferichPrime, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (Nat.one_le_pow (p - 1) 2 (by decide))]

/-- **Wieferich primes via remainders.** For every natural number $p$, $p$ is a Wieferich prime
if and only if $p$ is prime and the remainder of $2^{p-1}$ on division by $p^2$ is $1$. -/
theorem isWieferichPrime_iff_mod (p : ℕ) :
    p.IsWieferichPrime ↔ p.Prime ∧ 2 ^ (p - 1) % (p ^ 2) = 1 := by
  rw [isWieferichPrime_iff_modEq, Nat.ModEq]
  constructor
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩
  · rintro ⟨hp, h⟩
    have hp_sq : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    exact ⟨hp, by simpa [Nat.mod_eq_of_lt hp_sq] using h⟩

end Nat
