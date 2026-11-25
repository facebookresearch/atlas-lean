/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Basic

/-!
# Wieferich primes to base `a` via multiplicative orders

A prime `p` that does not divide a natural number `a` is a Wieferich prime to base `a` when
`a ^ (p - 1) ≡ 1 [MOD p ^ 2]`. This holds exactly when the multiplicative order of `a` modulo
`p ^ 2` equals its multiplicative order modulo `p`
(`MetaMathlibExt.pow_sub_one_modEq_one_sq_iff_orderOf_eq`).

## Proof outline

Write `d` and `D` for the orders of `a` modulo `p` and modulo `p ^ 2`.

* Reduction modulo `p` is a ring homomorphism `ZMod (p ^ 2) →+* ZMod p` that sends the class of
  `a` to the class of `a`, so `d ∣ D`.
* Since `p ∣ a ^ d - 1`, Mathlib's `dvd_sub_pow_of_dvd_sub` gives `p ^ 2 ∣ (a ^ d) ^ p - 1`, so
  `D ∣ d * p`.
* The congruence `a ^ (p - 1) ≡ 1 [MOD p ^ 2]` says `D ∣ p - 1`, and Fermat's little theorem
  gives `d ∣ p - 1`.

If `D ∣ p - 1`, then `D` is coprime to `p`, so `D ∣ d * p` gives `D ∣ d`, and `D = d`.
Conversely, if `D = d`, then `D ∣ p - 1`.

The hypothesis that `p` does not divide `a` is needed: for `a = p = 3`, both orders are `0` (the
classes of `3` are not units), while `3 ^ 2 ≡ 1 [MOD 9]` fails.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Wieferich primes to base $a$ via multiplicative orders.** Let $p$ be a prime and $a$ a
natural number not divisible by $p$. Then $a^{p-1} \equiv 1 \pmod{p^2}$, that is, $p$ is a
Wieferich prime to base $a$, if and only if the multiplicative order of $a$ modulo $p^2$ equals
the multiplicative order of $a$ modulo $p$.

The congruence $a^{p-1} \equiv 1 \pmod{p^2}$ is the source's equation (8) defining $p \in W(a)$.
The source assumes $a \ge 2$; both sides also hold for $a = 1$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 1 (iii) (`integers-2026-A77-lem-1`). -/
theorem pow_sub_one_modEq_one_sq_iff_orderOf_eq {a p : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p ^ 2] ↔ orderOf (a : ZMod (p ^ 2)) = orderOf (a : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  -- The congruence says that the order of `a` modulo `p ^ 2` divides `p - 1`.
  have hcong : a ^ (p - 1) ≡ 1 [MOD p ^ 2] ↔ orderOf (a : ZMod (p ^ 2)) ∣ p - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
  -- Reduction modulo `p` sends the class of `a` modulo `p ^ 2` to the class of `a` modulo `p`.
  have hdvd : orderOf (a : ZMod p) ∣ orderOf (a : ZMod (p ^ 2)) := by
    simpa using orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)).toMonoidHom (a : ZMod (p ^ 2))
  -- From `a ^ d ≡ 1 [MOD p]` with `d` the order modulo `p`, `a ^ (d * p) ≡ 1 [MOD p ^ 2]`.
  have hdvd_mul : orderOf (a : ZMod (p ^ 2)) ∣ orderOf (a : ZMod p) * p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h₁ : (p : ℤ) ∣ (a : ℤ) ^ orderOf (a : ZMod p) - 1 := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      exact (pow_orderOf_eq_one _).symm
    have h₂ := dvd_sub_pow_of_dvd_sub h₁ 1
    rw [pow_one, one_pow, ← pow_mul] at h₂
    have h₃ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mpr (by exact_mod_cast h₂)
    push_cast at h₃
    exact sub_eq_zero.mp h₃
  -- Fermat's little theorem: the order of `a` modulo `p` divides `p - 1`.
  have hfermat : orderOf (a : ZMod p) ∣ p - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    apply ZMod.pow_card_sub_one_eq_one
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  rw [hcong]
  constructor
  · intro h
    have hcop : Nat.Coprime (orderOf (a : ZMod (p ^ 2))) p :=
      Nat.Coprime.coprime_dvd_left h
        ((Nat.coprime_self_sub_left hp.one_lt.le).mpr (Nat.coprime_one_left p))
    exact Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right hdvd_mul) hdvd
  · intro h
    exact h ▸ hfermat

end MetaMathlibExt
