/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: reused CSLib's canonical polynomial-growth predicate, proved its
equivalence with the source's one-constant bound, and ported the source closure calculus.
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Closure properties of polynomial bounds

This module extends `Cslib.PolynomiallyBounded` with a normalized witness in which one natural
number is both coefficient and exponent, and with closure under constants, identity, addition,
multiplication, fixed powers, and composition. It also records that the normalized bounding
function is itself polynomially bounded and monotone.

Adapted from `eth/proof/machines/ToTuring/Bound.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The source's predicate `PB f := ∃ c, ∀ n, f n ≤ c * (n + 1) ^ c` is not copied: the first
theorem proves that it is exactly CSLib's canonical `PolynomiallyBounded f`. This is only a
numeric growth condition and makes no computability or running-time claim.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Cslib

/-- Polynomial growth is equivalent to a global bound whose coefficient equals its exponent. -/
theorem polynomiallyBounded_iff_le_mul_pow_self {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c : ℕ, ∀ n, f n ≤ c * (n + 1) ^ c := by
  rw [polynomiallyBounded_iff_le]
  constructor
  · rintro ⟨a, d, h⟩
    refine ⟨max a d, fun n ↦ (h n).trans ?_⟩
    exact Nat.mul_le_mul (Nat.le_max_left _ _)
      (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right _ _))
  · rintro ⟨c, h⟩
    exact ⟨c, c, h⟩

namespace PolynomiallyBounded

variable {f g : ℕ → ℕ}

/-- Increasing the coefficient and exponent increases a normalized polynomial bound. -/
private theorem bound_le {a b a' b' n : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    a * (n + 1) ^ b ≤ a' * (n + 1) ^ b' :=
  Nat.mul_le_mul ha (Nat.pow_le_pow_right (Nat.succ_pos n) hb)

/-- Substituting one normalized polynomial bound into another gives an explicit bound. -/
private theorem bound_comp (c c' n : ℕ) :
    c * (c' * (n + 1) ^ c' + 1) ^ c ≤
      (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by
  have hpow : 1 ≤ (n + 1) ^ c' := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hadd : c' * (n + 1) ^ c' + 1 ≤ (c' + 1) * (n + 1) ^ c' := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left hpow _
  calc
    c * (c' * (n + 1) ^ c' + 1) ^ c ≤
        c * ((c' + 1) * (n + 1) ^ c') ^ c :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left hadd c)
    _ = (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by
      rw [mul_pow, pow_mul, mul_assoc]

/-- Every constant natural-valued function is polynomially bounded. -/
theorem const (a : ℕ) : PolynomiallyBounded (fun _ ↦ a) := by
  apply polynomiallyBounded_iff_le_mul_pow_self.2
  exact ⟨a, fun n ↦ Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos n))⟩

/-- The identity function on natural numbers is polynomially bounded. -/
theorem id : PolynomiallyBounded (fun n ↦ n) := by
  apply polynomiallyBounded_iff_le_mul_pow_self.2
  refine ⟨1, fun n ↦ ?_⟩
  rw [pow_one, Nat.one_mul]
  exact Nat.le_succ n

/-- A pointwise sum of polynomially bounded functions is polynomially bounded. -/
theorem add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f n + g n) := by
  obtain ⟨c, hc⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hf
  obtain ⟨c', hc'⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hg
  apply polynomiallyBounded_iff_le_mul_pow_self.2
  refine ⟨c + c', fun n ↦ ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add
    ((hc n).trans (bound_le le_rfl (Nat.le_add_right _ _)))
    ((hc' n).trans (bound_le le_rfl (Nat.le_add_left _ _)))

/-- A pointwise product of polynomially bounded functions is polynomially bounded. -/
theorem mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f n * g n) := by
  obtain ⟨c, hc⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hf
  obtain ⟨c', hc'⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hg
  apply polynomiallyBounded_iff_le_mul_pow_self.2
  refine ⟨c * c' + (c + c'), fun n ↦ ?_⟩
  calc
    f n * g n ≤ c * (n + 1) ^ c * (c' * (n + 1) ^ c') :=
      Nat.mul_le_mul (hc n) (hc' n)
    _ = c * c' * (n + 1) ^ (c + c') := by
      rw [pow_add]
      ac_rfl
    _ ≤ (c * c' + (c + c')) * (n + 1) ^ (c * c' + (c + c')) :=
      bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- A fixed pointwise power of a polynomially bounded function is polynomially bounded. -/
theorem pow (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun n ↦ f n ^ k) := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

/-- A composition of polynomially bounded functions is polynomially bounded. -/
theorem comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f (g n)) := by
  obtain ⟨c, hc⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hf
  obtain ⟨c', hc'⟩ := polynomiallyBounded_iff_le_mul_pow_self.1 hg
  apply polynomiallyBounded_iff_le_mul_pow_self.2
  refine ⟨c * (c' + 1) ^ c + c' * c, fun n ↦ ?_⟩
  calc
    f (g n) ≤ c * (g n + 1) ^ c := hc _
    _ ≤ c * (c' * (n + 1) ^ c' + 1) ^ c := by
      exact Nat.mul_le_mul_left c <| Nat.pow_le_pow_left (Nat.add_le_add_right (hc' n) 1) c
    _ ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := bound_comp c c' n
    _ ≤ (c * (c' + 1) ^ c + c' * c) *
        (n + 1) ^ (c * (c' + 1) ^ c + c' * c) :=
      bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- The normalized bound is itself polynomially bounded and monotone in its input. -/
theorem mono_bound (c : ℕ) :
    PolynomiallyBounded (fun n ↦ c * (n + 1) ^ c) ∧
      Monotone (fun n ↦ c * (n + 1) ^ c) := by
  exact ⟨polynomiallyBounded_iff_le_mul_pow_self.2 ⟨c, fun _ ↦ le_rfl⟩,
    fun _ _ h ↦ Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) c)⟩

end PolynomiallyBounded

end Cslib
