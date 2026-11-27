/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerIdeal
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span

/-! # Tests for powers modulo a divided-power ideal -/

open MetaMathlibExt

-- The ideal (2) in ℤ/8ℤ is not square-zero, but squaring lands in twice the ideal.
example : IsDividedPowerIdeal (Ideal.span {(2 : ZMod 8)}) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA (k : ℕ) : ¬ 2 ∣ k → IsUnit (k : ZMod 8) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 3) Nat.prime_two (by decide)).mpr
  apply (isDividedPowerIdeal_iff_pow_prime_mem hA _).mpr
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨b ^ 2 * 2, Ideal.mem_span_singleton'.mpr ⟨b ^ 2, rfl⟩, ?_⟩
  rw [Nat.cast_ofNat]
  ring

-- The whole ring ℤ/2ℤ fails the criterion at 1.
example : ¬ IsDividedPowerIdeal (⊤ : Ideal (ZMod 2)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA (k : ℕ) : ¬ 2 ∣ k → IsUnit (k : ZMod 2) :=
    (CharP.isUnit_natCast_iff Nat.prime_two).mpr
  intro h
  obtain ⟨c, _, hc⟩ := (isDividedPowerIdeal_iff_pow_prime_mem hA ⊤).mp h 1 (by simp)
  simp [show (2 : ZMod 2) = 0 by decide] at hc

-- In characteristic p the prime-power congruence gives equality of p-th powers.
example {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p]
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {x y : A} (hxy : x - y ∈ I) :
    x ^ p = y ^ p := by
  obtain ⟨c, _, hc⟩ := (pow_sub_pow_mem_of_sub_mem
    (fun _ => (CharP.isUnit_natCast_iff hp.out).mpr) hI hxy).1 1
  simpa [CharP.cast_eq_zero A p, sub_eq_zero] using hc

-- In ℤ/4ℤ the ideal (2) is square-zero. Since 2 annihilates the ideal, all even powers
-- agree on x and x + 2, including exponent zero.
example (x : ZMod 4) (n : ℕ) : (x + 2) ^ (2 * n) = x ^ (2 * n) := by
  let I : Ideal (ZMod 4) := Ideal.span {2}
  have hI : IsDividedPowerIdeal I := by
    intro a ha k hk
    match k with
    | 0 => omega
    | 1 => exact ⟨a, ha, by simp⟩
    | k + 2 =>
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact ⟨0, I.zero_mem, by simp [pow_add, mul_pow, show (2 : ZMod 4) ^ 2 = 0 by decide]⟩
  have hxy : (x + 2) - x ∈ I := by simp [I]
  have hA (k : ℕ) : ¬ 2 ∣ k → IsUnit (k : ZMod 4) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 2) Nat.prime_two (by decide)).mpr
  obtain ⟨c, hc, h⟩ := (pow_sub_pow_mem_of_sub_mem hA hI hxy).2 (2 * n)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  apply sub_eq_zero.mp
  rw [h, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = (2 : ZMod 4) ^ 2 * (n * b) := by ring
    _ = 0 := by rw [show (2 : ZMod 4) ^ 2 = 0 by decide, zero_mul]
