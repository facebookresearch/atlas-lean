/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.PartitionProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span

/-! # Tests for partition product congruences -/

open MetaMathlibExt

-- The empty partition satisfies the multiplicity condition at every depth.
example {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsDividedPowerIdeal I) (f g : ℕ → A) (hfg : ∀ n, 1 ≤ n → f n - g n ∈ I)
    (l : Nat.Partition 0) (v : ℕ) :
    ∃ c ∈ I, (l.parts.map f).prod - (l.parts.map g).prod = (p : A) ^ v * c :=
  multiset_prod_sub_prod_mem_of_count_dvd hI f g hfg l (by simp)

-- In ℤ/12ℤ the square-zero ideal (6) is killed by 2. The odd parts 1 and 3 have
-- different even multiplicities, so congruence modulo (6) gives equality of the products.
example (f g : ℕ → ZMod 12) (hfg : ∀ n, 1 ≤ n → f n - g n ∈ Ideal.span {6}) :
    f 1 ^ 2 * f 3 ^ 4 = g 1 ^ 2 * g 3 ^ 4 := by
  have hI : IsDividedPowerIdeal (Ideal.span {(6 : ZMod 12)}) := by
    intro a ha k hk
    match k with
    | 0 => omega
    | 1 => exact ⟨a, ha, by simp⟩
    | k + 2 =>
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨0, Ideal.zero_mem _, by simp [pow_add, mul_pow, show (6 : ZMod 12) ^ 2 = 0 by decide]⟩
  let l : Nat.Partition 14 := ⟨Multiset.replicate 2 1 + Multiset.replicate 4 3, by decide, rfl⟩
  obtain ⟨c, hc, heq⟩ := multiset_prod_sub_prod_mem_of_count_dvd (p := 2) (v := 1)
    hI f g hfg l (by decide)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hc
  rw [pow_one, Nat.cast_ofNat, ← mul_assoc, show (2 : ZMod 12) * 6 = 0 by decide, zero_mul] at heq
  simpa only [l, Multiset.map_add, Multiset.map_replicate, Multiset.prod_add,
    Multiset.prod_replicate, sub_eq_zero] using heq
