/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.LaishramRamanujanPrimeBound

/-! # Tests for Laishram's upper bound -/

open MetaMathlibExt

example {R : ℕ} (hR : IsNthRamanujanPrime R 1) : R = 2 := by
  have hlt : R < 5 := by
    simpa only [Nat.reduceMul, Nat.reduceSub, Nat.nth_prime_two_eq_five] using
      laishram_ramanujan_prime_bound 1 R hR
  have h : ∀ p < 5, IsRamanujanPrime p 1 → p = 2 := by
    unfold IsRamanujanPrime
    decide
  exact h R hlt hR.2.1

-- With n = 5 the upper bound and the maximality condition identify R exactly.
example {R : ℕ} (hR : IsNthRamanujanPrime R 5) : R = 41 := by
  have h47 : Nat.nth Nat.Prime 14 = 47 :=
    Nat.nth_count (by decide : Nat.Prime 47)
  have hlt : R < 47 := by
    simpa only [Nat.reduceMul, Nat.reduceSub, h47] using laishram_ramanujan_prime_bound 5 R hR
  have hlo := hR.2.2 41 (by unfold IsRamanujanPrime; decide)
  have h : ∀ p < 47, 41 ≤ p → IsRamanujanPrime p 5 → p = 41 := by
    unfold IsRamanujanPrime
    decide
  exact h R hlt hlo hR.2.1
