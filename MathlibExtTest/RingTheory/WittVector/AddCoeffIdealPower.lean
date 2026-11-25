/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.WittVector.AddCoeffIdealPower

@[expose] public section

universe u

private theorem exactSource
    (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] (I : Ideal R) (c : ℕ)
    (x y : WittVector p R) (hx : ∀ i : ℕ, x.coeff i ∈ I)
    (hy : ∀ i : ℕ, y.coeff i ∈ I ^ (p ^ i + c)) (n : ℕ) :
    (x + y).coeff n - x.coeff n ∈ I ^ ((p - 1) * n + 1 + c) :=
  WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow p I c x y hx hy n

-- The same statement in a higher universe, for coefficients in `Type 1`.
example (I : Ideal (ULift.{1} ℤ)) (c : ℕ) (x y : WittVector 2 (ULift.{1} ℤ))
    (hx : ∀ i : ℕ, x.coeff i ∈ I) (hy : ∀ i : ℕ, y.coeff i ∈ I ^ (2 ^ i + c))
    (n : ℕ) :
    (x + y).coeff n - x.coeff n ∈ I ^ ((2 - 1) * n + 1 + c) :=
  WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow 2 I c x y hx hy n

-- Without the hypothesis on the coefficients of `y`, the conclusion can fail
-- already at `n = 0`: here the difference is `1`, which is not in `⊥ ^ 1`.
example :
    ¬ ((0 + WittVector.mk 2 (fun _ => (1 : ℤ))).coeff 0 - (0 : WittVector 2 ℤ).coeff 0 ∈
      (⊥ : Ideal ℤ) ^ ((2 - 1) * 0 + 1 + 0)) := by
  have hcoeff : (WittVector.mk 2 (fun _ => (1 : ℤ))).coeff 0 = 1 := rfl
  rw [pow_one, Ideal.mem_bot]
  simp [hcoeff]
