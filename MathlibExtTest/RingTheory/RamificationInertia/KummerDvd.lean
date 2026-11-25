/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.RamificationInertia.KummerDvd

@[expose] public section

private theorem exactSource
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra O R]
    {E : Type*} [Field E] [Algebra R E] [IsFractionRing R E] [Algebra O E]
    [IsScalarTower O R E]
    (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (m : ℤ) (n : ℕ) (hn : 0 < n)
    (hmn : IsCoprime m (n : ℤ))
    (a : E) (hab : a ^ n = algebraMap O E (u : O) * algebraMap O E ϖ ^ m)
    (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥)
    [𝔓.LiesOver (IsLocalRing.maximalIdeal O)] :
    n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 :=
  Ideal.dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
    ϖ hϖ u m n hn hmn a hab 𝔓 h𝔓

/-- The coprimality hypothesis matters: with `n = 2` and `m = 2` the
conclusion would assert `2 ∣ ramification index` from a square relation
alone, which the coprime case excludes. This records the boundary at the
level of the arithmetic hypothesis. -/
example : ¬ IsCoprime (2 : ℤ) (2 : ℤ) := by decide
