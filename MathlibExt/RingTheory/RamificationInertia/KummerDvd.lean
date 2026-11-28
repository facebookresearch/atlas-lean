/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime.lean`
and
`P2M/Sol/S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

/-- Let `ϖ` be a uniformizer of a discrete valuation ring `O` and `u` a unit of `O`, let `R`
be a Dedekind domain with an `O`-algebra structure, `E` its fraction field, and `𝔓` a
nonzero prime of `R` lying over the maximal ideal of `O`. If `a ∈ E` satisfies
`a ^ n = u * ϖ ^ m` in `E`, with `m ∈ ℤ` coprime to the positive integer `n`, then `n`
divides the ramification index of `𝔓` over the maximal ideal of `O`. -/
theorem Ideal.dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra O R]
    {E : Type*} [Field E] [Algebra R E] [IsFractionRing R E] [Algebra O E]
    [IsScalarTower O R E]
    (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (m : ℤ) (n : ℕ) (hn : 0 < n)
    (hmn : IsCoprime m (n : ℤ))
    (a : E) (hab : a ^ n = algebraMap O E (u : O) * algebraMap O E ϖ ^ m)
    (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥)
    [𝔓.LiesOver (IsLocalRing.maximalIdeal O)] :
    n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 := by
  classical
  have hmap : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) =
      Ideal.span {algebraMap O R ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  by_cases hϖR : algebraMap O R ϖ = 0
  · have hbot : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) = ⊥ := by
      rw [hmap, Ideal.span_singleton_eq_bot]
      exact hϖR
    have h0 : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = 0 :=
      Ideal.ramificationIdx'_eq_zero fun k =>
        ⟨k + 1, by rw [hbot]; exact bot_le, Nat.lt_succ_self k⟩
    rw [h0]
    exact dvd_zero n
  let v : IsDedekindDomain.HeightOneSpectrum R := ⟨𝔓, inferInstance, h𝔓⟩
  let val := IsDedekindDomain.HeightOneSpectrum.valuation E v
  have hne : v.intValuation (algebraMap O R ϖ) ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hϖR
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (algebraMap O R ϖ) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  have hk0 : k ≤ 0 := by
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v (algebraMap O R ϖ)
    rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = -(t : ℤ) := ⟨(-k).toNat, by omega⟩
  have he : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = t := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap]
      exact Ideal.dvd_iff_le.mp
        ((v.intValuation_le_pow_iff_dvd _ t).mp (le_of_eq hk))
    · rw [hmap]
      intro hle
      have h2 := (v.intValuation_le_pow_iff_dvd _ (t + 1)).mpr
        (Ideal.dvd_iff_le.mpr hle)
      rw [hk, WithZero.exp_le_exp] at h2
      omega
  have hvϖ : val (algebraMap O E ϖ) = WithZero.exp (-(t : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply O R E,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hk]
  have hvu : val (algebraMap O E (u : O)) = 1 := by
    rw [IsScalarTower.algebraMap_apply O R E,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro hmem
    have hu𝔪 : (u : O) ∈ IsLocalRing.maximalIdeal O :=
      (Ideal.mem_of_liesOver 𝔓 _ (u : O)).mpr hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hu𝔪 u.isUnit
  have hva : val a ^ n = WithZero.exp (-(t : ℤ)) ^ m := by
    have h := congrArg val hab
    rwa [map_pow, map_mul, map_zpow₀, hvu, one_mul, hvϖ] at h
  have ha0 : val a ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne', ← WithZero.exp_zsmul] at hva
    exact WithZero.exp_ne_zero hva.symm
  obtain ⟨ka, hka⟩ : ∃ ka : ℤ, val a = WithZero.exp ka :=
    ⟨_, (WithZero.exp_log ha0).symm⟩
  rw [hka, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, WithZero.exp_inj,
    nsmul_eq_mul, smul_eq_mul] at hva
  have hdvd : (n : ℤ) ∣ m * (t : ℤ) := ⟨-ka, by linarith⟩
  have hnt : (n : ℤ) ∣ (t : ℤ) := hmn.symm.dvd_of_dvd_mul_left hdvd
  rw [he]
  exact Int.natCast_dvd_natCast.mp hnt
