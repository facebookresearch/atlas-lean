/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one.lean` and
`P2M/Sol/S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.Localization.AtPrime.DiscreteValuationRing
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Valuation subrings at height-one primes

At a height-one prime of a Noetherian integrally closed domain, the
localization is a discrete valuation ring, and its image in the fraction
field is a principal ideal valuation subring whose membership is the
usual numerator-denominator criterion.
-/

@[expose] public section

/-- At a height-one prime of a Noetherian integrally closed domain, there
is a principal ideal valuation subring of the fraction field whose
membership is the usual numerator-denominator criterion. -/
theorem IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ V : ValuationSubring K, IsPrincipalIdealRing V ∧ V ≠ ⊤ ∧
      ∀ x : K, x ∈ V ↔
        ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r := by
  classical
  have : IsDiscreteValuationRing (Localization.AtPrime p) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one p hp
  set L := Localization.AtPrime p with hL
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    have hthis : (y : R) = 0 := hinjK (h0.trans (map_zero _).symm)
    exact y.2 (hthis.symm ▸ p.zero_mem)
  let φ : L →+* K := IsLocalization.lift (M := p.primeCompl) hunit
  have hφ_alg : ∀ r : R, φ (algebraMap R L r) = algebraMap R K r :=
    fun r => IsLocalization.lift_eq (M := p.primeCompl) hunit r
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have h1 : φ (IsLocalization.mk' L r s) * algebraMap R K s = algebraMap R K r := by
      rw [← hφ_alg s, ← map_mul, IsLocalization.mk'_spec, hφ_alg]
    rw [hz, zero_mul] at h1
    have hr : r = 0 := hinjK (h1.symm.trans (map_zero _).symm)
    subst hr
    have h2 : IsLocalization.mk' L (0 : R) s * algebraMap R L (s : R) = 0 := by
      rw [IsLocalization.mk'_spec, map_zero]
    exact (IsLocalization.map_units L s).mul_left_eq_zero.mp h2
  let V₀ : Subring K := φ.range
  have hmem : ∀ x : K, x ∈ V₀ ↔
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
      refine ⟨r, s, s.2, ?_⟩
      change φ (IsLocalization.mk' L r s) * algebraMap R K s = algebraMap R K r
      rw [← hφ_alg s, ← map_mul, IsLocalization.mk'_spec, hφ_alg]
    · rintro ⟨r, s, hs, hx⟩
      refine ⟨IsLocalization.mk' L r (⟨s, hs⟩ : p.primeCompl), ?_⟩
      have h1 : φ (IsLocalization.mk' L r (⟨s, hs⟩ : p.primeCompl)) * algebraMap R K s =
          algebraMap R K r := by
        rw [← hφ_alg s, ← map_mul]
        change φ (IsLocalization.mk' L r (⟨s, hs⟩ : p.primeCompl) *
          algebraMap R L ((⟨s, hs⟩ : p.primeCompl) : R)) = _
        rw [IsLocalization.mk'_spec, hφ_alg]
      have hs0 : algebraMap R K s ≠ 0 := (hunit ⟨s, hs⟩).ne_zero
      exact mul_right_cancel₀ hs0 (h1.trans hx.symm)
  have hval : ∀ x : K, x ∈ V₀ ∨ x⁻¹ ∈ V₀ := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : algebraMap R K b ≠ 0 := fun h0 =>
      nonZeroDivisors.ne_zero hb (hinjK (h0.trans (map_zero _).symm))
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap R L a) (algebraMap R L b)
    · by_cases ha0 : algebraMap R K a = 0
      · left
        rw [ha0, zero_div]
        exact V₀.zero_mem
      · right
        refine ⟨c, ?_⟩
        have hthis := congrArg φ hc
        rw [map_mul, hφ_alg, hφ_alg] at hthis
        rw [inv_div, eq_div_iff ha0, mul_comm]
        exact hthis
    · left
      refine ⟨c, ?_⟩
      have hthis := congrArg φ hc
      rw [map_mul, hφ_alg, hφ_alg] at hthis
      rw [eq_div_iff hb0, mul_comm]
      exact hthis
  let V : ValuationSubring K := ⟨V₀, hval⟩
  have hVmem : ∀ x : K, x ∈ V ↔ x ∈ V₀ := fun x => Iff.rfl
  refine ⟨V, ?_, ?_, fun x => (hVmem x).trans (hmem x)⟩
  · have hsurj : Function.Surjective (φ.rangeRestrict) := φ.rangeRestrict_surjective
    have hthis : IsPrincipalIdealRing V₀ := IsPrincipalIdealRing.of_surjective φ.rangeRestrict hsurj
    exact hthis
  · have hp0 : p ≠ ⊥ := by
      rintro rfl
      apply IsDiscreteValuationRing.not_a_field' (R := L)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
    obtain ⟨c, hcp, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    intro htop
    have hcK : algebraMap R K c ≠ 0 := fun h0 => hc0 (hinjK (h0.trans (map_zero _).symm))
    have hmemc : (algebraMap R K c)⁻¹ ∈ V := by
      rw [htop]
      exact ValuationSubring.mem_top _
    rw [hVmem, hmem] at hmemc
    obtain ⟨r, s, hs, hrs⟩ := hmemc
    apply hs
    have hsc : s = c * r := by
      apply hinjK
      rw [map_mul, ← hrs, ← mul_assoc, mul_inv_cancel₀ hcK, one_mul]
    rw [hsc]
    exact p.mul_mem_right r hcp
