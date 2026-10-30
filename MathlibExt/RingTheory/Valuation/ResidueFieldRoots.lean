/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat.lean`,
`P2M/Sol/S_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat.lean`,
`Theorems/Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_
of_isAlgClosed.lean` and
`P2M/Sol/S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Residue fields of valuation subrings

The residue field of a valuation subring of an algebraic extension of `ℚ`
is algebraic over `𝔽_p`, and roots of unity lift uniquely from the residue
field when the order is prime to the residue characteristic: the residue
map is injective on `m`-th roots of unity and every `m`-th root of unity
in the residue field lifts.
-/

@[expose] public section

open IsLocalRing

/-- The residue field of a valuation subring of an algebraic extension of
`ℚ` is algebraic over `𝔽_p`. -/
theorem ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := by
  classical
  have hp : p.Prime := Fact.out
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  refine ⟨fun r => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  have ha : IsAlgebraic ℤ ((a : ↥A) : K) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨P, hP0, hPa⟩ := ha
  have hQprim : P.primPart.IsPrimitive := P.isPrimitive_primPart
  have hQa : Polynomial.aeval ((a : ↥A) : K) P.primPart = 0 :=
    Polynomial.aeval_primPart_eq_zero hP0 hPa
  have hQaA : Polynomial.aeval (a : ↥A) P.primPart = 0 := by
    have h1 : Polynomial.aeval (algebraMap (↥A) K a) P.primPart =
        algebraMap (↥A) K (Polynomial.aeval a P.primPart) :=
      Polynomial.aeval_algebraMap_apply K a P.primPart
    have h2 : algebraMap (↥A) K (Polynomial.aeval a P.primPart) = 0 := by
      rw [← h1]; exact hQa
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (↥A) K)).mp h2
  have hres : Polynomial.aeval (IsLocalRing.residue (↥A) a)
      (P.primPart.map (algebraMap ℤ (ZMod p))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)).comp
        (algebraMap ℤ (ZMod p))) (algebraMap ℤ _),
      ← Polynomial.aeval_def]
    have hthis := Polynomial.aeval_algHom_apply ((IsLocalRing.residue ↥A).toIntAlgHom) a P.primPart
    rw [RingHom.toIntAlgHom_apply] at hthis
    exact hthis.trans (by rw [hQaA, map_zero])
  have hne : P.primPart.map (algebraMap ℤ (ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ P.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have hn := congrArg (fun q => q.coeff n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, algebraMap_int_eq,
        Int.coe_castRingHom] at hn
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := hp.two_le
    omega
  exact ⟨P.primPart.map (algebraMap ℤ (ZMod p)), hne, hres⟩

namespace TeichmullerAux

private theorem eq_one_of_pow_eq_one_of_residue_eq_one {R : Type*} [CommRing R]
    [IsLocalRing R] {m : ℕ} (hm : (m : ResidueField R) ≠ 0) {ζ : R} (hζ : ζ ^ m = 1)
    (h1 : residue R ζ = 1) : ζ = 1 := by
  have hgeom : (∑ i ∈ Finset.range m, ζ ^ i) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hζ, sub_self]
  have hunit : IsUnit (∑ i ∈ Finset.range m, ζ ^ i) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact hm
  have hthis := hunit.mul_left_cancel (hgeom.trans (mul_zero _).symm)
  exact sub_eq_zero.mp hthis

private theorem eq_of_pow_eq_one_of_residue_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {m : ℕ} (hm : (m : ResidueField R) ≠ 0) {ζ₁ ζ₂ : R} (h₁ : ζ₁ ^ m = 1) (h₂ : ζ₂ ^ m = 1)
    (h : residue R ζ₁ = residue R ζ₂) : ζ₁ = ζ₂ := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one h₂ hm0
  have hu : u ^ m = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h₂)
  have hz : (ζ₁ * ↑u⁻¹) ^ m = 1 := by
    rw [mul_pow, h₁, one_mul, ← Units.val_pow_eq_pow_val, inv_pow, hu, inv_one, Units.val_one]
  have hres : residue R (ζ₁ * ↑u⁻¹) = 1 := by
    rw [map_mul, h, ← map_mul, Units.mul_inv, map_one]
  have hthis := eq_one_of_pow_eq_one_of_residue_eq_one hm hz hres
  calc ζ₁ = ζ₁ * ↑u⁻¹ * ↑u := by rw [Units.inv_mul_cancel_right]
    _ = ↑u := by rw [hthis, one_mul]

end TeichmullerAux

/-- The residue map is injective on `m`-th roots of unity, and every `m`-th
root of unity in the residue field lifts, when `m` is nonzero in the
residue field. -/
theorem ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (m : ℕ) (hm : (m : ResidueField ↥A) ≠ 0) :
    (∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂) ∧
    (∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u) := by
  have hinj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ →
      ζ₁ = ζ₂ :=
    fun _ _ h₁ h₂ h => TeichmullerAux.eq_of_pow_eq_one_of_residue_eq hm h₁ h₂ h
  refine ⟨hinj, fun u hu => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have : NeZero m := ⟨hm0⟩
  have hmK : (m : K) ≠ 0 := by
    intro h0
    apply hm
    have hA : (m : ↥A) = 0 := by
      apply Subtype.ext
      simpa using h0
    rw [← map_natCast (residue ↥A), hA, map_zero]
  have : NeZero (m : K) := ⟨hmK⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos m K (Nat.pos_of_ne_zero hm0)))
  have hζ₀ : IsPrimitiveRoot ζ₀ m := Polynomial.isRoot_cyclotomic_iff.mp hζ₀
  have hζ₀A : ζ₀ ∈ A := by
    rw [← A.valuation_le_one_iff]
    have hpow : A.valuation ζ₀ ^ m = 1 := by rw [← map_pow, hζ₀.pow_eq_one, map_one]
    exact ((pow_eq_one_iff.mp hpow).resolve_right hm0).le
  set ζA : ↥A := ⟨ζ₀, hζ₀A⟩ with hζA
  have hζAm : ζA ^ m = 1 := Subtype.ext (by simp [hζA, hζ₀.pow_eq_one])
  have hprim : IsPrimitiveRoot (residue ↥A ζA) m := by
    refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hm0) ?_ fun l hl0 hlm => ?_
    · rw [← map_pow, hζAm, map_one]
    · intro hl
      have hζl : ζA ^ l = 1 := by
        refine hinj _ _ ?_ (one_pow m) (by rwa [map_pow, map_one])
        rw [← pow_mul, mul_comm, pow_mul, hζAm, one_pow]
      have hthis : ζ₀ ^ l = 1 := by
        have hcongr := congrArg Subtype.val hζl
        simpa [hζA] using hcongr
      exact hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hlm hthis
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hu
  refine ⟨ζA ^ k, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζAm, one_pow]
  · rw [map_pow, hk]
