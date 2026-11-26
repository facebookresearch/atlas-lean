/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn.lean`
and
`P2M/Sol/S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
public import MathlibExt.RingTheory.Valuation.InertiaSubgroupIn
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.GCD

/-!
# Inertia and roots of unity

A valuation subring lies over a rational prime `q` when `q` is a nonunit of
the subring. Its inertia subgroup, viewed inside the full automorphism
group of the field, fixes every root of unity whose order is prime to `q`.
-/

@[expose] public section

open scoped Pointwise

namespace InertiaRootsOfUnity

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private lemma mem_inertiaSubgroupIn_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K,
        (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

private theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc
    σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

private theorem apply_sub_self_mem_nonunits {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) {x : L} (hx : x ∈ A) :
    σ x - x ∈ A.nonunits := by
  obtain ⟨hd, hI⟩ := InertiaRootsOfUnity.mem_inertiaSubgroupIn_iff.mp hσ
  set a : A := ⟨x, hx⟩
  set g : A.decompositionSubgroup K := ⟨σ, hd⟩
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g = 1 := MonoidHom.mem_ker.mp hI
  have happ : (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A a)
      = g • (IsLocalRing.residue A a) := rfl
  have hres : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul, ← happ, hker]
    rfl
  have hmem : g • a - a ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a) = 0 := by
      rw [map_sub, hres, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a : A) : L) = σ x - x := rfl
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hmem
  rwa [hcoe] at h

private theorem mul_mem_nonunits {A : ValuationSubring L} {a b : L}
    (ha : a ∈ A.nonunits) (hb : b ∈ A) :
    a * b ∈ A.nonunits := by
  have ha' : a ∈ A := A.nonunits_subset ha
  have h1 : (⟨a, ha'⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp ha
  have h2 : (⟨a, ha'⟩ * ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.mul_mem_right _ _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

end InertiaRootsOfUnity

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element of the inertia subgroup of a valuation subring fixes every
root of unity whose order is nonzero and is not a nonunit of the subring. -/
public theorem
    ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn_of_not_mem_nonunits
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {n : ℕ} (hn0 : n ≠ 0) (hnA : (n : L) ∉ A.nonunits)
    {ζ : L} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hσD : σ ∈ A.decompositionSubgroup K :=
    (InertiaRootsOfUnity.mem_inertiaSubgroupIn_iff.mp hσ).1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hζ
    exact zero_ne_one hζ
  have hvζ : A.valuation ζ = 1 := by
    have h : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hn0).mp h
  have hζA : ζ ∈ A := by rw [← ValuationSubring.valuation_le_one_iff, hvζ]
  have hζinvA : ζ⁻¹ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hvζ, inv_one]
  have hσζA : σ ζ ∈ A := (InertiaRootsOfUnity.apply_mem_iff hσD ζ).mpr hζA
  have hηA : σ ζ * ζ⁻¹ ∈ A := A.mul_mem _ _ hσζA hζinvA
  have hηn : (σ ζ * ζ⁻¹) ^ n = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, mul_one]
  have hη1 : σ ζ * ζ⁻¹ - 1 ∈ A.nonunits := by
    have e : σ ζ * ζ⁻¹ - 1 = (σ ζ - ζ) * ζ⁻¹ := by field_simp
    rw [e]
    exact InertiaRootsOfUnity.mul_mem_nonunits
      (InertiaRootsOfUnity.apply_sub_self_mem_nonunits hσ hζA) hζinvA
  set e : A := ⟨σ ζ * ζ⁻¹, hηA⟩ with he
  have hen : e ^ n = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hηn)
  have hres1 : IsLocalRing.residue A e = 1 := by
    rw [← (IsLocalRing.residue A).map_one]
    apply Ideal.Quotient.eq.mpr
    exact ValuationSubring.coe_mem_nonunits_iff.mp hη1
  rcases mul_eq_zero.mp (show (∑ i ∈ Finset.range n, e ^ i) * (e - 1) = 0 by
      rw [geom_sum_mul, hen, sub_self]) with hsum | he1
  · exfalso
    apply hnA
    have hresn : IsLocalRing.residue A (n : A) = 0 := by
      have h := congrArg (IsLocalRing.residue A) hsum
      rw [map_sum, _root_.map_zero] at h
      simp only [map_pow, hres1, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one] at h
      rw [map_natCast]
      exact h
    have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A :=
      Ideal.Quotient.eq_zero_iff_mem.mp hresn
    have h := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
    simpa using h
  · have h1 : σ ζ * ζ⁻¹ = 1 := by
      have h := congrArg (fun t : A => (t : L)) (sub_eq_zero.mp he1)
      simpa [he] using h
    calc
      σ ζ = σ ζ * ζ⁻¹ * ζ := by rw [mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
      _ = ζ := by rw [h1, one_mul]

/-- An element of the inertia subgroup at a place above a prime `q` fixes
every root of unity whose order is not divisible by `q`. -/
public theorem ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
    {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {n : ℕ} (hn : ¬ q ∣ n)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero q)
  refine
    ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn_of_not_mem_nonunits
      hσ hn0 ?_ hζ
  intro hnA
  have hcop : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hn
  have hbez : ((q : ℤ) * Nat.gcdA q n + (n : ℤ) * Nat.gcdB q n : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  have hone : (1 : AlgebraicClosure ℚ) ∈ A.nonunits := by
    have e : (1 : AlgebraicClosure ℚ) =
        (q : AlgebraicClosure ℚ) * (Nat.gcdA q n : ℤ) +
          (n : AlgebraicClosure ℚ) * (Nat.gcdB q n : ℤ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hbez.symm
    rw [e]
    exact A.nonunits.add_mem
      (InertiaRootsOfUnity.mul_mem_nonunits hA (intCast_mem A.toSubring _))
      (InertiaRootsOfUnity.mul_mem_nonunits hnA (intCast_mem A.toSubring _))
  rw [ValuationSubring.mem_nonunits_iff, map_one] at hone
  exact lt_irrefl 1 hone
