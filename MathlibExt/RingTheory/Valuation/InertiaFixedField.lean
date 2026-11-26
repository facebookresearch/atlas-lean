/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_admissible_smallConstants.lean`,
`P2M/Sol/S_ValuationSubring_exists_admissible_smallConstants.lean`,
and the theorems and solutions they depend on in `Theorems/` and `P2M/Sol/` (files named
`..._exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq`,
`..._isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn`,
`..._henselianLocalRing_comap_fixedField_inertiaSubgroupIn`,
`..._exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq` and
`..._isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn`)
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

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.Valuation.Henselian
import MathlibExt.RingTheory.Valuation.InertiaCyclotomic
import MathlibExt.RingTheory.Valuation.RatCastMem
import MathlibExt.RingTheory.Valuation.ResidueChar
import MathlibExt.RingTheory.Valuation.ResidueField
import MathlibExt.RingTheory.Valuation.ResidueFieldRoots

/-!
# The valuation ring of the inertia fixed field

Let `A` be a valuation subring of `ℚ̄ = AlgebraicClosure ℚ` lying over a prime `q`, and let `k₀`
be the subfield of `ℚ̄` fixed by the inertia subgroup of `A`, with valuation ring
`O = A ∩ k₀`. We prove:

* `ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn`: `O` is a
  discrete valuation ring;
* `ValuationSubring.irreducible_natCast_comap_fixedField_inertiaSubgroupIn`: `q` is a
  uniformizer of `O`;
* `ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn`: for any valuation
  subring of an algebraically closed field, the comap to the inertia fixed field is Henselian;
* `ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq`: every residue
  class of `A` has a representative in `O`;
* `ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn`: the residue
  field of `O` is algebraically closed;
* `ValuationSubring.exists_intermediateField_henselian_dvr_residue_approx`: there is an
  intermediate field `k₀` of `ℚ̄ / ℚ` whose valuation ring is a Henselian discrete valuation ring
  with algebraically closed residue field and through which every residue class of `A` factors.
-/

@[expose] public section

open scoped NumberField Pointwise
open IsLocalRing Polynomial

noncomputable section

namespace ValuationSubring

section Arithmetic

variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem algebraMap_rat_mem_of_den_coprime (hA : A.LiesOverPrime q)
    (r : ℚ) (hr : r.den.Coprime q) : algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hnd : ¬ q ∣ r.den := fun h =>
    (Fact.out : q.Prime).ne_one (Nat.Coprime.eq_one_of_dvd hr.symm h)
  rw [eq_ratCast, ratCast_mem_iff_padicValRat_nonneg A Fact.out
    ((ValuationSubring.mem_nonunits_iff A).mp hA) hr0, padicValRat_def,
    multiplicity_eq_zero_of_not_dvd hnd, Nat.cast_zero, sub_zero]
  exact Int.natCast_nonneg _

private theorem valuation_intCast_eq_pow (hA : A.LiesOverPrime q) (n : ℤ) (hn : n ≠ 0) :
    ∃ k : ℕ, A.valuation ((n : ℤ) : AlgebraicClosure ℚ)
      = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ k := by
  have hnA : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
  obtain ⟨k, m, hmdvd, hfact⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnA q hq1
  have hm0 : m ≠ 0 := by rintro rfl; exact hnA (by simp [hfact])
  have hmcop : Nat.Coprime m q :=
    (((Fact.out : q.Prime).coprime_iff_not_dvd).mpr hmdvd).symm
  have hmunit : A.valuation ((m : ℕ) : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm
    · rw [ValuationSubring.valuation_le_one_iff]
      exact natCast_mem A.toSubring m
    · have hr : algebraMap ℚ (AlgebraicClosure ℚ) ((m : ℚ)⁻¹) ∈ A := by
        refine algebraMap_rat_mem_of_den_coprime q A hA _ ?_
        simpa [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hm0)] using hmcop
      have hinv : A.valuation (((m : ℕ) : AlgebraicClosure ℚ))⁻¹ ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff]
        have : algebraMap ℚ (AlgebraicClosure ℚ) ((m : ℚ)⁻¹)
            = (((m : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
          rw [map_inv₀, eq_ratCast, Rat.cast_natCast]
        rwa [← this]
      rw [map_inv₀] at hinv
      have hpos : (0 : A.ValueGroup) < A.valuation ((m : ℕ) : AlgebraicClosure ℚ) :=
        (A.valuation.pos_iff).mpr (by exact_mod_cast hm0)
      rwa [inv_le_one₀ hpos] at hinv
  have hnabs : A.valuation ((n : ℤ) : AlgebraicClosure ℚ)
      = A.valuation ((n.natAbs : ℤ) : AlgebraicClosure ℚ) := by
    rcases Int.natAbs_eq n with heq | heq
    · conv_lhs => rw [heq]
    · conv_lhs => rw [heq, Int.cast_neg, Valuation.map_neg]
  refine ⟨k, ?_⟩
  rw [hnabs, Int.cast_natCast, hfact]; push_cast; rw [map_mul, map_pow, hmunit, mul_one]

private theorem exists_valuation_pow_le (hA : A.LiesOverPrime q)
    (z : AlgebraicClosure ℚ) (hz : z ∈ A) (hz0 : z ≠ 0) :
    ∃ N : ℕ, A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ N ≤ A.valuation z := by
  have hzQ : IsAlgebraic ℚ z⁻¹ := (Algebra.IsIntegral.isIntegral (R := ℚ) z⁻¹).isAlgebraic
  have hzZ : IsAlgebraic ℤ z⁻¹ :=
    (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := AlgebraicClosure ℚ)).mpr hzQ
  obtain ⟨d, hd0, hdint⟩ := hzZ.exists_integral_multiple
  obtain ⟨p, hpm, hpev⟩ := hdint
  set n := p.natDegree with hn
  simp only [Algebra.smul_def, eq_intCast] at hpev
  set w : AlgebraicClosure ℚ := (d : AlgebraicClosure ℚ) * z⁻¹ with hw
  have hwz : w * z = (d : AlgebraicClosure ℚ) := by
    rw [hw, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
  have hsum : ∑ i ∈ Finset.range (n + 1), (p.coeff i : AlgebraicClosure ℚ) * w ^ i = 0 := by
    have hev : Polynomial.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) w p
        = ∑ i ∈ Finset.range (p.natDegree + 1),
            (algebraMap ℤ (AlgebraicClosure ℚ)) (p.coeff i) * w ^ i :=
      Polynomial.eval₂_eq_sum_range (algebraMap ℤ (AlgebraicClosure ℚ)) w
    simp only [eq_intCast] at hev
    rw [hn, ← hev]; exact hpev
  have hmul : ∑ i ∈ Finset.range (n + 1),
      (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i * z ^ (n - i) = 0 := by
    have := congrArg (· * z ^ n) hsum
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hile : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hkey : w ^ i * z ^ n = (d : AlgebraicClosure ℚ) ^ i * z ^ (n - i) := by
      conv_lhs => rw [show n = i + (n - i) by omega, pow_add, ← mul_assoc, ← mul_pow, hwz]
    rw [mul_assoc (a := ((p.coeff i : AlgebraicClosure ℚ))),
        mul_assoc (a := ((p.coeff i : AlgebraicClosure ℚ))), hkey]
  have hlead : (p.coeff n : AlgebraicClosure ℚ) = 1 := by
    rw [hn, hpm.coeff_natDegree]; exact Int.cast_one
  have hsep : (d : AlgebraicClosure ℚ) ^ n
      + ∑ i ∈ Finset.range n,
          (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i * z ^ (n - i) = 0 := by
    have h1 := hmul
    rw [Finset.sum_range_succ, hlead, one_mul, Nat.sub_self, pow_zero, mul_one] at h1
    linear_combination h1
  have hbr : (d : AlgebraicClosure ℚ) ^ n
      = -z * ∑ i ∈ Finset.range n,
          (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i * z ^ (n - 1 - i) := by
    have h2 : ∑ i ∈ Finset.range n,
        (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i * z ^ (n - i)
        = z * ∑ i ∈ Finset.range n,
            (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i *
              z ^ (n - 1 - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := Finset.mem_range.mp hi
      have hni : n - i = (n - 1 - i) + 1 := by omega
      rw [hni, pow_succ]; ring
    linear_combination hsep - h2
  have hbracketA :
      ∑ i ∈ Finset.range n,
        (p.coeff i : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) ^ i *
          z ^ (n - 1 - i) ∈ A := by
    refine Subring.sum_mem A.toSubring fun i _ => ?_
    exact A.toSubring.mul_mem
      (A.toSubring.mul_mem (intCast_mem A.toSubring _)
        (A.toSubring.pow_mem (intCast_mem A.toSubring d) i))
      (A.toSubring.pow_mem hz _)
  have hvle : A.valuation ((d : AlgebraicClosure ℚ) ^ n) ≤ A.valuation z := by
    rw [hbr, map_mul, Valuation.map_neg]
    calc A.valuation z * A.valuation _
        ≤ A.valuation z * 1 := by
          gcongr; rw [ValuationSubring.valuation_le_one_iff]; exact hbracketA
      _ = A.valuation z := mul_one _
  have hdnpow : (d : AlgebraicClosure ℚ) ^ n = (((d ^ n : ℤ) : ℤ) : AlgebraicClosure ℚ) := by
    push_cast; ring
  obtain ⟨k, hk⟩ := valuation_intCast_eq_pow q A hA (d ^ n) (pow_ne_zero n hd0)
  rw [hdnpow, hk] at hvle
  exact ⟨k, hvle⟩

end Arithmetic

section Bridge

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem exists_finiteDimensional_isGalois_mem (x : AlgebraicClosure ℚ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ x ∈ F := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x} :
      IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.adjoin.finiteDimensional hint
  refine ⟨IntermediateField.normalClosure ℚ (IntermediateField.adjoin ℚ {x})
      (AlgebraicClosure ℚ),
    inferInstance, IsGalois.normalClosure ℚ (IntermediateField.adjoin ℚ {x})
      (AlgebraicClosure ℚ), ?_⟩
  exact (IntermediateField.adjoin ℚ {x}).le_normalClosure
    (IntermediateField.mem_adjoin_simple_self ℚ x)

private theorem restrictNormal_fix_of_inertia_map_eq
    {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [Normal ℚ F]
    {G : Subgroup (F ≃ₐ[ℚ] F)}
    (hQI : (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom F) = G)
    {x : AlgebraicClosure ℚ} (hxfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x)
    {xF : F} (hxF : algebraMap F (AlgebraicClosure ℚ) xF = x) :
    ∀ τ ∈ G, τ xF = xF := by
  intro τ hτ
  rw [← hQI] at hτ
  obtain ⟨σ, hσI, rfl⟩ := Subgroup.mem_map.mp hτ
  apply (algebraMap F (AlgebraicClosure ℚ)).injective
  have happ : AlgEquiv.restrictNormalHom F σ xF = σ.restrictNormal F xF := rfl
  rw [happ, AlgEquiv.restrictNormal_commutes σ F xF, hxF, hxfix σ hσI]

private theorem bridge (q : ℕ) [Fact q.Prime] (hA : A.LiesOverPrime q) (x : AlgebraicClosure ℚ)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ F)
      (_ : IsGalois ℚ F)
      (hxF : x ∈ F) (Q : Ideal (𝓞 F)), Q.IsMaximal ∧
      ((q : ℕ) : 𝓞 F) ∈ Q ∧
      (∀ y : 𝓞 F, A.valuation ((y : F) : AlgebraicClosure ℚ) ≤ 1) ∧
      (∀ y : 𝓞 F, y ∈ Q ↔ A.valuation ((y : F) : AlgebraicClosure ℚ) < 1) ∧
      (∀ τ ∈ Q.inertia (F ≃ₐ[ℚ] F), τ ⟨x, hxF⟩ = ⟨x, hxF⟩) := by
  obtain ⟨F, hFD, hFG, hxF⟩ := exists_finiteDimensional_isGalois_mem x
  have := hFD; have := hFG
  obtain ⟨Q, hQmax, hQq, hQle, hQlt, hQI⟩ :=
    ValuationSubring.exists_isMaximal_inertia_eq_map_restrictNormalHom A F
      (Fact.out : q.Prime) hA
  exact ⟨F, hFD, hFG, hxF, Q, hQmax, hQq, hQle, hQlt,
    restrictNormal_fix_of_inertia_map_eq A hQI hfix (xF := ⟨x, hxF⟩) rfl⟩

end Bridge

section KeyValuation

attribute [local instance] Ideal.Quotient.field

private theorem exists_mul_eq_mul_of_notMem_sq {D : Type*} [CommRing D] [IsDedekindDomain D]
    (P : Ideal D) {π a : D} (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) (ha : a ∈ P) :
    ∃ s ∉ P, ∃ b, s * a = π * b := by
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have h2 : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := (IsConcreteLE.not_le_iff_exists.mp hJP)
  have hsa : s * a ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s a]
    exact Ideal.mul_mem_mul ha hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsa
  exact ⟨s, hsP, b, by rw [← hb, mul_comm]⟩

/-- In a finite Galois extension `F / ℚ`, the prime `q` stays unramified in the fixed field of
the inertia group of a prime `Q` above `q`. -/
private theorem natCast_notMem_under_sq (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (q : ℕ) [hq : Fact q.Prime] (Q : Ideal (𝓞 F)) [hQ : Q.IsMaximal]
    (hqQ : ((q : ℕ) : 𝓞 F) ∈ Q) (E : IntermediateField ℚ F)
    (hE : IntermediateField.fixedField (Q.inertia (F ≃ₐ[ℚ] F)) = E) :
    ((q : ℕ) : 𝓞 E) ∉ (Q.under (𝓞 E)) ^ 2 := by
  classical
  have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hp0 : Ideal.span {((q : ℕ) : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hq0
  have hpmax : (Ideal.span {((q : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hq0).mpr (Nat.prime_iff_prime_int.mp hq.out)).isMaximal hp0
  have hQp : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    refine ⟨hpmax.eq_of_le ?_ ?_⟩
    · rw [Ideal.under_def]
      exact Ideal.comap_ne_top _ hQ.ne_top
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hqQ
  have : NeZero ((q : ℕ) : ℤ) := ⟨hq0⟩
  have hcard₁ : Nat.card (Q.inertia (F ≃ₐ[ℚ] F)) =
      (Ideal.span {((q : ℕ) : ℤ)}).ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[ℚ] F)
        (Ideal.span {((q : ℕ) : ℤ)}) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (F ≃ₐ[ℚ] F),
      ← Ideal.ramificationIdx'_eq_ramificationIdx _ Q hp0]
  subst hE
  set E : IntermediateField ℚ F := IntermediateField.fixedField (Q.inertia (F ≃ₐ[ℚ] F))
    with hEdef
  have : NumberField E := inferInstance
  have hGal : IsGaloisGroup (Q.inertia (F ≃ₐ[ℚ] F)) E F :=
    IsGaloisGroup.subgroup (F ≃ₐ[ℚ] F) ℚ F _
  have : IsGaloisGroup (Q.inertia (F ≃ₐ[ℚ] F)) (𝓞 E) (𝓞 F) :=
    IsGaloisGroup.of_isFractionRing (Q.inertia (F ≃ₐ[ℚ] F)) (𝓞 E) (𝓞 F) E F
  set QE : Ideal (𝓞 E) := Q.under (𝓞 E) with hQEdef
  have hQEmax : QE.IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  have hqQE : ((q : ℕ) : 𝓞 E) ∈ QE := by
    rw [hQEdef, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hqQ
  have hQE0 : QE ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqQE
    exact hq.out.ne_zero (by exact_mod_cast hqQE)
  have : Finite (𝓞 E ⧸ QE) := Ideal.finiteQuotientOfFreeOfNeBot QE hQE0
  have hcard₂ : Nat.card (Q.inertia (Q.inertia (F ≃ₐ[ℚ] F))) = QE.ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Q.inertia (F ≃ₐ[ℚ] F)) QE Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx QE Q (Q.inertia (F ≃ₐ[ℚ] F)),
      ← Ideal.ramificationIdx'_eq_ramificationIdx QE Q hQE0]
  have htop : Q.inertia (Q.inertia (F ≃ₐ[ℚ] F)) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).mpr fun τ => ?_
    rw [AddSubgroup.mem_inertia]
    intro x
    exact (AddSubgroup.mem_inertia.mp τ.2) x
  have hcardI : Nat.card (Q.inertia (Q.inertia (F ≃ₐ[ℚ] F))) =
      Nat.card (Q.inertia (F ≃ₐ[ℚ] F)) := by
    rw [htop, Subgroup.card_top]
  have htower := Ideal.ramificationIdx'_algebra_tower' (Ideal.span {((q : ℕ) : ℤ)}) QE Q
  have hne : Nat.card (Q.inertia (F ≃ₐ[ℚ] F)) ≠ 0 := Nat.card_pos.ne'
  have he1 : (Ideal.span {((q : ℕ) : ℤ)}).ramificationIdx' QE = 1 := by
    rw [← hcard₁, ← hcard₂, hcardI] at htower
    exact (Nat.mul_eq_right hne).mp htower.symm
  intro hmem
  have hle1 : (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ QE := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, map_natCast]
    exact hqQE
  have hle2 : (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ QE ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, map_natCast]
    exact hmem
  exact ((Ideal.ramificationIdx'_ne_one_iff hle1).mpr hle2) he1

private theorem valuation_eq_pow_of_step {D : Type*} [CommRing D]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (φ : D →+* AlgebraicClosure ℚ)
    (P : Ideal D) (π : D) (hπ0 : A.valuation (φ π) ≠ 0)
    (hle : ∀ y, A.valuation (φ y) ≤ 1) (hlt : ∀ y, y ∈ P ↔ A.valuation (φ y) < 1)
    (hstep : ∀ a ∈ P, ∃ s ∉ P, ∃ b, s * a = π * b) :
    ∀ (N : ℕ) (a : D), A.valuation (φ π) ^ N ≤ A.valuation (φ a) →
      ∃ m : ℕ, A.valuation (φ a) = A.valuation (φ π) ^ m := by
  intro N
  induction N with
  | zero =>
    intro a ha
    refine ⟨0, ?_⟩
    rw [pow_zero] at ha ⊢
    exact le_antisymm (hle a) ha
  | succ N ih =>
    intro a ha
    by_cases h1 : A.valuation (φ a) < 1
    · obtain ⟨s, hsP, b, hsab⟩ := hstep a ((hlt a).mpr h1)
      have hs1 : A.valuation (φ s) = 1 :=
        le_antisymm (hle s) (not_lt.mp (mt (hlt s).mpr hsP))
      have hab : A.valuation (φ a) = A.valuation (φ π) * A.valuation (φ b) := by
        have h := congrArg (fun t => A.valuation (φ t)) hsab
        simp only [map_mul, hs1, one_mul] at h
        exact h
      have h' : A.valuation (φ π) ^ N * A.valuation (φ π) ≤
          A.valuation (φ b) * A.valuation (φ π) := by
        calc A.valuation (φ π) ^ N * A.valuation (φ π)
            = A.valuation (φ π) ^ (N + 1) := (pow_succ _ _).symm
          _ ≤ A.valuation (φ a) := ha
          _ = A.valuation (φ π) * A.valuation (φ b) := hab
          _ = A.valuation (φ b) * A.valuation (φ π) := mul_comm _ _
      obtain ⟨m, hm⟩ := ih b (le_of_mul_le_mul_right h' (zero_lt_iff.mpr hπ0))
      exact ⟨m + 1, by rw [hab, hm, pow_succ, mul_comm]⟩
    · refine ⟨0, ?_⟩
      rw [pow_zero]
      exact le_antisymm (hle a) (not_lt.mp h1)

/-- An element of `A` fixed by the inertia subgroup and of valuation `< 1` has valuation at most
that of `q`: the inertia fixed field is unramified over `ℚ` at `A`. -/
private theorem valuation_le_of_forall_inertia_fix (q : ℕ) [hq : Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (x : AlgebraicClosure ℚ) (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x) (hxA : x ∈ A)
    (hx1 : A.valuation x < 1) :
    A.valuation x ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
  have hvq0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hq.out.ne_zero
  have halgQ : IsAlgebraic ℚ x := (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨d, hd0, hint⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hint
  have hfix' : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      σ ((d : AlgebraicClosure ℚ) * x) = (d : AlgebraicClosure ℚ) * x := by
    intro σ hσ
    rw [map_mul, map_intCast, hfix σ hσ]
  have hdA : ((d : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A d
  have hx'A : (d : AlgebraicClosure ℚ) * x ∈ A := A.mul_mem _ _ hdA hxA
  have hx'0 : (d : AlgebraicClosure ℚ) * x ≠ 0 := mul_ne_zero (by exact_mod_cast hd0) hx0
  obtain ⟨F, hFfin, hFgal, hxF, Q, hQmax, hqQ, hle, hlt, hfixQ⟩ :=
    bridge A q hA ((d : AlgebraicClosure ℚ) * x) hfix'
  have := hFfin
  have := hFgal
  have := hQmax
  have : NumberField F := NumberField.mk
  set E : IntermediateField ℚ F := IntermediateField.fixedField (Q.inertia (F ≃ₐ[ℚ] F))
    with hEdef
  have : NumberField E := inferInstance
  have hyE : (⟨(d : AlgebraicClosure ℚ) * x, hxF⟩ : F) ∈ E := by
    rw [hEdef, IntermediateField.mem_fixedField_iff]
    exact hfixQ
  have hintF : IsIntegral ℤ (⟨(d : AlgebraicClosure ℚ) * x, hxF⟩ : F) :=
    (isIntegral_algHom_iff (algebraMap F (AlgebraicClosure ℚ)).toIntAlgHom
      (algebraMap F (AlgebraicClosure ℚ)).injective).mp hint
  have hintE : IsIntegral ℤ (⟨⟨(d : AlgebraicClosure ℚ) * x, hxF⟩, hyE⟩ : E) :=
    (isIntegral_algHom_iff (algebraMap E F).toIntAlgHom (algebraMap E F).injective).mp hintF
  set a : 𝓞 E := ⟨⟨⟨(d : AlgebraicClosure ℚ) * x, hxF⟩, hyE⟩, hintE⟩ with hadef
  set QE : Ideal (𝓞 E) := Q.under (𝓞 E) with hQEdef
  let φ : 𝓞 E →+* AlgebraicClosure ℚ :=
    (algebraMap F (AlgebraicClosure ℚ)).comp ((algebraMap E F).comp (algebraMap (𝓞 E) E))
  have hφ : ∀ y : 𝓞 E,
      φ y = (((algebraMap (𝓞 E) (𝓞 F) y : 𝓞 F) : F) : AlgebraicClosure ℚ) := fun y => rfl
  have hleE : ∀ y : 𝓞 E, A.valuation (φ y) ≤ 1 := fun y => by rw [hφ]; exact hle _
  have hltE : ∀ y : 𝓞 E, y ∈ QE ↔ A.valuation (φ y) < 1 := fun y => by
    rw [hQEdef, Ideal.under_def, Ideal.mem_comap, hφ]
    exact hlt _
  have hqQE : ((q : ℕ) : 𝓞 E) ∈ QE := by
    rw [hQEdef, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hqQ
  have hqQE2 : ((q : ℕ) : 𝓞 E) ∉ QE ^ 2 := natCast_notMem_under_sq F q Q hqQ E hEdef.symm
  have hstep : ∀ b ∈ QE, ∃ s ∉ QE, ∃ c, s * b = ((q : ℕ) : 𝓞 E) * c :=
    fun b hb => exists_mul_eq_mul_of_notMem_sq QE hqQE hqQE2 hb
  have hφq : φ ((q : ℕ) : 𝓞 E) = ((q : ℕ) : AlgebraicClosure ℚ) := map_natCast φ q
  have hφa : φ a = (d : AlgebraicClosure ℚ) * x := rfl
  obtain ⟨N, hN⟩ := exists_valuation_pow_le q A hA _ hx'A hx'0
  obtain ⟨m, hm⟩ := valuation_eq_pow_of_step A φ QE ((q : ℕ) : 𝓞 E) (by rwa [hφq])
    hleE hltE hstep N a (by rwa [hφq, hφa])
  rw [hφa, hφq] at hm
  obtain ⟨k, hk⟩ := valuation_intCast_eq_pow q A hA d hd0
  have hprod : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ k * A.valuation x =
      A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ m := by
    rw [← hk, ← map_mul, ← hm]
  rcases le_or_gt m k with hmk | hkm
  · exfalso
    have h1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ k ≤
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ m :=
      pow_le_pow_right_of_le_one' hvq.le hmk
    have h2 : 1 * A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ k ≤
        A.valuation x * A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ k := by
      rw [one_mul, mul_comm, hprod]
      exact h1
    have h3 : 1 ≤ A.valuation x :=
      le_of_mul_le_mul_right h2 (zero_lt_iff.mpr (pow_ne_zero k hvq0))
    exact absurd hx1 (not_lt.mpr h3)
  · obtain ⟨j, rfl⟩ : ∃ j, m = k + (j + 1) := ⟨m - k - 1, by omega⟩
    have hxj : A.valuation x = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (j + 1) := by
      rw [pow_add] at hprod
      exact mul_left_cancel₀ (pow_ne_zero k hvq0) hprod
    rw [hxj, pow_succ]
    exact mul_le_of_le_one_left' (pow_le_one' hvq.le j)

end KeyValuation

section DVR

variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

/-- The ring of elements of `A` fixed by the inertia subgroup of `A`, as a subring of `ℚ̄`. -/
private def inertiaFixedRing : Subring (AlgebraicClosure ℚ) :=
  (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)).toSubring ⊓ A.toSubring

private theorem mem_inertiaFixedRing_iff (x : AlgebraicClosure ℚ) :
    x ∈ inertiaFixedRing A ↔ (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x) ∧ x ∈ A := by
  unfold inertiaFixedRing
  rw [Subring.mem_inf]
  exact and_congr_left' (IntermediateField.mem_fixedField_iff _ _)

private theorem isUnit_of_valuation_eq_one
    {x : AlgebraicClosure ℚ} (hx : x ∈ inertiaFixedRing A) (hx0 : x ≠ 0)
    (hv : A.valuation x = 1) : IsUnit (⟨x, hx⟩ : inertiaFixedRing A) := by
  obtain ⟨hxI, -⟩ := (mem_inertiaFixedRing_iff A x).mp hx
  have hxinvA : x⁻¹ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hv, inv_one]
  have hxinvI : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x⁻¹ = x⁻¹ := fun σ hσ => by
    rw [map_inv₀, hxI σ hσ]
  have hxinv : x⁻¹ ∈ inertiaFixedRing A :=
    (mem_inertiaFixedRing_iff A _).mpr ⟨hxinvI, hxinvA⟩
  exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxinv⟩,
    Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

variable {q} (hA : A.LiesOverPrime q)
include hA

private theorem exists_mul_eq_of_valuation_lt_one
    {x : AlgebraicClosure ℚ} (hx : x ∈ inertiaFixedRing A) (hvx : A.valuation x < 1) :
    ∃ y ∈ inertiaFixedRing A, x = ((q : ℕ) : AlgebraicClosure ℚ) * y := by
  obtain ⟨hxI, hxA⟩ := (mem_inertiaFixedRing_iff A x).mp hx
  have hvle := valuation_le_of_forall_inertia_fix q A hA x hxI hxA hvx
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  refine ⟨x / ((q : ℕ) : AlgebraicClosure ℚ), ?_, (mul_div_cancel₀ x hq0).symm⟩
  refine (mem_inertiaFixedRing_iff A _).mpr ⟨fun σ hσ => ?_, ?_⟩
  · rw [map_div₀, hxI σ hσ, show σ ((q : ℕ) : AlgebraicClosure ℚ) = q from map_natCast _ _]
  · rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    have hvqpos : (0 : A.ValueGroup) < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) :=
      (A.valuation.pos_iff).mpr hq0
    calc A.valuation x / A.valuation ((q : ℕ) : AlgebraicClosure ℚ)
        = A.valuation x * (A.valuation ((q : ℕ) : AlgebraicClosure ℚ))⁻¹ :=
          div_eq_mul_inv _ _
      _ ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ)
            * (A.valuation ((q : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hvle (inv_nonneg.mpr hvqpos.le)
      _ = 1 := mul_inv_cancel₀ hvqpos.ne'

private theorem irreducible_natCast_inertiaFixedRing :
    Irreducible (((q : ℕ) : inertiaFixedRing A)) := by
  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 :=
    (ValuationSubring.mem_nonunits_iff A).mp hA
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hvqpos : (0 : A.ValueGroup) < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) :=
    (A.valuation.pos_iff).mpr hq0
  constructor
  · intro hunit
    rcases hunit with ⟨u, hu⟩
    have hvuinv : A.valuation
        (((u⁻¹ : (inertiaFixedRing A)ˣ) : inertiaFixedRing A) : AlgebraicClosure ℚ) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff]
      exact ((mem_inertiaFixedRing_iff A _).mp
        ((u⁻¹ : (inertiaFixedRing A)ˣ) : inertiaFixedRing A).2).2
    have hprod : (((q : ℕ) : AlgebraicClosure ℚ)) *
        (((u⁻¹ : (inertiaFixedRing A)ˣ) : inertiaFixedRing A) : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (Subtype.val (p := (· ∈ inertiaFixedRing A))) u.mul_inv
      simpa [hu] using this
    have h1 : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
      rw [← hprod, map_mul]
      calc A.valuation _ * A.valuation _
          ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hvq
    simp at h1
  · rintro ⟨a, haO⟩ ⟨b, hbO⟩ hab
    have habℚ : ((q : ℕ) : AlgebraicClosure ℚ) = a * b :=
      congrArg (Subtype.val (p := (· ∈ inertiaFixedRing A))) hab
    have hvab : A.valuation ((q : ℕ) : AlgebraicClosure ℚ)
        = A.valuation a * A.valuation b := by rw [habℚ, map_mul]
    have ha0 : a ≠ 0 := by rintro rfl; exact hq0 (by simp [habℚ])
    have hb0 : b ≠ 0 := by rintro rfl; exact hq0 (by simp [habℚ])
    obtain ⟨haI, haA⟩ := (mem_inertiaFixedRing_iff A a).mp haO
    obtain ⟨-, hbA⟩ := (mem_inertiaFixedRing_iff A b).mp hbO
    rcases lt_or_eq_of_le ((ValuationSubring.valuation_le_one_iff A a).mpr haA) with hva | hva
    · have hvale := valuation_le_of_forall_inertia_fix q A hA a haI haA hva
      have hvb1 : A.valuation b = 1 := by
        apply le_antisymm ((ValuationSubring.valuation_le_one_iff A b).mpr hbA)
        have hineq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * 1
            ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * A.valuation b := by
          calc A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * 1
              = A.valuation a * A.valuation b := by rw [mul_one, hvab]
            _ ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * A.valuation b :=
                mul_le_mul_of_nonneg_right hvale ((A.valuation.pos_iff).mpr hb0).le
        exact le_of_mul_le_mul_left hineq hvqpos
      exact Or.inr (isUnit_of_valuation_eq_one A hbO hb0 hvb1)
    · exact Or.inl (isUnit_of_valuation_eq_one A haO ha0 hva)

private theorem associated_pow_of_ne_zero :
    ∀ x : inertiaFixedRing A, (x : AlgebraicClosure ℚ) ≠ 0 →
      ∃ n : ℕ, Associated (((q : ℕ) : inertiaFixedRing A) ^ n) x := by
  rintro ⟨x, hxO⟩ hx0
  obtain ⟨-, hxA⟩ := (mem_inertiaFixedRing_iff A x).mp hxO
  obtain ⟨N, hN⟩ := exists_valuation_pow_le q A hA x hxA hx0
  clear hxA
  induction N generalizing x with
  | zero =>
    rw [pow_zero] at hN
    obtain ⟨-, hxA⟩ := (mem_inertiaFixedRing_iff A x).mp hxO
    have hv1 : A.valuation x = 1 :=
      le_antisymm ((ValuationSubring.valuation_le_one_iff A x).mpr hxA) hN
    exact ⟨0, by
      rw [pow_zero]; exact (associated_one_iff_isUnit.mpr
        (isUnit_of_valuation_eq_one A hxO hx0 hv1)).symm⟩
  | succ N IH =>
    obtain ⟨-, hxA⟩ := (mem_inertiaFixedRing_iff A x).mp hxO
    rcases lt_or_eq_of_le ((ValuationSubring.valuation_le_one_iff A x).mpr hxA) with hvx | hvx
    · obtain ⟨y, hyO, hxy⟩ := exists_mul_eq_of_valuation_lt_one A hA hxO hvx
      have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : q.Prime).ne_zero
      have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp [hxy])
      have hvqpos : (0 : A.ValueGroup) < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) :=
        (A.valuation.pos_iff).mpr hq0
      have hNy : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ N ≤ A.valuation y := by
        have heq : A.valuation x
            = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * A.valuation y := by
          rw [hxy, map_mul]
        rw [pow_succ', heq] at hN
        exact le_of_mul_le_mul_left hN hvqpos
      obtain ⟨n, hn⟩ := IH y hyO hy0 hNy
      refine ⟨n + 1, ?_⟩
      have hxy' : (⟨x, hxO⟩ : inertiaFixedRing A) = ((q : ℕ) : inertiaFixedRing A) * ⟨y, hyO⟩ :=
        Subtype.ext (by push_cast; exact hxy)
      rw [hxy', pow_succ']
      exact (Associated.refl _).mul_mul hn
    · exact ⟨0, by
        rw [pow_zero]; exact (associated_one_iff_isUnit.mpr
          (isUnit_of_valuation_eq_one A hxO hx0 hvx)).symm⟩

private theorem isDiscreteValuationRing_inertiaFixedRing :
    IsDiscreteValuationRing (inertiaFixedRing A) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨((q : ℕ) : inertiaFixedRing A), irreducible_natCast_inertiaFixedRing A hA, ?_⟩
  intro x hx
  exact associated_pow_of_ne_zero A hA x (fun h => hx (Subtype.ext h))

omit hA in
/-- The valuation ring of the inertia fixed field is ring-isomorphic to `inertiaFixedRing A`. -/
private def inertiaFixedRingEquiv :
    inertiaFixedRing A ≃+*
      A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ)) where
  toFun x := ⟨⟨x, (IntermediateField.mem_fixedField_iff _ _).mpr
      ((mem_inertiaFixedRing_iff A x).mp x.2).1⟩, ((mem_inertiaFixedRing_iff A x).mp x.2).2⟩
  invFun y := ⟨(y : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)),
    (mem_inertiaFixedRing_iff A _).mpr
      ⟨(IntermediateField.mem_fixedField_iff _ _).mp
        (y : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)).2, y.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end DVR

section PublicDVR

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
  (hA : A.LiesOverPrime q)
include hA

/-- The valuation ring of the subfield of `ℚ̄` fixed by the inertia subgroup of a valuation
subring `A` lying over a prime is a discrete valuation ring. -/
public theorem isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn :
    IsDiscreteValuationRing
      (A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ))) := by
  have := isDiscreteValuationRing_inertiaFixedRing A hA
  have : IsPrincipalIdealRing
      (A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ))) :=
    IsPrincipalIdealRing.of_surjective (inertiaFixedRingEquiv A).toRingHom
      (inertiaFixedRingEquiv A).surjective
  have hirr : Irreducible ((q : ℕ) :
      A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ))) := by
    rw [← map_natCast (inertiaFixedRingEquiv A) q]
    exact (MulEquiv.irreducible_iff (inertiaFixedRingEquiv A).toMulEquiv).mpr
      (irreducible_natCast_inertiaFixedRing A hA)
  refine { not_a_field' := fun hbot => ?_ }
  have hmem : ((q : ℕ) : A.comap (algebraMap
      (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∈
      maximalIdeal _ := (mem_maximalIdeal _).mpr hirr.not_isUnit
  rw [hbot, Ideal.mem_bot] at hmem
  exact hirr.ne_zero hmem

/-- For a valuation subring `A` of `ℚ̄` lying over a prime `q`, the prime `q` is a uniformizer
of the valuation ring of the subfield of `ℚ̄` fixed by the inertia subgroup of `A`. -/
public theorem irreducible_natCast_comap_fixedField_inertiaSubgroupIn :
    Irreducible ((q : ℕ) :
      A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ))) := by
  rw [← map_natCast (inertiaFixedRingEquiv A) q]
  exact (MulEquiv.irreducible_iff (inertiaFixedRingEquiv A).toMulEquiv).mpr
    (irreducible_natCast_inertiaFixedRing A hA)

end PublicDVR

section Henselian

private theorem isUnit_of_sub_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hx : IsUnit x) (hxy : y - x ∈ maximalIdeal R) : IsUnit y := by
  by_contra hy
  have hy' : y ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hy
  have hx' : x ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hy' hxy
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal _).mp hx' hx

private theorem eval_sub_eval_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (g : R[X]) {x y : R} (hxy : x - y ∈ maximalIdeal R) :
    g.eval x - g.eval y ∈ maximalIdeal R := by
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub x y g
  rw [hc]
  exact Ideal.mul_mem_right _ _ hxy

/-- A root of `f` congruent to `a₀` modulo the maximal ideal is unique when `f' (a₀)` is a
unit. -/
private theorem eq_of_isRoot_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] (f : R[X])
    (a₀ : R) (hu : IsUnit (f.derivative.eval a₀)) {α β : R} (hα : f.IsRoot α)
    (hα₀ : α - a₀ ∈ maximalIdeal R) (hβ : f.IsRoot β) (hβ₀ : β - a₀ ∈ maximalIdeal R) :
    β = α := by
  set g := f /ₘ (X - C α) with hg
  have hfac : (X - C α) * g = f := mul_divByMonic_eq_iff_isRoot.mpr hα
  have hder : f.derivative.eval α = g.eval α := by
    conv_lhs => rw [← hfac]
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have hgα : IsUnit (g.eval α) := by
    rw [← hder]
    exact isUnit_of_sub_mem_maximalIdeal hu (eval_sub_eval_mem_maximalIdeal f.derivative hα₀)
  have hβα : β - α ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hβ₀ hα₀
    rwa [sub_sub_sub_cancel_right] at this
  have hgβ : IsUnit (g.eval β) :=
    isUnit_of_sub_mem_maximalIdeal hgα (eval_sub_eval_mem_maximalIdeal g hβα)
  have h0 : (β - α) * g.eval β = 0 := by
    have := hβ.eq_zero
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this
  exact sub_eq_zero.mp ((hgβ.mul_left_eq_zero).mp h0)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- The inclusion of the valuation ring of the inertia fixed field into `A`. -/
private def inertiaFixedIncl :
    A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L) →+* A where
  toFun o := ⟨algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L
    (o : IntermediateField.fixedField (A.inertiaSubgroupIn K)), ValuationSubring.mem_comap.mp o.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem inertiaFixedIncl_coe
    (o : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) :
    ((inertiaFixedIncl A o : A) : L) =
      ((o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L) := rfl

private theorem inertiaFixedIncl_injective :
    Function.Injective (inertiaFixedIncl (K := K) A) := by
  intro x y h
  have h1 : ((x : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L) =
      ((y : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L) := by
    rw [← inertiaFixedIncl_coe, ← inertiaFixedIncl_coe, h]
  exact Subtype.ext (Subtype.ext h1)

private theorem isUnit_iff_isUnit_inertiaFixedIncl
    (o : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) :
    IsUnit o ↔ IsUnit (inertiaFixedIncl A o) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  have ho' : (o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) ≠ 0 := by
    intro h0
    apply h.ne_zero
    apply Subtype.ext
    rw [inertiaFixedIncl_coe, h0]; rfl
  obtain ⟨w, hw⟩ := h.exists_left_inv
  have h1 : ((w : A) : L) * ((o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L) =
      1 := by
    have := congrArg (fun a : A => (a : L)) hw
    simpa [inertiaFixedIncl_coe] using this
  have hwL : ((w : A) : L) =
      (((o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L))⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  have hinvA : algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L
      ((o : IntermediateField.fixedField (A.inertiaSubgroupIn K))⁻¹) ∈ A := by
    rw [map_inv₀]
    change (((o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L))⁻¹ ∈ A
    rw [← hwL]; exact w.2
  have hinvO : ((o : IntermediateField.fixedField (A.inertiaSubgroupIn K))⁻¹) ∈
      A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L) :=
    ValuationSubring.mem_comap.mpr hinvA
  refine IsUnit.of_mul_eq_one ⟨_, hinvO⟩ ?_
  apply Subtype.ext
  change (o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) *
    (o : IntermediateField.fixedField (A.inertiaSubgroupIn K))⁻¹ = 1
  exact mul_inv_cancel₀ ho'

private theorem mem_maximalIdeal_iff_inertiaFixedIncl
    (o : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) :
    o ∈ maximalIdeal _ ↔ inertiaFixedIncl A o ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_maximalIdeal, _root_.mem_nonunits_iff, _root_.mem_nonunits_iff,
    isUnit_iff_isUnit_inertiaFixedIncl]

private theorem smul_sub_mem_maximalIdeal (τ : A.decompositionSubgroup K)
    (hτ : τ ∈ A.inertiaSubgroup K) (a : A) : τ • a - a ∈ maximalIdeal A := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) τ = 1 :=
    (MonoidHom.mem_ker).mp hτ
  have h2 : τ • residue A a = residue A a := by
    have := congrArg (fun e : RingAut (ResidueField A) => e (residue A a)) h1
    simpa [MulSemiringAction.toRingAut_apply] using this
  rw [← ResidueField.residue_smul] at h2
  exact Ideal.Quotient.eq.mp h2

private theorem smul_inertiaFixedIncl (τ : A.decompositionSubgroup K)
    (hτ : τ ∈ A.inertiaSubgroup K)
    (o : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) :
    τ • inertiaFixedIncl A o = inertiaFixedIncl A o := by
  apply Subtype.ext
  change (τ : L ≃ₐ[K] L) _ = _
  rw [inertiaFixedIncl_coe]
  have hmem : ((o : IntermediateField.fixedField (A.inertiaSubgroupIn K)) : L) ∈
      IntermediateField.fixedField (A.inertiaSubgroupIn K) :=
    (o : IntermediateField.fixedField (A.inertiaSubgroupIn K)).2
  exact (IntermediateField.mem_fixedField_iff _ _).mp hmem _ (Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩)

/-- For a valuation subring `A` of an algebraically closed field `L` and any subfield `K`, the
valuation ring of the subfield of `L` fixed by the inertia subgroup of `A` over `K` is
Henselian. -/
public theorem henselianLocalRing_comap_fixedField_inertiaSubgroupIn [IsAlgClosed L] :
    HenselianLocalRing
      (A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) where
  is_henselian f hf a₀ h₀ hu := by
    have : HenselianLocalRing A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
    set ι := inertiaFixedIncl (K := K) A with hι
    set fA := f.map ι with hfA
    have hfAm : fA.Monic := hf.map ι
    have hev : ∀ o, fA.eval (ι o) = ι (f.eval o) := fun o => by
      rw [hfA, eval_map, eval₂_hom]
    have h₀A : fA.eval (ι a₀) ∈ maximalIdeal A := by
      rw [hev]; exact (mem_maximalIdeal_iff_inertiaFixedIncl A _).mp h₀
    have huA : IsUnit (fA.derivative.eval (ι a₀)) := by
      rw [hfA, derivative_map, eval_map, eval₂_hom]; exact hu.map ι
    obtain ⟨α, hα, hα₀⟩ := HenselianLocalRing.is_henselian fA hfAm (ι a₀) h₀A huA
    have hfix : ∀ σ ∈ A.inertiaSubgroupIn K, σ (α : L) = α := by
      intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
      have hsm : τ • fA = fA := by
        ext n
        rw [AddMonoidAlgebra.coeff_smul_apply, hfA, coeff_map, smul_inertiaFixedIncl A τ hτ]
      have hβroot : fA.IsRoot (τ • α) := by
        change fA.eval (τ • α) = 0
        conv_lhs => rw [← hsm]
        rw [smul_eval_smul, (show fA.eval α = 0 from hα), smul_zero]
      have hβ₀ : τ • α - ι a₀ ∈ maximalIdeal A := by
        have := Ideal.add_mem _ (smul_sub_mem_maximalIdeal A τ hτ α) hα₀
        rwa [sub_add_sub_cancel] at this
      have hβα : τ • α = α := eq_of_isRoot_of_sub_mem fA (ι a₀) huA hα hα₀ hβroot hβ₀
      exact congrArg (fun a : A => (a : L)) hβα
    have hαK : (α : L) ∈ IntermediateField.fixedField (A.inertiaSubgroupIn K) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr hfix
    have hαA : algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L
        ⟨α, hαK⟩ ∈ A := α.2
    let a : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L) :=
      ⟨⟨α, hαK⟩, ValuationSubring.mem_comap.mpr hαA⟩
    have ha : ι a = α := Subtype.ext rfl
    refine ⟨a, ?_, ?_⟩
    · apply inertiaFixedIncl_injective (K := K) A
      change ι (f.eval a) = ι 0
      rw [map_zero, ← hev, ha]
      exact hα
    · rw [mem_maximalIdeal_iff_inertiaFixedIncl, map_sub]
      change ι a - ι a₀ ∈ maximalIdeal A
      rw [ha]
      exact hα₀

end Henselian

section Residue

private theorem exists_residue_apply_eq {L : Type*} [Field L] [Algebra ℚ L]
    (A : ValuationSubring L) {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (a : A) :
    ∃ h : σ (a : L) ∈ A, residue A ⟨σ (a : L), h⟩ = residue A a := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hval : ((d • a : A) : L) = ((A.decompositionSubgroup ℚ).subtype d) (a : L) := rfl
  refine ⟨hval ▸ (d • a).2, ?_⟩
  have h1 : (⟨((A.decompositionSubgroup ℚ).subtype d) (a : L), hval ▸ (d • a).2⟩ : A) =
      d • a := Subtype.ext hval.symm
  rw [h1, ResidueField.residue_smul]
  have h2 := RingEquiv.congr_fun (MonoidHom.mem_ker.mp hd) (residue A a)
  simpa using h2

end Residue

section ResidueSurjective

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]

set_option quotPrecheck false in
local notation "κ₀" => IntermediateField.fixedField (ValuationSubring.inertiaSubgroupIn ℚ A)

/-- Every residue class of a valuation subring `A` of `ℚ̄` lying over a prime has a
representative in the subfield fixed by the inertia subgroup of `A`. -/
public theorem exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
    (hA : A.LiesOverPrime q) (x : ResidueField A) :
    ∃ y : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ)),
      residue A ⟨algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ) (y : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)),
          y.2⟩ = x := by
  classical
  have hchar : CharP (ResidueField A) q :=
    charP_residueField_of_liesOverPrime A q hA
  have hq : q.Prime := Fact.out
  let red' : A.comap (algebraMap κ₀ (AlgebraicClosure ℚ)) → ResidueField A :=
    fun y => residue A ⟨algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀), y.2⟩
  have red'_mul : ∀ y y', red' (y * y') = red' y * red' y' := fun y y' => by
    simp only [red']; rw [← map_mul]; rfl
  have red'_add : ∀ y y', red' (y + y') = red' y + red' y' := fun y y' => by
    simp only [red']; rw [← map_add]; rfl
  have red'_one : red' 1 = 1 := by
    simp only [red']; rw [← (residue A).map_one]; rfl
  have red'_zero : red' 0 = 0 := by
    simp only [red']; rw [← (residue A).map_zero]; rfl
  have red'_neg : ∀ y, red' (-y) = -red' y := fun y => by
    simp only [red']; rw [← map_neg]; rfl
  suffices hsurj : ∃ y, red' y = x by obtain ⟨y, hy⟩ := hsurj; exact ⟨y, hy⟩
  let k' : Subfield (ResidueField A) :=
    { carrier := Set.range red'
      mul_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩; exact ⟨y * y', red'_mul y y'⟩
      one_mem' := ⟨1, red'_one⟩
      add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩; exact ⟨y + y', red'_add y y'⟩
      zero_mem' := ⟨0, red'_zero⟩
      neg_mem' := by rintro _ ⟨y, rfl⟩; exact ⟨-y, red'_neg y⟩
      inv_mem' := by
        rintro _ ⟨y, rfl⟩
        by_cases h0 : red' y = 0
        · exact ⟨y, by rw [h0, inv_zero]⟩
        · have hyu : IsUnit
              (⟨algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀), y.2⟩ : A) := by
            by_contra hnu
            exact h0 ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hnu))
          have hy0 : (y : κ₀) ≠ 0 := by
            intro h; apply h0
            change residue A ⟨algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀), y.2⟩ = 0
            have : (⟨algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀), y.2⟩ : A) = 0 :=
              Subtype.ext (by simp [h])
            rw [this, map_zero]
          obtain ⟨u, hu⟩ := hyu
          have hval : ((u : A) : AlgebraicClosure ℚ) =
              algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀) := congrArg Subtype.val hu
          have hmul : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) *
              algebraMap κ₀ (AlgebraicClosure ℚ) (y : κ₀) = 1 := by
            rw [← hval, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
          have hinvA : algebraMap κ₀ (AlgebraicClosure ℚ) ((y : κ₀)⁻¹) ∈ A := by
            rw [map_inv₀, inv_eq_of_mul_eq_one_left hmul]
            exact Subtype.coe_prop _
          refine ⟨⟨(y : κ₀)⁻¹, hinvA⟩, ?_⟩
          apply eq_inv_of_mul_eq_one_right
          rw [← red'_mul]
          have : y * ⟨(y : κ₀)⁻¹, hinvA⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
          rw [this, red'_one] }
  have hk'mem : ∀ y, red' y ∈ k' := fun y => ⟨y, rfl⟩
  have : CharP k' q := by
    refine (CharP.charP_iff_prime_eq_zero hq).mpr (k'.subtype.injective ?_)
    rw [map_natCast, map_zero, CharP.cast_eq_zero]
  let : Algebra (ZMod q) k' := ZMod.algebra _ q
  have halgL : ∀ b : AlgebraicClosure ℚ, IsAlgebraic ℚ b := fun b =>
    (Algebra.IsIntegral.isIntegral (R := ℚ) b).isAlgebraic
  have : Algebra.IsAlgebraic (ZMod q) k' := by
    let : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
    have := algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A q
    exact Algebra.IsAlgebraic.of_injective
      { k'.subtype with
        commutes' := fun r => RingHom.congr_fun (Subsingleton.elim
          (k'.subtype.comp (algebraMap (ZMod q) k')) (algebraMap (ZMod q) (ResidueField A))) r }
      k'.subtype.injective
  have : PerfectField k' := Algebra.IsAlgebraic.perfectField (K := ZMod q)
  obtain ⟨a, rfl⟩ := residue_surjective x
  have haint : IsIntegral ℚ (a : AlgebraicClosure ℚ) := (halgL _).isIntegral
  have hfinL : {b : AlgebraicClosure ℚ |
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = b}.Finite := by
    refine ((minpoly ℚ (a : AlgebraicClosure ℚ)).rootSet_finite (AlgebraicClosure ℚ)).subset ?_
    rintro _ ⟨σ, -, rfl⟩
    rw [mem_rootSet]
    exact ⟨minpoly.ne_zero haint, by rw [aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  have hfin : (Subtype.val ⁻¹' {b : AlgebraicClosure ℚ |
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = b} : Set A).Finite :=
    hfinL.preimage Subtype.val_injective.injOn
  set F := hfin.toFinset with hF
  have hmemF : ∀ b : A, b ∈ F ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ,
      σ (a : AlgebraicClosure ℚ) = (b : AlgebraicClosure ℚ) := fun b => by
    rw [hF, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
  have haF : a ∈ F := (hmemF a).mpr ⟨1, Subgroup.one_mem _, rfl⟩
  have hres : ∀ b ∈ F, residue A b = residue A a := by
    intro b hb
    obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
    obtain ⟨h, hres⟩ := exists_residue_apply_eq A hσ a
    rw [← hres]; congr 1; exact Subtype.ext hb.symm
  set PA : A[X] := ∏ b ∈ F, (X - C b) with hPA
  have hPAres : PA.map (residue A) = (X - C (residue A a)) ^ F.card := by
    rw [hPA, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rw [Finset.prod_congr rfl (fun b hb => by rw [hres b hb]), Finset.prod_const]
  have hstab : ∀ {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
      (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (b : A), τ (b : AlgebraicClosure ℚ) ∈ A :=
    fun hτ b => (exists_residue_apply_eq A hτ b).1
  have hcoeffKI : ∀ k, ((PA.coeff k : A) : AlgebraicClosure ℚ) ∈ κ₀ := by
    intro k
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hτ' : τ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hτ
    have hP : (PA.map A.subtype).map
        (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = PA.map A.subtype := by
      rw [hPA, Polynomial.map_prod, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe]
      refine Finset.prod_nbij' (fun b => (⟨τ (b : AlgebraicClosure ℚ), hstab hτ b⟩ : A))
        (fun b => (⟨τ⁻¹ (b : AlgebraicClosure ℚ), hstab hτ' b⟩ : A)) ?_ ?_ ?_ ?_ ?_
      · intro b hb
        obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
        exact (hmemF _).mpr
          ⟨τ * σ, Subgroup.mul_mem _ hτ hσ, by rw [AlgEquiv.mul_apply, hb]⟩
      · intro b hb
        obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
        exact (hmemF _).mpr
          ⟨τ⁻¹ * σ, Subgroup.mul_mem _ hτ' hσ, by rw [AlgEquiv.mul_apply, hb]⟩
      · intro b _; apply Subtype.ext; simp
      · intro b _; apply Subtype.ext; simp
      · intro b _; rfl
    have := congrArg (fun f => f.coeff k) hP
    simp only [coeff_map, RingHom.coe_coe] at this
    exact this
  set n := F.card with hn
  have hn0 : n ≠ 0 := Finset.card_ne_zero_of_mem haF
  have hlifts : (X - C (residue A a)) ^ n ∈
      Polynomial.lifts (algebraMap k' (ResidueField A)) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    refine ⟨⟨red' ⟨⟨_, hcoeffKI k⟩, (PA.coeff k).2⟩, hk'mem _⟩, ?_⟩
    rw [← hPAres, coeff_map]
    rfl
  obtain ⟨Q, hQmap, -, hQmonic⟩ :=
    lifts_and_natDegree_eq_and_monic hlifts ((monic_X_sub_C _).pow n)
  set x := residue A a with hx
  have hxint : IsIntegral k' x := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [eval₂_eq_eval_map, hQmap, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hn0]
  have hsep : (minpoly k' x).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hxint)
  have hdvd : (minpoly k' x).map (algebraMap k' (ResidueField A)) ∣ (X - C x) ^ n := by
    rw [← hQmap]
    refine Polynomial.map_dvd _ (minpoly.dvd _ _ ?_)
    rw [aeval_def, eval₂_eq_eval_map, hQmap, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow hn0]
  have hpow0 : (X - C x) ^ n ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero x)
  have hsplit : ((minpoly k' x).map (algebraMap k' (ResidueField A))).Splits :=
    ((Splits.X_sub_C x).pow n).of_dvd hpow0 hdvd
  have hroots : ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots = {x} := by
    have hle : ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots ≤
        n • ({x} : Multiset (ResidueField A)) := by
      have := roots.le_of_dvd hpow0 hdvd
      rwa [roots_pow, roots_X_sub_C] at this
    have hall : ∀ b ∈ ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots, b = x :=
      fun b hb => by
        have := Multiset.mem_of_le hle hb
        rw [Multiset.mem_nsmul] at this
        exact Multiset.mem_singleton.mp this.2
    have hnodup : ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots.Nodup :=
      nodup_roots hsep.map
    have hxmem : x ∈ ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots := by
      rw [mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hxint)), IsRoot.def, eval_map,
        ← aeval_def]
      exact minpoly.aeval _ _
    have hrep := Multiset.eq_replicate_of_mem hall
    have hle1 : Multiset.card
        ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots ≤ 1 := by
      have := Multiset.nodup_iff_count_le_one.mp hnodup x
      rwa [hrep, Multiset.count_replicate_self] at this
    have hge1 : 1 ≤ Multiset.card
        ((minpoly k' x).map (algebraMap k' (ResidueField A))).roots :=
      Multiset.card_pos.mpr (fun h0 => by rw [h0] at hxmem; exact Multiset.notMem_zero _ hxmem)
    rw [hrep, le_antisymm hle1 hge1]
    rfl
  have hdeg : (minpoly k' x).natDegree = 1 := by
    rw [← Polynomial.natDegree_map (algebraMap k' (ResidueField A)),
      hsplit.natDegree_eq_card_roots, hroots]
    rfl
  obtain ⟨z, hz⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  obtain ⟨y, hy⟩ := z.2
  exact ⟨y, hy.trans hz⟩

end ResidueSurjective

section Main

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]

private theorem isLocalHom_inertiaFixedIncl : IsLocalHom (inertiaFixedIncl (K := ℚ) A) :=
  ⟨fun o ho => (isUnit_iff_isUnit_inertiaFixedIncl A o).mpr ho⟩

/-- For a valuation subring `A` of `ℚ̄` lying over a prime, the residue field of the valuation
ring of the subfield of `ℚ̄` fixed by the inertia subgroup of `A` is algebraically closed. -/
public theorem isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
    (hA : A.LiesOverPrime q) :
    IsAlgClosed (ResidueField
      (A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ)))) := by
  have := isLocalHom_inertiaFixedIncl A
  have : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hsurj : Function.Surjective (ResidueField.map (inertiaFixedIncl (K := ℚ) A)) := by
    intro r
    obtain ⟨y, hy⟩ := exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq A hA r
    exact ⟨residue _ y, by rw [ResidueField.map_residue]; exact hy⟩
  exact IsAlgClosed.of_ringEquiv _ _
    (RingEquiv.ofBijective _ ⟨(ResidueField.map _).injective, hsurj⟩).symm

/-- **Intermediate Henselian discrete valuation ring.** For a valuation subring `A` of `ℚ̄`
lying over a prime `q`, there is an intermediate field `k₀` of `ℚ̄ / ℚ` and an element
`π₀ ∈ k₀ ∩ A` such that `k₀ ∩ A` is a Henselian discrete valuation ring with maximal ideal
generated by `π₀` and algebraically closed residue field, and every element of `A` is
congruent modulo the maximal ideal of `A` to an element of `k₀ ∩ A`. One may take `k₀` to be
the inertia fixed field and `π₀ = q`. -/
public theorem exists_intermediateField_henselian_dvr_residue_approx
    (hA : A.LiesOverPrime q) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : k₀)
      (hπ : (π₀ : AlgebraicClosure ℚ) ∈ A),
      IsDiscreteValuationRing (A.comap (algebraMap k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal (A.comap (algebraMap k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : A.comap (algebraMap k₀ (AlgebraicClosure ℚ)))} ∧
      HenselianLocalRing (A.comap (algebraMap k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField (A.comap (algebraMap k₀ (AlgebraicClosure ℚ)))) ∧
      ∀ a : AlgebraicClosure ℚ, a ∈ A → ∃ c : k₀, (c : AlgebraicClosure ℚ) ∈ A ∧
        ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A := by
  have hπ : (((q : ℕ) : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) :
      AlgebraicClosure ℚ) ∈ A := by
    simp
  have := isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A hA
  refine ⟨IntermediateField.fixedField (A.inertiaSubgroupIn ℚ), (q : ℕ), hπ, inferInstance,
    ?_, henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A,
    isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn A hA, ?_⟩
  · have hq : (⟨(q : ℕ), hπ⟩ : A.comap (algebraMap
        (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) =
        ((q : ℕ) : A.comap (algebraMap
          (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) :=
      Subtype.ext (by simp)
    rw [hq]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
      (irreducible_natCast_comap_fixedField_inertiaSubgroupIn A hA)
  · intro a ha
    obtain ⟨y, hy⟩ :=
      exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq A hA (residue A ⟨a, ha⟩)
    refine ⟨y, y.2, A.toSubring.sub_mem ha y.2, ?_⟩
    exact Ideal.Quotient.eq.mp hy.symm

end Main

end ValuationSubring
