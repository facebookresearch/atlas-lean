/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.lean`,
`P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.lean`,
the prime-power inertia-character theorem and solution in `Theorems/` and
`P2M/Sol/` (files named
`..._exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one`),
`Definitions/Def_FLTPrelim_Ramification.lean`, and the inertia-at-`p`
Kummer-character theorem and solution in `Theorems/` and `P2M/Sol/`
(files named
`..._exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot`)
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

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Valuation.LocalSubring

@[expose] public section

open scoped NumberField Pointwise

namespace InertiaCyclotomicAux

scoped instance (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  to_finiteDimensional := inferInstance

end InertiaCyclotomicAux

open scoped InertiaCyclotomicAux

noncomputable section

namespace ValuationSubring


section Integers

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_of_isIntegral_int {b : AlgebraicClosure ℚ} (hb : IsIntegral ℤ b) : b ∈ A := by
  have hbA : IsIntegral A b := by
    obtain ⟨f, hf, hfb⟩ := hb
    refine ⟨f.map (Int.castRingHom A), hf.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A) =
        algebraMap ℤ (AlgebraicClosure ℚ) from RingHom.ext_int _ _]
    exact hfb
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hbA
  rw [← hy]
  exact y.2


private theorem coe_integralClosure_mem (b : integralClosure ℤ (AlgebraicClosure ℚ)) :
    (b : AlgebraicClosure ℚ) ∈ A :=
  mem_of_isIntegral_int A b.2

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem algebraMap_ringOfIntegers_mem (x : 𝓞 L) :
    algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A :=
  mem_of_isIntegral_int A
    (map_isIntegral_int (algebraMap L (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe x))


private theorem valuation_algebraMap_ringOfIntegers_le_one (x : 𝓞 L) :
    A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (algebraMap_ringOfIntegers_mem A L x)


private def ringOfIntegersToValuationSubring : 𝓞 L →+* A :=
  ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
    (fun x => algebraMap_ringOfIntegers_mem A L x)

@[scoped simp] private theorem coe_ringOfIntegersToValuationSubring (x : 𝓞 L) :
    (ringOfIntegersToValuationSubring A L x : AlgebraicClosure ℚ) =
      algebraMap L (AlgebraicClosure ℚ) (x : L) := rfl

private def primeBelow : Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal A).comap (ringOfIntegersToValuationSubring A L)

private theorem mem_primeBelow_iff {x : 𝓞 L} :
    x ∈ primeBelow A L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) < 1 := by
  rw [primeBelow, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

private theorem mem_primeBelow_iff_mem_nonunits {x : 𝓞 L} :
    x ∈ primeBelow A L ↔ algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A.nonunits := by
  rw [mem_primeBelow_iff, mem_nonunits_iff]

private theorem notMem_primeBelow_iff {x : 𝓞 L} :
    x ∉ primeBelow A L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) = 1 := by
  rw [mem_primeBelow_iff, not_lt]
  exact ⟨fun h => le_antisymm (valuation_algebraMap_ringOfIntegers_le_one A L x) h,
    fun h => h.ge⟩

private instance primeBelow_isPrime : (primeBelow A L).IsPrime :=
  Ideal.IsPrime.comap _

variable {p : ℕ}

private theorem natCast_mem_primeBelow (hA : A.LiesOverPrime p) : (p : 𝓞 L) ∈ primeBelow A L := by
  rw [mem_primeBelow_iff_mem_nonunits]
  change algebraMap L (AlgebraicClosure ℚ) (algebraMap (𝓞 L) L (p : 𝓞 L)) ∈ A.nonunits
  rw [map_natCast, map_natCast]
  exact hA

private theorem primeBelow_ne_bot (hp : p.Prime) (hA : A.LiesOverPrime p) : primeBelow A L ≠ ⊥ := by
  intro h
  have := natCast_mem_primeBelow A L hA
  rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
  exact hp.ne_zero this

private theorem span_natCast_isMaximal (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)

private theorem under_int_primeBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (primeBelow A L).under ℤ = Ideal.span {(p : ℤ)} := by
  refine ((span_natCast_isMaximal hp).eq_of_le (Ideal.IsPrime.under ℤ _).ne_top ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeBelow A L hA

private theorem primeBelow_liesOver (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (primeBelow A L).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(under_int_primeBelow A L hp hA).symm⟩

private theorem isMaximal_primeBelow [FiniteDimensional ℚ L] (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (primeBelow A L).IsMaximal :=
  (primeBelow_isPrime A L).isMaximal (primeBelow_ne_bot A L hp hA)

end Integers

section Localization

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private def heightOneSpectrumBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  ⟨primeBelow A L, inferInstance, primeBelow_ne_bot A L hp hA⟩

@[scoped simp] private theorem heightOneSpectrumBelow_asIdeal
    (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (heightOneSpectrumBelow A L hp hA).asIdeal = primeBelow A L := rfl

variable [FiniteDimensional ℚ L]

private theorem exists_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : algebraMap L (AlgebraicClosure ℚ) z ∈ A) :
    ∃ x s : 𝓞 L, s ∉ primeBelow A L ∧ z * s = x := by
  obtain ⟨n, d, h | h⟩ :=
    (heightOneSpectrumBelow A L hp hA).exists_primeCompl_mul_eq_or_mul_eq (K := L) z
  · exact ⟨n, d, d.2, h⟩
  · refine ⟨d, n, ?_, h⟩

    have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
      (notMem_primeBelow_iff A L).mp d.2
    rw [notMem_primeBelow_iff A L]
    refine le_antisymm (valuation_algebraMap_ringOfIntegers_le_one A L n) ?_
    have hzle : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr hz
    have hprod : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) *
        A.valuation (algebraMap L (AlgebraicClosure ℚ) ((n : 𝓞 L) : L)) = 1 := by
      rw [← map_mul, ← map_mul]
      change A.valuation (algebraMap L (AlgebraicClosure ℚ) (z * algebraMap (𝓞 L) L n)) = 1
      rw [h]
      exact hd
    calc (1 : _) = _ := hprod.symm
      _ ≤ A.valuation (algebraMap L (AlgebraicClosure ℚ) ((n : 𝓞 L) : L)) :=
          mul_le_of_le_one_left' hzle


private theorem mem_of_adicValuation_le_one (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : (heightOneSpectrumBelow A L hp hA).valuation L z ≤ 1) :
    algebraMap L (AlgebraicClosure ℚ) z ∈ A := by
  obtain ⟨n, d, h⟩ :=
    (heightOneSpectrumBelow A L hp hA).exists_primeCompl_mul_eq_of_integer z hz
  have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
    (notMem_primeBelow_iff A L).mp d.2
  have key : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) *
      A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) ≤ 1 := by
    rw [← map_mul, ← map_mul]
    change A.valuation (algebraMap L (AlgebraicClosure ℚ) (z * algebraMap (𝓞 L) L d)) ≤ 1
    rw [h]
    exact valuation_algebraMap_ringOfIntegers_le_one A L n
  rw [hd, mul_one] at key
  exact (A.valuation_le_one_iff _).mp key


private theorem isEquiv_valuation_comap_adicValuation (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.valuation.comap (algebraMap L (AlgebraicClosure ℚ))).IsEquiv
      ((heightOneSpectrumBelow A L hp hA).valuation L) := by
  refine Valuation.isEquiv_iff_val_le_one.mpr fun {z} => ?_
  rw [Valuation.comap_apply, valuation_le_one_iff]
  constructor
  · intro hz
    obtain ⟨x, s, hs, hzs⟩ := exists_mul_eq_of_mem A L hp hA z hz
    have hs1 : (heightOneSpectrumBelow A L hp hA).valuation L ((s : 𝓞 L) : L) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L)
        (v := heightOneSpectrumBelow A L hp hA)).mpr hs
    have h := congrArg ((heightOneSpectrumBelow A L hp hA).valuation L) hzs
    rw [map_mul, hs1, mul_one] at h
    rw [h]
    exact (heightOneSpectrumBelow A L hp hA).valuation_le_one (K := L) x
  · exact mem_of_adicValuation_le_one A L hp hA z

end Localization

section Ramification

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] {p : ℕ}

omit [FiniteDimensional ℚ L] in
private theorem map_span_natCast_eq :
    Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 L)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem adicValuation_natCast_eq_exp_neg_ramificationIdx (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (heightOneSpectrumBelow A L hp hA).valuation L (p : L) =
      WithZero.exp (-(Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) : ℤ)) := by
  classical
  have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hspan0 : Ideal.span {(p : 𝓞 L)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hp0
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    rwa [map_span_natCast_eq]
  rw [show (p : L) = algebraMap (𝓞 L) L (p : 𝓞 L) from (map_natCast _ p).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hp0, heightOneSpectrumBelow_asIdeal,
    Ideal.count_associates_factors_eq hspan0 (primeBelow_isPrime A L)
      (primeBelow_ne_bot A L hp hA),
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0
      (primeBelow_isPrime A L)
      (primeBelow_ne_bot A L hp hA), map_span_natCast_eq]


private theorem dvd_ramificationIdx_of_valuation_pow_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) := by
  set e := Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) with he
  set w := (heightOneSpectrumBelow A L hp hA).valuation L with hw
  have hequiv := isEquiv_valuation_comap_adicValuation A L hp hA

  have hval' : w (z ^ m) = w ((p : L) ^ a) := by
    refine (hequiv.eq_iff).mp ?_
    simp only [Valuation.comap_apply, map_pow, map_natCast]
    exact hval
  rw [map_pow, map_pow, hw, adicValuation_natCast_eq_exp_neg_ramificationIdx A L hp hA,
    ← he, ← WithZero.exp_nsmul] at hval'
  have hz0 : (heightOneSpectrumBelow A L hp hA).valuation L z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hval'
    exact WithZero.exp_ne_zero hval'.symm
  rw [← WithZero.exp_log hz0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg] at hval'

  have hdvd : (m : ℤ) ∣ (a : ℤ) * (e : ℤ) := by
    rw [← dvd_neg, ← hval']
    exact dvd_mul_right _ _
  have hdvd' : m ∣ a * e := by exact_mod_cast hdvd
  exact hcop.symm.dvd_of_dvd_mul_left hdvd'

end Ramification

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn' (A : ValuationSubring F)
    {σ : F ≃ₐ[K] F}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {a : F} (ha : a ∈ A) :
    σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hdA : (d : F ≃ₐ[K] F) • A = A := d.2
  have hmem : (d : F ≃ₐ[K] F) a ∈ A := by
    have := smul_mem_pointwise_smul (d : F ≃ₐ[K] F) a A ha
    rwa [hdA] at this
  refine ⟨hmem, ?_⟩
  rw [inertiaSubgroup, MonoidHom.mem_ker] at hd
  have h := RingEquiv.congr_fun hd (IsLocalRing.residue A ⟨a, ha⟩)
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul, RingAut.one_apply, IsLocalRing.residue_def,
    IsLocalRing.residue_def] at h
  have h2 : d • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h
  rw [valuation_lt_one_iff] at h2
  exact h2

end General

section Center

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ}

private def integralClosureToValuationSubring : integralClosure ℤ (AlgebraicClosure ℚ) →+* A :=
  (integralClosure ℤ (AlgebraicClosure ℚ)).val.toRingHom.codRestrict A.toSubring
    (coe_integralClosure_mem A)


private def center : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) :=
  (IsLocalRing.maximalIdeal A).comap (integralClosureToValuationSubring A)

private theorem mem_center_iff {b : integralClosure ℤ (AlgebraicClosure ℚ)} :
    b ∈ center A ↔ A.valuation b < 1 := by
  rw [center, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

private instance center_isPrime : (center A).IsPrime := Ideal.IsPrime.comap _

private theorem natCast_mem_center (hA : A.LiesOverPrime p) :
    (p : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ center A := by
  rw [mem_center_iff, ← mem_nonunits_iff]
  simpa using (show ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits from hA)

private theorem valuation_eq_one_of_notMem_center {s : integralClosure ℤ (AlgebraicClosure ℚ)}
    (hs : s ∉ center A) : A.valuation s = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).mpr (coe_integralClosure_mem A s))
    (not_lt.mp fun h => hs ((mem_center_iff A).mpr h))


private theorem mem_primeBelow_iff_mem_center (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : 𝓞 L) :
    x ∈ primeBelow A L ↔
      (⟨algebraMap L (AlgebraicClosure ℚ) (x : L), map_isIntegral_int _
        (NumberField.RingOfIntegers.isIntegral_coe x)⟩ :
          integralClosure ℤ (AlgebraicClosure ℚ)) ∈ center A := by
  rw [mem_primeBelow_iff, mem_center_iff]

private theorem exists_integralClosure_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), s ∉ center A ∧
      a * s = x := by
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {a}
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  let a' : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have ha' : algebraMap F (AlgebraicClosure ℚ) a' = a := rfl
  obtain ⟨x, s, hs, hxs⟩ := exists_mul_eq_of_mem A F hp hA a' (ha'.symm ▸ ha)
  refine ⟨⟨algebraMap F (AlgebraicClosure ℚ) (x : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe x)⟩,
    ⟨algebraMap F (AlgebraicClosure ℚ) (s : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe s)⟩, ?_, ?_⟩
  · rwa [← mem_primeBelow_iff_mem_center]
  · change a * algebraMap F (AlgebraicClosure ℚ) (s : F) = algebraMap F (AlgebraicClosure ℚ) (x : F)
    rw [← ha', ← map_mul, hxs]


private theorem apply_mem_and_valuation_sub_lt_one (hp : p.Prime) (hA : A.LiesOverPrime p)
    (ρ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hρ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      A.valuation (ρ b - b) < 1)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ρ a ∈ A ∧ A.valuation (ρ a - a) < 1 := by
  obtain ⟨x, s, hs, hax⟩ := exists_integralClosure_mul_eq_of_mem A hp hA a ha
  have hvs : A.valuation (s : AlgebraicClosure ℚ) = 1 := valuation_eq_one_of_notMem_center A hs
  have hvx : A.valuation (x : AlgebraicClosure ℚ) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (coe_integralClosure_mem A x)
  set c : AlgebraicClosure ℚ := ρ x - x with hc
  set c' : AlgebraicClosure ℚ := ρ s - s with hc'
  have hvc : A.valuation c < 1 := hρ x
  have hvc' : A.valuation c' < 1 := hρ s
  have hρx : ρ x = x + c := by rw [hc]; ring
  have hρs : ρ s = s + c' := by rw [hc']; ring
  have hlt : A.valuation c' < A.valuation (s : AlgebraicClosure ℚ) := by rw [hvs]; exact hvc'
  have hvρs : A.valuation (ρ s) = 1 := by
    rw [hρs, Valuation.map_add_eq_of_lt_left _ hlt, hvs]
  have hs0 : (s : AlgebraicClosure ℚ) ≠ 0 := fun h => by
    rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hρs0 : ρ s ≠ 0 := fun h => by
    rw [h, map_zero] at hvρs; exact zero_ne_one hvρs
  have hρa : ρ a = ρ x / ρ s := by
    rw [eq_div_iff hρs0, ← map_mul, hax]
  have hvρx : A.valuation (ρ x) ≤ 1 := by
    rw [hρx]
    exact Valuation.map_add_le _ hvx hvc.le
  refine ⟨?_, ?_⟩
  · rw [← A.valuation_le_one_iff, hρa, map_div₀, hvρs, div_one]
    exact hvρx
  · have ha' : a = x / s := by rw [eq_div_iff hs0, hax]
    have hdiff : ρ a - a = (c * s - x * c') / (ρ s * s) := by
      rw [hρa, ha', hρx, hρs, div_sub_div _ _ (by rw [← hρs]; exact hρs0) hs0]
      congr 1
      ring
    rw [hdiff, map_div₀, map_mul, hvρs, hvs, one_mul, div_one]
    refine Valuation.map_sub_lt _ ?_ ?_
    · rw [map_mul, hvs, mul_one]; exact hvc
    · rw [map_mul]
      calc A.valuation (x : AlgebraicClosure ℚ) * A.valuation c'
          ≤ A.valuation c' := mul_le_of_le_one_left' hvx
        _ < 1 := hvc'


private theorem mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one (hp : p.Prime)
    (hA : A.LiesOverPrime p) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), A.valuation (σ b - b) < 1) :
    σ ∈ A.inertiaSubgroupIn ℚ := by
  have key := apply_mem_and_valuation_sub_lt_one A hp hA

  have hσinv : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), A.valuation (σ⁻¹ b - b) < 1 := by
    intro b
    have hb' : IsIntegral ℤ (σ⁻¹ (b : AlgebraicClosure ℚ)) := map_isIntegral_int _ b.2
    have h := hσ ⟨_, hb'⟩
    have e : σ (σ⁻¹ (b : AlgebraicClosure ℚ)) = b := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    change A.valuation (σ (σ⁻¹ (b : AlgebraicClosure ℚ)) - σ⁻¹ b) < 1 at h
    rw [e] at h
    rwa [← Valuation.map_neg, neg_sub]

  have hstab : σ ∈ A.decompositionSubgroup ℚ := by
    rw [decompositionSubgroup, MulAction.mem_stabilizer_iff]
    ext x
    rw [mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · intro hx
      have := (key σ hσ _ hx).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    · intro hx
      exact (key σ⁻¹ hσinv _ hx).1

  refine Subgroup.mem_map.mpr ⟨⟨σ, hstab⟩, ?_, rfl⟩
  rw [inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul, RingAut.one_apply, IsLocalRing.residue_def,
    IsLocalRing.residue_def]
  apply Ideal.Quotient.eq.mpr
  rw [valuation_lt_one_iff]
  exact (key σ hσ a a.2).2

end Center

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem algebraMap_restrictNormalHom_apply [Normal ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : L) :
    algebraMap L (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom L σ x) =
      σ (algebraMap L (AlgebraicClosure ℚ) x) :=
  AlgEquiv.restrictNormal_commutes σ L x

variable [IsGalois ℚ L]

private theorem exists_lift_valuation_sub_lt_one_of_mem_inertia (τ : L ≃ₐ[ℚ] L)
    (hτ : τ ∈ (primeBelow A L).inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
        A.valuation (σ b - b) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : Algebra.IsIntegral L (AlgebraicClosure ℚ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : Normal L (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ L _
  haveI : Algebra.IsSeparable L (AlgebraicClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable ℚ L _
  haveI : IsGalois L (AlgebraicClosure ℚ) := ⟨⟩
  set Q : Ideal (𝓞 L) := primeBelow A L with hQdef
  set 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) := center A with h𝔔def
  have hτ' : ∀ x : 𝓞 L, τ • x - x ∈ Q := fun x => (AddSubgroup.mem_inertia.mp hτ) x
  have hstabτ : τ • Q = Q := Ideal.inertia_le_stabilizer Q hτ

  letI actG : MulSemiringAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := inferInstance
  letI actGI : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := Ideal.pointwiseDistribMulAction
  letI mulActGI : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toMulAction
  letI dsmulGI : DistribSMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toDistribSMul
  letI smulzGI : SMulZeroClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribSMul.toSMulZeroClass
  letI smulGI : SMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := SMulZeroClass.toSMul

  let f : 𝓞 L →+* integralClosure ℤ (AlgebraicClosure ℚ) :=
    (algebraMap (𝓞 L) (AlgebraicClosure ℚ)).codRestrict (integralClosure ℤ (AlgebraicClosure ℚ))
      fun x => (map_isIntegral_int (algebraMap (𝓞 L) (AlgebraicClosure ℚ))
        (Algebra.IsIntegral.isIntegral x))
  letI algOB : Algebra (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) := f.toAlgebra
  have hf_coe : ∀ x : 𝓞 L, ((algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x :
      integralClosure ℤ (AlgebraicClosure ℚ)) : AlgebraicClosure ℚ) =
        algebraMap L (AlgebraicClosure ℚ) (x : L) :=
    fun x => rfl
  haveI : IsScalarTower (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl

  have hmemQ : ∀ x : 𝓞 L, algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x ∈ 𝔔 ↔
      x ∈ Q := fun x => by
    rw [h𝔔def, mem_center_iff, hf_coe, hQdef, mem_primeBelow_iff]
  haveI h𝔔lies : 𝔔.LiesOver Q := ⟨by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, hmemQ]⟩

  have hres : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : 𝓞 L),
      σ • algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x =
        algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ))
          ((AlgEquiv.restrictNormalHom L σ) • x) := by
    intro σ x
    apply Subtype.ext
    change σ (algebraMap L (AlgebraicClosure ℚ) (x : L)) =
      algebraMap L (AlgebraicClosure ℚ) ((σ.restrictNormal L) (x : L))
    exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm

  let rsh : (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toFun := fun g => g.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrsh_apply : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ),
      rsh g x = g x := fun _ _ => rfl

  have hresL : ∀ g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom L (rsh g) = 1 := by
    intro g
    refine AlgEquiv.ext fun x => (algebraMap L (AlgebraicClosure ℚ)).injective ?_
    change algebraMap L (AlgebraicClosure ℚ) (((rsh g).restrictNormal L) x) =
      algebraMap L (AlgebraicClosure ℚ) x
    rw [AlgEquiv.restrictNormal_commutes, hrsh_apply]
    exact g.commutes x
  letI actL : MulSemiringAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := MulSemiringAction.compHom _ rsh
  letI actLI : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := Ideal.pointwiseDistribMulAction
  letI mulActLI : MulAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toMulAction
  letI dsmulLI : DistribSMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toDistribSMul
  letI smulzLI : SMulZeroClass (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribSMul.toSMulZeroClass
  letI smulLI : SMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := SMulZeroClass.toSMul
  have hrs : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (b : integralClosure ℤ (AlgebraicClosure ℚ)), g • b = rsh g • b := fun _ _ => rfl
  have hrsI : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (J : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))), g • J = rsh g • J := by
    intro g J
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, hrs]

  haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (𝓞 L)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨fun g a b => by
    apply Subtype.ext
    change g ((algebraMap L (AlgebraicClosure ℚ) (a : L)) * (b : AlgebraicClosure ℚ)) =
      algebraMap L (AlgebraicClosure ℚ) (a : L) * g (b : AlgebraicClosure ℚ)
    rw [map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace (integralClosure ℤ (AlgebraicClosure ℚ)) := ⊥
  haveI : DiscreteTopology (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨rfl⟩
  haveI : ContinuousSMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional L (IntermediateField.adjoin L {(b : AlgebraicClosure ℚ)}) :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (b : AlgebraicClosure ℚ))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen
        (IntermediateField.adjoin L {(b : AlgebraicClosure ℚ)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g (b : AlgebraicClosure ℚ) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self L (b : AlgebraicClosure ℚ))
  haveI : Algebra.IsInvariant (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ))
      (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) := ⟨fun b hb => by
    have hb' : (b : AlgebraicClosure ℚ) ∈ Set.range (algebraMap L (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : integralClosure ℤ (AlgebraicClosure ℚ) => (z : AlgebraicClosure ℚ))
        (hb g)
    obtain ⟨y, hy⟩ := hb'
    have hyint : IsIntegral ℤ y := by
      obtain ⟨q, hq, hq0⟩ := (b.2 : IsIntegral ℤ (b : AlgebraicClosure ℚ))
      refine ⟨q, hq, (algebraMap L (AlgebraicClosure ℚ)).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hy]
      convert hq0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
    refine ⟨⟨y, by exact hyint⟩, Subtype.ext ?_⟩
    exact (hf_coe _).trans hy⟩

  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (AlgebraicClosure ℚ) τ
  have hunder : Ideal.under (𝓞 L) (σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) =
      Ideal.under (𝓞 L) 𝔔 := by
    ext x
    rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hres,
      hmemQ, hmemQ, map_inv, hσ₀]
    conv_rhs => rw [← hstabτ]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  haveI : 𝔔.IsPrime := h𝔔def ▸ center_isPrime A
  haveI : (σ₀ • 𝔔).IsPrime := Ideal.IsPrime.smul σ₀
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := 𝓞 L) (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) 𝔔 hunder

  have hσ₁𝔔 : (rsh g * σ₀) • 𝔔 = 𝔔 := by rw [mul_smul, ← hrsI, ← hg]
  have hσ₁L : AlgEquiv.restrictNormalHom L (rsh g * σ₀) = τ := by
    rw [map_mul, hresL, one_mul, hσ₀]

  have hσ₁stab : rsh g * σ₀ ∈
      MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝔔 := hσ₁𝔔
  let φ₀ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃ₐ[ℤ ⧸ 𝔔.under ℤ]
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) :=
    Ideal.Quotient.stabilizerHom 𝔔 (𝔔.under ℤ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ⟨rsh g * σ₀, hσ₁stab⟩
  have hστQ : ∀ x : 𝓞 L, Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) •
      algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x) =
        Ideal.Quotient.mk 𝔔 (algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x) := by
    intro x
    rw [Ideal.Quotient.eq, hres, hσ₁L, ← map_sub, hmemQ]
    exact hτ' x
  let φ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃ₐ[𝓞 L ⧸ Q]
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) :=
    AlgEquiv.ofRingEquiv (f := (φ₀ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃+*
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔))) (by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      exact hστQ x)
  have hφ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      φ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  obtain ⟨t, ht⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) Q 𝔔 φ
  have ht' : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      Ideal.Quotient.mk 𝔔 ((t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) := by
    intro b
    have h := congrArg (fun e => e (Ideal.Quotient.mk 𝔔 b)) ht
    simpa only [Ideal.Quotient.stabilizerHom_apply, hφ, Subgroup.smul_def,
      Submonoid.smul_def] using h

  refine ⟨(rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * (rsh g * σ₀), ?_, ?_⟩
  · rw [map_mul, map_inv, hresL, inv_one, one_mul, hσ₁L]
  · intro b
    have h1 : (rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b ∈ 𝔔 := by
      rw [← Ideal.Quotient.eq]
      exact (ht' b).symm
    have h2 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          ((rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) ∈ 𝔔 := by
      have hmem := (Ideal.smul_mem_pointwise_smul_iff
        (a := ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
          AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))).mpr h1
      rwa [MulAction.mem_stabilizer_iff.mp (t⁻¹).2] at hmem
    have h3 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          ((rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        ((rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * (rsh g * σ₀)) • b - b := by
      rw [Subgroup.coe_inv, smul_sub, inv_smul_smul, hrs, map_inv]
      simp only [mul_smul]
    rw [h3] at h2
    exact (mem_center_iff A).mp h2


private theorem exists_mem_inertiaSubgroupIn_restrictNormalHom_eq (hp : p.Prime)
    (hA : A.LiesOverPrime p)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ (primeBelow A L).inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσL, hσ⟩ := exists_lift_valuation_sub_lt_one_of_mem_inertia A L τ hτ
  exact ⟨σ, mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one A hp hA σ hσ, hσL⟩

end Lift

section Dictionary

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem coe_smul_ringOfIntegers (τ : L ≃ₐ[ℚ] L) (x : 𝓞 L) :
    ((τ • x : 𝓞 L) : L) = τ (x : L) :=
  rfl

variable [IsGalois ℚ L]

private theorem map_restrictNormalHom_inertiaSubgroupIn_le :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) ≤
      (primeBelow A L).inertia (L ≃ₐ[ℚ] L) := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  change AlgEquiv.restrictNormalHom L σ • x - x ∈ primeBelow A L
  rw [mem_primeBelow_iff]
  have hcoe : (((AlgEquiv.restrictNormalHom L σ • x - x : 𝓞 L)) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - x := rfl
  rw [hcoe, map_sub, algebraMap_restrictNormalHom_apply]
  exact (valuation_sub_lt_one_of_mem_inertiaSubgroupIn' A hσ
    (algebraMap_ringOfIntegers_mem A L x)).2


private theorem map_restrictNormalHom_inertiaSubgroupIn_eq_inertia (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) =
      (primeBelow A L).inertia (L ≃ₐ[ℚ] L) := by
  refine le_antisymm (map_restrictNormalHom_inertiaSubgroupIn_le A L) fun τ hτ => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_mem_inertiaSubgroupIn_restrictNormalHom_eq A L hp hA τ hτ
  exact Subgroup.mem_map_of_mem _ hσ

variable [FiniteDimensional ℚ L]

/-- Let `A` be a valuation subring of `ℚ̄` lying over a prime `p`, and let `L` be a finite Galois
subextension of `ℚ̄ / ℚ`. Then `𝓞 L` lies in `A`, its center `{x ∈ 𝓞 L | A.valuation x < 1}` is
a maximal ideal containing `p`, and the inertia group of the center is the image of the inertia
subgroup of `A` under restriction to `L`. -/
public theorem exists_isMaximal_inertia_eq_map_restrictNormalHom (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q ∧
      (∀ x : 𝓞 L, A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) ≤ 1) ∧
      (∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) < 1) ∧
      (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) =
        Q.inertia (L ≃ₐ[ℚ] L) :=
  ⟨primeBelow A L, isMaximal_primeBelow A L hp hA, natCast_mem_primeBelow A L hA,
    valuation_algebraMap_ringOfIntegers_le_one A L, fun _ => mem_primeBelow_iff A L,
    map_restrictNormalHom_inertiaSubgroupIn_eq_inertia A L hp hA⟩

attribute [local instance] Ideal.Quotient.field in

private theorem card_inertia_primeBelow_eq_ramificationIdx (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Nat.card ((primeBelow A L).inertia (L ≃ₐ[ℚ] L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := primeBelow_liesOver A L hp hA
  haveI := isMaximal_primeBelow A L hp hA
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)})
      (primeBelow A L),
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (primeBelow A L)
      (L ≃ₐ[ℚ] L)]
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (primeBelow A L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)).symm


private theorem card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) := by
  rw [map_restrictNormalHom_inertiaSubgroupIn_eq_inertia A L hp hA,
    card_inertia_primeBelow_eq_ramificationIdx A L hp hA]

omit [IsGalois ℚ L] in

private theorem ramificationIdx_primeBelow_ne_zero (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) ≠ 0 :=
  haveI := primeBelow_liesOver A L hp hA
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)

private theorem dvd_card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime)
    (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) := by
  rw [card_map_restrictNormalHom_inertiaSubgroupIn A L hp hA]
  exact dvd_ramificationIdx_of_valuation_pow_eq A L hp hA z hm hcop hval

private theorem map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥ ↔
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) = 1 := by
  rw [← Subgroup.card_eq_one, card_map_restrictNormalHom_inertiaSubgroupIn A L hp hA]

omit [IsGalois ℚ L] in

private theorem ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (primeBelow A L) = 1 ↔
      Algebra.IsUnramifiedAt ℤ (primeBelow A L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := primeBelow_liesOver A L hp hA
  have e := Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (primeBelow A L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)
  rw [e, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]


private theorem map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff_isUnramifiedAt (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥ ↔
      Algebra.IsUnramifiedAt ℤ (primeBelow A L) := by
  rw [map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff A L hp hA,
    ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt A L hp hA]

end Dictionary


section Cyclotomic

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem map_restrictNormalHom_inertiaSubgroupIn_eq_top_of_isCyclotomicExtension
    [FiniteDimensional ℚ L] [IsGalois ℚ L] [IsCyclotomicExtension {p} ℚ L]
    (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := primeBelow_liesOver A L hp hA
  refine Subgroup.eq_top_of_card_eq _ ?_
  have e := Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (primeBelow A L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)
  rw [card_map_restrictNormalHom_inertiaSubgroupIn A L hp hA, e,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p L (primeBelow A L),
    IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
      (Polynomial.cyclotomic.irreducible_rat hp.pos),
    Nat.totient_prime hp]


private theorem exists_mem_inertiaSubgroupIn_cyclotomic_character (hp : p.Prime)
    (hA : A.LiesOverPrime p)
    (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
      σ μ = μ ^ (a : ZMod p).val := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : IsCyclotomicExtension {p} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p} ℚ L
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L (AlgebraicClosure ℚ)) hζ
      (algebraMap L (AlgebraicClosure ℚ)).injective

  let χ := hζL.autToPow ℚ
  have hχ : Function.Bijective χ := by
    refine (Nat.bijective_iff_injective_and_card χ).mpr ⟨hζL.autToPow_injective ℚ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
        (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨τ, hτ⟩ := hχ.2 a
  have hτζ : τ ζL = ζL ^ (a : ZMod p).val := by
    rw [← hτ]
    exact (hζL.autToPow_spec ℚ τ).symm

  have hτmem : τ ∈ (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) := by
    rw [map_restrictNormalHom_inertiaSubgroupIn_eq_top_of_isCyclotomicExtension A L hp hA]
    exact Subgroup.mem_top τ
  obtain ⟨σ, hσ, hσL⟩ := Subgroup.mem_map.mp hτmem
  refine ⟨σ, hσ, fun μ hμ => ?_⟩
  have hσζ : σ ζ = ζ ^ (a : ZMod p).val := by
    change σ (algebraMap L (AlgebraicClosure ℚ) ζL) = (algebraMap L (AlgebraicClosure ℚ) ζL) ^ _
    rw [← algebraMap_restrictNormalHom_apply, hσL, hτζ, map_pow]
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm]

end Cyclotomic

/-- Inertia at a prime above `p` surjects onto the mod-`p` cyclotomic
character: for every unit `a` modulo `p` there is an element of the
inertia subgroup at a valuation subring of `AlgebraicClosure ℚ` lying
over `p` that sends every `p`-th root of unity `μ` to `μ ^ a`. This is
the total ramification of `ℚ(ζ_p)` at `p`, lifted to the algebraic
closure. -/
public theorem exists_mem_inertiaSubgroupIn_apply_eq_pow
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
      σ μ = μ ^ (a : ZMod p).val :=
  exists_mem_inertiaSubgroupIn_cyclotomic_character A hp hA a


section PrimePowerCyclotomic

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem valuation_one_sub_pow_le {ζ : AlgebraicClosure ℚ} (hζ : IsIntegral ℤ ζ)
    (i : ℕ) :
    A.valuation (1 - ζ ^ i) ≤ A.valuation (1 - ζ) := by
  have hζA : ζ ∈ A := mem_of_isIntegral_int A hζ
  have hS : (∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
    sum_mem fun j _ => pow_mem hζA j
  rw [← geom_sum_mul_neg ζ i, map_mul]
  calc A.valuation (∑ j ∈ Finset.range i, ζ ^ j) * A.valuation (1 - ζ)
      ≤ 1 * A.valuation (1 - ζ) :=
        mul_le_mul_left ((A.valuation_le_one_iff _).mpr hS) _
    _ = A.valuation (1 - ζ) := one_mul _

private theorem valuation_one_sub_eq_of_mem_primitiveRoots {n : ℕ} (hn : 0 < n)
    {ζ μ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : μ ∈ primitiveRoots n (AlgebraicClosure ℚ)) :
    A.valuation (1 - μ) = A.valuation (1 - ζ) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hμ' : IsPrimitiveRoot μ n := (mem_primitiveRoots hn).mp hμ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
  obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm (valuation_one_sub_pow_le A (hζ.isIntegral hn) i) ?_
  calc A.valuation (1 - ζ) = A.valuation (1 - (ζ ^ i) ^ j) := by rw [hj]
    _ ≤ A.valuation (1 - ζ ^ i) :=
        valuation_one_sub_pow_le A ((hζ.isIntegral hn).pow i) j

private theorem valuation_one_sub_pow_totient_eq {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 0 < k) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    A.valuation (1 - ζ) ^ Nat.totient (p ^ k) = A.valuation (p : AlgebraicClosure ℚ) := by
  haveI := Fact.mk hp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  have hpos : 0 < p ^ (k' + 1) := pow_pos hp.pos _
  have hprod : (p : AlgebraicClosure ℚ) =
      ∏ μ ∈ primitiveRoots (p ^ (k' + 1)) (AlgebraicClosure ℚ), (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime_pow (R := AlgebraicClosure ℚ)
      (p := p) k'
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    exact h.symm
  rw [hprod, map_prod,
    Finset.prod_congr rfl fun μ hμ => valuation_one_sub_eq_of_mem_primitiveRoots A hpos hζ hμ,
    Finset.prod_const, hζ.card_primitiveRoots]

private theorem exists_mem_inertiaSubgroupIn_prime_pow_character
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (k : ℕ) (a : (ZMod (p ^ k))ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 →
      σ μ = μ ^ (a : ZMod (p ^ k)).val := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, Subgroup.one_mem _, fun μ hμ => ?_⟩
    rw [pow_zero, pow_one] at hμ
    subst hμ
    rw [one_pow]
    exact map_one _
  haveI : NeZero (p ^ k) := ⟨(pow_pos hp.pos k).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ k)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : IsCyclotomicExtension {p ^ k} ℚ L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p ^ k} ℚ L
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL (p ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L (AlgebraicClosure ℚ)) hζ
      (algebraMap L (AlgebraicClosure ℚ)).injective
  have hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) (1 - ζL)) ^
        Nat.totient (p ^ k) =
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 1 := by
    have hmap : algebraMap L (AlgebraicClosure ℚ) (1 - ζL) = 1 - ζ := by
      rw [map_sub, map_one]; rfl
    rw [hmap, pow_one, valuation_one_sub_pow_totient_eq A hp hk hζ]
  have hdvd : Nat.totient (p ^ k) ∣
      Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) :=
    dvd_card_map_restrictNormalHom_inertiaSubgroupIn A L hp hA (1 - ζL)
      (Nat.totient_pos.mpr (pow_pos hp.pos k)) (Nat.coprime_one_left _) hval
  have hGcard : Nat.card (L ≃ₐ[ℚ] L) = Nat.totient (p ^ k) := by
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p ^ k) L
        (Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos k))]
  have himtop : (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    have hdvd' := Subgroup.card_subgroup_dvd_card
      ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L))
    rw [hGcard] at hdvd' ⊢
    exact Nat.dvd_antisymm hdvd' hdvd
  let χ := hζL.autToPow ℚ
  have hχ : Function.Bijective χ := by
    refine (Nat.bijective_iff_injective_and_card χ).mpr ⟨hζL.autToPow_injective ℚ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p ^ k) L
        (Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos k)),
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨τ, hτ⟩ := hχ.2 a
  have hτζ : τ ζL = ζL ^ (a : ZMod (p ^ k)).val := by
    rw [← hτ]
    exact (hζL.autToPow_spec ℚ τ).symm
  have hτmem : τ ∈ (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) := by
    rw [himtop]; exact Subgroup.mem_top τ
  obtain ⟨σ, hσ, hσL⟩ := Subgroup.mem_map.mp hτmem
  refine ⟨σ, hσ, ?_⟩
  have hσζ : σ ζ = ζ ^ (a : ZMod (p ^ k)).val := by
    change σ (algebraMap L (AlgebraicClosure ℚ) ζL) =
      (algebraMap L (AlgebraicClosure ℚ) ζL) ^ (a : ZMod (p ^ k)).val
    rw [← algebraMap_restrictNormalHom_apply L σ ζL, hσL, hτζ, map_pow]
  intro μ hμ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm]

end PrimePowerCyclotomic

/-- Inertia at a prime above `p` surjects onto the mod-`p ^ k` cyclotomic
character: for every unit `a` modulo `p ^ k` there is an element of the
inertia subgroup at a valuation subring of `AlgebraicClosure ℚ` lying
over `p` that sends every `p ^ k`-th root of unity `μ` to `μ ^ a`. -/
public theorem exists_mem_inertiaSubgroupIn_apply_eq_pow_prime_pow
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (k : ℕ) (a : (ZMod (p ^ k))ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 →
      σ μ = μ ^ (a : ZMod (p ^ k)).val :=
  exists_mem_inertiaSubgroupIn_prime_pow_character A hp hA k a

section KummerDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private lemma exists_forall_apply_eq_pow {n : ℕ} (hn : 0 < n) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) (σ : L ≃ₐ[K] L) :
    ∃ a : ℕ, ∀ η : L, η ^ n = 1 → σ η = η ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : (σ ζ) ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨a, fun η hη => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

private theorem exists_forall_apply_eq_and_pow_eq_pow {n : ℕ} (hn : 0 < n)
    (I : Subgroup (L ≃ₐ[K] L)) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) (g₀ : L ≃ₐ[K] L) (hg₀ : g₀ ∈ I)
    (hg₀act : ∀ η : L, η ^ n = 1 → g₀ η = η ^ 2)
    (w : L) (hw : ∀ σ ∈ I, σ ζ = ζ → σ w = w) (hx : ∀ σ ∈ I, σ (w ^ n) = w ^ n) :
    ∃ w' : L, (∀ σ ∈ I, σ w' = w') ∧ w' ^ n = w ^ n := by
  by_cases hw0 : w = 0
  · exact ⟨0, fun σ _ => map_zero σ, by rw [hw0]⟩
  let η : (L ≃ₐ[K] L) → L := fun σ => σ w / w
  have hηw : ∀ σ : L ≃ₐ[K] L, σ w = η σ * w := fun σ => by
    change σ w = σ w / w * w
    rw [div_mul_cancel₀ _ hw0]
  have hηn : ∀ σ ∈ I, η σ ^ n = 1 := fun σ hσ => by
    change (σ w / w) ^ n = 1
    rw [div_pow, ← map_pow, hx σ hσ, div_self (pow_ne_zero _ hw0)]
  have hη0 : ∀ σ ∈ I, η σ ≠ 0 := fun σ hσ h => by
    have h1 := hηn σ hσ
    rw [h, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  have key : ∀ σ ∈ I, σ (η g₀) = η σ * η g₀ := by
    intro σ hσ
    obtain ⟨a, ha⟩ := exists_forall_apply_eq_pow hn hζ σ
    have hζa : (ζ ^ a) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hL : (σ * g₀) ζ = ζ ^ (2 * a) := by
      rw [AlgEquiv.mul_apply, hg₀act ζ hζ.pow_eq_one, map_pow, ha ζ hζ.pow_eq_one,
        ← pow_mul, mul_comm]
    have hR : (g₀ * σ) ζ = ζ ^ (2 * a) := by
      rw [AlgEquiv.mul_apply, ha ζ hζ.pow_eq_one, hg₀act _ hζa, ← pow_mul, mul_comm]
    have hdI : (g₀ * σ)⁻¹ * (σ * g₀) ∈ I :=
      I.mul_mem (I.inv_mem (I.mul_mem hg₀ hσ)) (I.mul_mem hσ hg₀)
    have hdζ : ((g₀ * σ)⁻¹ * (σ * g₀)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, hL, ← hR, ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
    have hdw := hw _ hdI hdζ
    have hcommw : (σ * g₀) w = (g₀ * σ) w := by
      have h2 := congrArg (g₀ * σ) hdw
      rwa [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul] at h2
    have hL' : (σ * g₀) w = σ (η g₀) * η σ * w := by
      rw [AlgEquiv.mul_apply, hηw g₀, map_mul, hηw σ, mul_assoc]
    have hR' : (g₀ * σ) w = η σ ^ 2 * η g₀ * w := by
      rw [AlgEquiv.mul_apply, hηw σ, map_mul, hg₀act _ (hηn σ hσ), hηw g₀, mul_assoc]
    rw [hL', hR'] at hcommw
    have h3 : σ (η g₀) * η σ = η σ ^ 2 * η g₀ := mul_right_cancel₀ hw0 hcommw
    apply mul_right_cancel₀ (hη0 σ hσ)
    rw [h3]
    ring
  refine ⟨w / η g₀, fun σ hσ => ?_, ?_⟩
  · rw [map_div₀, key σ hσ, hηw σ, mul_comm (η σ) w, mul_comm (η σ) (η g₀),
      mul_div_mul_right _ _ (hη0 σ hσ)]
  · rw [div_pow, hηn g₀ hg₀, div_one]

end KummerDescent

/-- Kummer descent along the inertia subgroup: if every inertia element
fixing a primitive `p ^ N`-th root of unity `ζ` also fixes `w`, and every
inertia element fixes `w ^ (p ^ N)`, then some `w'` fixed by the whole
inertia subgroup satisfies `w' ^ (p ^ N) = w ^ (p ^ N)`. The odd prime
hypothesis supplies an inertia element acting by squaring on roots of
unity, which forces the Kummer cocycle to be a coboundary. -/
public theorem exists_inertia_fixed_and_pow_eq_pow_of_isPrimitiveRoot
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (w : AlgebraicClosure ℚ)
    (hw : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ζ = ζ → σ w = w)
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (w ^ p ^ N) = w ^ p ^ N) :
    ∃ w' : AlgebraicClosure ℚ, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧
      w' ^ p ^ N = w ^ p ^ N := by
  have hn : 0 < p ^ N := pow_pos hp.pos N
  have h2 : Nat.Coprime 2 (p ^ N) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_right N
  obtain ⟨g₀, hg₀, hg₀act⟩ :=
    exists_mem_inertiaSubgroupIn_apply_eq_pow_prime_pow P hp hP N
      (ZMod.unitOfCoprime 2 h2)
  refine exists_forall_apply_eq_and_pow_eq_pow hn (P.inertiaSubgroupIn ℚ) hζ g₀ hg₀ ?_ w hw hx
  intro η hη
  have hmod : η ^ (2 % p ^ N) = η ^ 2 := by
    conv_rhs => rw [← Nat.div_add_mod 2 (p ^ N), pow_add, pow_mul, hη, one_pow, one_mul]
  have hthis := hg₀act η hη
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, hmod] at hthis
  convert hthis using 1


end ValuationSubring

end
