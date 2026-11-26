/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.KoszulFamilyPrimeFiltration
public import Mathlib.RingTheory.KrullDimension.Regular
public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientRegularQuotient

/-!
# Local dimension vanishing and Koszul Euler multiplicities

Let R be noetherian and local, a a family of n elements in its maximal ideal and M finitely
generated. Assume R/(ideal(a)+Ann M) has finite length. If the support dimension of M is below
n, the coefficient Koszul Euler invariant is zero.

With support dimension at most n, each prime-filtration factor of nonzero Euler value is
minimal in the module support. Its occurrence count is the localized length of M, giving the
distinct-factor sum of generic multiplicities times factor Euler values. The coefficient
module universe remains independent of the ring universe.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Module

variable (R : Type u) [CommRing R]

/-- A support prime quotient has no larger support dimension.

For finite M and p in its support, dim Supp(R/p) ≤ dim Supp(M). -/
theorem supportDim_quotient_le_of_mem_support
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    Module.supportDim R (R ⧸ p.asIdeal) ≤ Module.supportDim R M := by
  have hAnn : Module.annihilator R M ≤ p.asIdeal :=
    Module.mem_support_iff_of_finite.mp hp
  let f : Module.support R (R ⧸ p.asIdeal) → Module.support R M := fun q =>
    ⟨q.1, Module.mem_support_iff_of_finite.mpr (hAnn.trans (by
      have hq := Module.mem_support_iff_of_finite.mp q.2
      rw [Ideal.annihilator_quotient] at hq
      exact hq))⟩
  exact Order.krullDim_le_of_strictMono f (fun _ _ h => h)

/-- A strict inclusion of support primes lowers quotient dimension.

For support primes q<p and dim Supp(M)≤n, the quotient R/p has support dimension below n. -/
theorem supportDim_quotient_lt_of_lt_of_mem_support
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p q : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hq : q ∈ Module.support R M) (hqp : q < p) {n : ℕ}
    (hdim : Module.supportDim R M ≤ n) :
    Module.supportDim R (R ⧸ p.asIdeal) < n := by
  have hAnn : Module.annihilator R M ≤ p.asIdeal :=
    Module.mem_support_iff_of_finite.mp hp
  let f : Module.support R (R ⧸ p.asIdeal) → Module.support R M := fun r =>
    ⟨r.1, Module.mem_support_iff_of_finite.mpr (hAnn.trans (by
      have hr := Module.mem_support_iff_of_finite.mp r.2
      rw [Ideal.annihilator_quotient] at hr
      exact hr))⟩
  have hf : StrictMono f := fun _ _ h => h
  apply Order.krullDim_lt_coe_iff.mpr
  intro l
  have hhead : (⟨q, hq⟩ : Module.support R M) < (l.map f hf).head := by
    have hl := Module.mem_support_iff_of_finite.mp l.head.2
    rw [Ideal.annihilator_quotient] at hl
    change q.asIdeal < l.head.1.asIdeal
    exact lt_of_lt_of_le hqp hl
  have hlength := (Order.LTSeries.length_le_krullDim
    ((l.map f hf).cons ⟨q, hq⟩ hhead)).trans hdim
  have hlen : l.length + 1 ≤ n := by
    simpa only [RelSeries.cons_length, LTSeries.map_length, Nat.cast_le] using hlength
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen

end Module

namespace KoszulComplex

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}

private theorem familyTensorCoefficientEuler_eq_zero_of_supportDim_lt_sameUniverse
    (a : Fin n → R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R M < n) :
    familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot = 0 := by
  classical
  induction n generalizing M with
  | zero =>
      have hbot : Module.supportDim R M = ⊥ := WithBot.lt_coe_bot.mp hdim
      have hsub : Subsingleton M := (Module.supportDim_eq_bot_iff_subsingleton R M).mp hbot
      have hsupport : Module.support R M = ∅ := Module.support_eq_empty_iff.mpr hsub
      obtain ⟨d⟩ := Module.exists_koszulFamilyEulerPrimeDecomposition R a M hquot
      have hnil : d.factors = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro f hf
        have hp := d.factor_mem_support f hf
        rw [hsupport] at hp
        exact hp
      rw [d.eq_sum_familyTensorCoefficientEuler R hquot, hnil]
      simp
  | succ n ih =>
      obtain ⟨d⟩ := Module.exists_koszulFamilyEulerPrimeDecomposition R a M hquot
      have hfactor : ∀ f ∈ d.factors, f.value R = 0 := by
        intro f hf
        let p := f.prime.asIdeal
        let N := R ⧸ p
        let : p.IsPrime := f.prime.isPrime
        have hquotp : Module.length R
            (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R N)) ≠ ⊤ := by
          change Module.length R (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R (R ⧸ p))) ≠ ⊤
          rw [Ideal.annihilator_quotient]
          exact f.quotient_length_ne_top
        have hdimN : Module.supportDim R N < n + 1 :=
          (Module.supportDim_quotient_le_of_mem_support R M f.prime
            (d.factor_mem_support f hf)).trans_lt hdim
        change familyTensorCoefficientEuler R a (ModuleCat.of R N) hquotp = 0
        by_cases hall : ∀ i, a i ∈ p
        · apply familyTensorCoefficientEuler_eq_zero_of_coefficients_annihilate
          · intro i
            change a i ∈ Module.annihilator R (R ⧸ p)
            rw [Ideal.annihilator_quotient]
            exact hall i
          · exact Nat.succ_ne_zero n
        · obtain ⟨i, hi⟩ := not_forall.mp hall
          let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap i (Fin.last n)
          let a' : Fin (n + 1) → R := fun j => a (e.symm j)
          have hlast : a' (Fin.last n) ∉ p := by simpa [a', e] using hi
          have ha' : ∀ j, a' j ∈ IsLocalRing.maximalIdeal R := fun j => ha (e.symm j)
          have hquot' : Module.length R
              (R ⧸ (Ideal.span (Set.range a') ⊔ Module.annihilator R N)) ≠ ⊤ := by
            change Module.length R
              (R ⧸ (Ideal.span (Set.range (fun j => a (e.symm j))) ⊔ Module.annihilator R N)) ≠ ⊤
            rw [familyReindex_range R a e]
            exact hquotp
          have hreg : IsSMulRegular N (a' (Fin.last n)) := by
            intro x y hxy
            change Ideal.Quotient.mk p (a' (Fin.last n)) * x =
              Ideal.Quotient.mk p (a' (Fin.last n)) * y at hxy
            exact mul_left_cancel₀ (Ideal.Quotient.eq_zero_iff_mem.not.mpr hlast) hxy
          let Q := QuotSMulTop (a' (Fin.last n)) N
          have hdrop : Module.supportDim R Q + 1 = Module.supportDim R N :=
            Module.supportDim_quotSMulTop_succ_eq_supportDim
              (R := R) (M := N) hreg (ha' (Fin.last n))
          have hdimQ : Module.supportDim R Q < n := by
            by_contra hnot
            have hle : (n : WithBot ENat) ≤ Module.supportDim R Q := le_of_not_gt hnot
            have hle' : (n + 1 : ℕ) ≤ Module.supportDim R Q + 1 := by
              simpa only [Nat.cast_add_one, add_comm] using add_le_add_right hle (1 : WithBot ENat)
            exact (not_le_of_gt hdimN) (hle'.trans_eq hdrop)
          rw [familyTensorCoefficientEuler_reindex R a (ModuleCat.of R N) e hquotp hquot',
            familyTensorCoefficientEuler_eq_of_last_regular R a' (ModuleCat.of R N) hreg hquot']
          exact ih (fun j : Fin n => a' j.castSucc) Q
            (familyTensorCoefficientQuotient_length_ne_top R a' (ModuleCat.of R N) hquot')
            (fun j => ha' j.castSucc) hdimQ
      rw [d.eq_sum_familyTensorCoefficientEuler R hquot]
      rw [List.map_congr_left hfactor]
      simp

/-- The Koszul Euler invariant vanishes below the family-size dimension.

For the stated local family, finite post-quotient and finite M, support dimension below n
gives Euler value zero. -/
theorem familyTensorCoefficientEuler_eq_zero_of_supportDim_lt
    (a : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R M < n) :
    familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot = 0 := by
  obtain ⟨d⟩ := Module.exists_koszulFamilyEulerPrimeDecomposition R a M hquot
  have hfactor : ∀ f ∈ d.factors, f.value R = 0 := by
    intro f hf
    have hquotp : Module.length R (R ⧸
        (Ideal.span (Set.range a) ⊔ Module.annihilator R (R ⧸ f.prime.asIdeal))) ≠ ⊤ := by
      rw [Ideal.annihilator_quotient]
      exact f.quotient_length_ne_top
    change familyTensorCoefficientEuler R a (ModuleCat.of R (R ⧸ f.prime.asIdeal)) hquotp = 0
    exact familyTensorCoefficientEuler_eq_zero_of_supportDim_lt_sameUniverse R a
      (R ⧸ f.prime.asIdeal) hquotp ha
      ((Module.supportDim_quotient_le_of_mem_support R M f.prime
        (d.factor_mem_support f hf)).trans_lt hdim)
  rw [d.eq_sum_familyTensorCoefficientEuler R hquot]
  rw [List.map_congr_left hfactor]
  simp

end KoszulComplex

namespace Module

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}

/-- Nonzero Koszul Euler factors are minimal in support.

With all coefficients in the maximal ideal and support dimension at most n, each listed factor
of nonzero value satisfies the minimal-support condition. -/
theorem KoszulFamilyEulerPrimeDecomposition.factor_minimal_support_of_value_ne_zero_of_supportDim_le
    {a : Fin n → R} {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : KoszulFamilyEulerPrimeDecomposition R a M)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R) (hdim : Module.supportDim R M ≤ n)
    (f : KoszulFamilyEulerPrimeFactor R a) (hf : f ∈ d.factors) (hvalue : f.value R ≠ 0) :
    ∀ p : PrimeSpectrum R, p ∈ Module.support R M → p.asIdeal ≤ f.prime.asIdeal → p = f.prime := by
  intro p hp hle
  by_contra hne
  have hlt : p < f.prime := lt_of_le_of_ne (show p ≤ f.prime from hle) hne
  have hdimf : Module.supportDim R (R ⧸ f.prime.asIdeal) < n :=
    supportDim_quotient_lt_of_lt_of_mem_support R M f.prime p
      (d.factor_mem_support f hf) hp hlt hdim
  have hquotf : Module.length R (R ⧸
      (Ideal.span (Set.range a) ⊔ Module.annihilator R (R ⧸ f.prime.asIdeal))) ≠ ⊤ := by
    rw [Ideal.annihilator_quotient]
    exact f.quotient_length_ne_top
  apply hvalue
  change KoszulComplex.familyTensorCoefficientEuler R a
    (ModuleCat.of R (R ⧸ f.prime.asIdeal)) hquotf = 0
  exact KoszulComplex.familyTensorCoefficientEuler_eq_zero_of_supportDim_lt
    R a (R ⧸ f.prime.asIdeal) hquotf ha hdimf

open Classical in
/-- The local Koszul Euler sum weighted by localized lengths.

Under the family-size support-dimension bound, the coefficient Euler invariant is the
distinct-factor sum of localized module lengths times prime-factor values. -/
theorem KoszulFamilyEulerPrimeDecomposition.eq_sum_localizedLength_mul_of_supportDim_le
    {a : Fin n → R} {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : KoszulFamilyEulerPrimeDecomposition R a M)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R) (hdim : Module.supportDim R M ≤ n) :
    KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot =
      ∑ f ∈ d.factors.toFinset,
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) * f.value R := by
  apply d.eq_sum_localizedLength_mul R hquot
  exact d.factor_minimal_support_of_value_ne_zero_of_supportDim_le R ha hdim

open Classical in
/-- Existence of the local generic-multiplicity Koszul Euler formula.

For the stated finite coefficient and local dimension hypotheses, a prime decomposition
supplies the localized-length weighted sum. -/
theorem exists_koszulFamilyEulerPrimeDecomposition_localizedLength_mul
    (a : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R) (hdim : Module.supportDim R M ≤ n) :
    ∃ d : KoszulFamilyEulerPrimeDecomposition R a M,
      KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot =
        ∑ f ∈ d.factors.toFinset,
          ((Module.length (Localization.AtPrime f.prime.asIdeal)
            (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) * f.value R := by
  obtain ⟨d⟩ := exists_koszulFamilyEulerPrimeDecomposition R a M hquot
  exact ⟨d, d.eq_sum_localizedLength_mul_of_supportDim_le R hquot ha hdim⟩

end Module
