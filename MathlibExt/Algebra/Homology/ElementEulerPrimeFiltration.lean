/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.ElementEuler
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.KrullDimension.Module

/-!
# Prime-factor decomposition of a one-element Euler invariant

For a finitely generated module over a noetherian ring, finite length of M/rM gives finite
multiplication kernel and cokernel data and a finite list of prime-quotient factors. The list
records multiplicities, its primes lie in the support of M, and its localized length sums and
Euler sum recover those of M.

A factor R/p contributes zero when r ∈ p and otherwise contributes ℓ_R((R/p)/r(R/p)). At a
prime satisfying the stated minimal-support condition, the localized length of M equals its
occurrence count. Over a local ring with support dimension at most one and r in the maximal
ideal, factors whose primes exclude r have that minimality, giving the generic-multiplicity
formula.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Module

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- A prime quotient with finite multiplication lengths.

Record a prime p and finite kernel/cokernel length data for multiplication by r on R/p. -/
structure ElementEulerPrimeFactor (r : R) where
  /-- The prime of an Euler factor.

This prime p determines the factor module R/p. -/
  prime : PrimeSpectrum R
/-- Finite multiplication data of a prime Euler factor.

The multiplication kernel and cokernel of r on R/p have finite R-length. -/
  finiteLength : ElementEulerFiniteLength R (R ⧸ prime.asIdeal) r

/-- The Euler value of a prime factor.

The factor value is χ_r(R/p), computed using its finite multiplication lengths. -/
noncomputable def ElementEulerPrimeFactor.value
    {r : R} (f : ElementEulerPrimeFactor R r) : ℤ :=
  elementEulerCharacteristic R (R ⧸ f.prime.asIdeal) r f.finiteLength

omit [IsNoetherianRing R] in
open Classical in
/-- The prime factor contribution by membership of the element.

The contribution is zero if r ∈ p, and otherwise equals the length of (R/p)/r(R/p). -/
theorem ElementEulerPrimeFactor.value_eq_ite
    {r : R} (f : ElementEulerPrimeFactor R r) :
    f.value = if r ∈ f.prime.asIdeal then 0 else
      (Module.length R
        ((R ⧸ f.prime.asIdeal) ⧸
          (LinearMap.lsmul R (R ⧸ f.prime.asIdeal) r).range)).toNat := by
  by_cases hr : r ∈ f.prime.asIdeal
  · simp only [hr, ↓reduceIte]
    exact elementEulerCharacteristic_quotient_prime_eq_zero_of_mem
      R f.prime.asIdeal r hr f.finiteLength
  · simp only [hr, ↓reduceIte]
    exact elementEulerCharacteristic_quotient_prime_eq_length_of_not_mem
      R f.prime.asIdeal r hr f.finiteLength

/-- The localized length of a prime factor.

At q, take the length over R_q of the localization of R/p. -/
noncomputable def ElementEulerPrimeFactor.localLengthAt
    {r : R} (f : ElementEulerPrimeFactor R r) (q : PrimeSpectrum R) : ENat :=
  Module.length (Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl (R ⧸ f.prime.asIdeal))

omit [IsNoetherianRing R] in
/-- Prime Euler factors are determined by their primes.

Two bundled factors for the same r are equal exactly when their prime components are equal. -/
theorem ElementEulerPrimeFactor.eq_iff_prime_eq
    {r : R} {f g : ElementEulerPrimeFactor R r} :
    f = g ↔ f.prime = g.prime := by
  constructor
  · exact fun h => congrArg ElementEulerPrimeFactor.prime h
  · intro h
    cases f with
    | mk fp fh =>
      cases g with
      | mk gp gh =>
        dsimp only at h
        subst gp
        rfl

omit [IsNoetherianRing R] in
open Classical in
/-- Factor multiplicity equals its prime occurrence count.

Counting a bundled factor in a list equals counting list entries with its prime. -/
theorem ElementEulerPrimeFactor.count_eq_countP_prime
    {r : R} (l : List (ElementEulerPrimeFactor R r))
    (f : ElementEulerPrimeFactor R r) :
    l.count f = l.countP (fun g => decide (g.prime = f.prime)) := by
  induction l with
  | nil => simp
  | cons g l ih =>
      by_cases h : g.prime = f.prime
      · have hgf : g = f :=
          (ElementEulerPrimeFactor.eq_iff_prime_eq R).mpr h
        subst g
        simp [ih]
      · have hgf : g ≠ f := fun h' => h <|
          (ElementEulerPrimeFactor.eq_iff_prime_eq R).mp h'
        simp [h, hgf, ih]

omit [IsNoetherianRing R] in
/-- A prime factor has length one at its own prime.

The localization of R/p at p has length one over R_p. -/
theorem ElementEulerPrimeFactor.localLengthAt_eq_one
    {r : R} (f : ElementEulerPrimeFactor R r) :
    f.localLengthAt R f.prime = 1 := by
  let S := f.prime.asIdeal.primeCompl
  let Q := Localization.AtPrime f.prime.asIdeal
  have hmap : LocalizedModule.mkLinearMap S R = Algebra.linearMap R Q := by
    apply LinearMap.ext
    intro x
    rfl
  have hloc : Submodule.localized S f.prime.asIdeal =
      f.prime.asIdeal.map (algebraMap R Q) := by
    simpa only [Submodule.localized, hmap] using
      (Ideal.localized'_eq_map Q S f.prime.asIdeal)
  let e : LocalizedModule S (R ⧸ f.prime.asIdeal) ≃ₗ[Q]
      f.prime.asIdeal.ResidueField :=
    (localizedQuotientEquiv S f.prime.asIdeal).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by
        rw [hloc, Localization.AtPrime.map_eq_maximalIdeal])
  change Module.length Q
    (LocalizedModule S (R ⧸ f.prime.asIdeal)) = 1
  have hsimple : IsSimpleModule Q f.prime.asIdeal.ResidueField :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨IsLocalRing.maximalIdeal Q, inferInstance, ⟨LinearEquiv.refl Q _⟩⟩
  let : IsSimpleModule Q f.prime.asIdeal.ResidueField := hsimple
  exact e.length_eq.trans (Module.length_eq_one Q _)

omit [IsNoetherianRing R] in
/-- A factor vanishes at a prime not containing its prime.

If p is not contained in q, the localization of R/p at q has length zero. -/
theorem ElementEulerPrimeFactor.localLengthAt_eq_zero_of_not_le
    {r : R} (f : ElementEulerPrimeFactor R r) (q : PrimeSpectrum R)
    (h : ¬ f.prime.asIdeal ≤ q.asIdeal) :
    f.localLengthAt R q = 0 := by
  change Module.length (Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl (R ⧸ f.prime.asIdeal)) = 0
  rw [Module.length_eq_zero_iff]
  apply (LocalizedModule.subsingleton_iff
    (R := R) (M := R ⧸ f.prime.asIdeal)
      (S := q.asIdeal.primeCompl)).mpr
  obtain ⟨a, ha, haq⟩ := IsConcreteLE.not_le_iff_exists.mp h
  intro x
  refine ⟨a, haq, ?_⟩
  change a • x = 0
  rw [show (a : R) • x = Ideal.Quotient.mk f.prime.asIdeal a * x by rfl,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]

/-- A finite prime-factor length and Euler decomposition.

Record finite multiplication data for M, a list of prime factors in its support, and
equalities expressing every localized length and χ_r(M) as the corresponding factor sums. -/
structure ElementEulerPrimeDecomposition
    (M : Type v) [AddCommGroup M] [Module R M] (r : R) where
/-- Finite multiplication lengths of the decomposed module.

The module M has finite multiplication kernel and cokernel lengths for r. -/
  finiteLength : ElementEulerFiniteLength R M r
  /-- The prime-factor list with multiplicities.

The list retains repeated prime factors, so occurrence counts encode multiplicities. -/
  factors : List (ElementEulerPrimeFactor R r)
/-- The factor primes belong to the module support.

Every prime appearing in the factor list lies in Supp_R(M). -/
  factor_mem_support : ∀ f ∈ factors, f.prime ∈ Module.support R M
/-- The localized module length is the sum of factor lengths.

For every prime q, ℓ_{R_q}(M_q) equals the sum of the localized lengths of all entries in the
factor list. -/
  localized_length_eq : ∀ q : PrimeSpectrum R,
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) =
      (factors.map fun f => f.localLengthAt R q).sum
/-- The one-element Euler invariant is the factor-value sum.

The integer χ_r(M) equals the sum of the Euler values of the factor list, with repetitions
retained. -/
  eq_sum : elementEulerCharacteristic R M r finiteLength =
    (factors.map (ElementEulerPrimeFactor.value R)).sum

omit [IsNoetherianRing R] in
open Classical in
/-- Localized length under the minimal-support condition.

If every support prime contained in q equals q, then ℓ_{R_q}(M_q) equals the number of
factor-list occurrences of q. -/
theorem ElementEulerPrimeDecomposition.localized_length_eq_countP_of_minimal
    {M : Type v} [AddCommGroup M] [Module R M] {r : R}
    (d : ElementEulerPrimeDecomposition R M r) (q : PrimeSpectrum R)
    (hmin : ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
      p.asIdeal ≤ q.asIdeal → p = q) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) =
      (d.factors.countP fun f => decide (f.prime = q) : ℕ) := by
  rw [d.localized_length_eq q]
  have hfactor : ∀ f ∈ d.factors,
      f.localLengthAt R q =
        if f.prime = q then (1 : ENat) else 0 := by
    intro f hf
    by_cases heq : f.prime = q
    · subst q
      simp only [↓reduceIte]
      exact f.localLengthAt_eq_one R
    · simp only [heq, ↓reduceIte]
      apply f.localLengthAt_eq_zero_of_not_le R q
      intro hle
      exact heq (hmin f.prime (d.factor_mem_support f hf) hle)
  rw [List.map_congr_left hfactor]
  induction d.factors with
  | nil => simp
  | cons f fs ih =>
      by_cases h : f.prime = q <;>
        simp [h, ih, add_comm]

omit [IsNoetherianRing R] in
open Classical in
/-- Every minimal ring prime occurs in the regular-module decomposition.

For a decomposition of R and a minimal prime q, some factor-list entry has prime q. -/
theorem ElementEulerPrimeDecomposition.exists_factor_prime_eq_of_isMin
    {r : R} (d : ElementEulerPrimeDecomposition R R r)
    (q : PrimeSpectrum R) (hmin : IsMin q) :
    ∃ f ∈ d.factors, f.prime = q := by
  have hqSupport : q ∈ Module.support R R := by
    rw [Module.mem_support_iff_of_finite]
    have hAnn : Module.annihilator R R = ⊥ :=
      Module.annihilator_eq_bot.mpr
        ((faithfulSMul_iff_algebraMap_injective R R).mpr
          fun {_ _} h => h)
    rw [hAnn]
    exact bot_le
  have hlocal := d.localized_length_eq_countP_of_minimal R q
    (fun p _ hpq => le_antisymm hpq (hmin hpq))
  have hlength : Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl R) ≠ 0 := by
    intro hzero
    have hsub : Subsingleton (LocalizedModule q.asIdeal.primeCompl R) :=
      Module.length_eq_zero_iff.mp hzero
    let _ : Nontrivial (LocalizedModule q.asIdeal.primeCompl R) := hqSupport
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub
  have hcount : d.factors.countP
      (fun f => decide (f.prime = q)) ≠ 0 := by
    intro hzero
    apply hlength
    rw [hlocal, hzero]
    rfl
  obtain ⟨f, hf, hfp⟩ :=
    List.countP_pos_iff.mp (Nat.pos_of_ne_zero hcount)
  exact ⟨f, hf, of_decide_eq_true hfp⟩

omit [IsNoetherianRing R] in
open Classical in
/-- Euler factors weighted by their generic multiplicities.

If every factor excluding r satisfies the stated minimal-support condition, χ_r(M) is the sum
over distinct factors of ℓ_{R_p}(M_p) times the factor Euler value. -/
theorem ElementEulerPrimeDecomposition.eq_sum_localizedLength_mul
    {M : Type v} [AddCommGroup M] [Module R M] {r : R}
    (d : ElementEulerPrimeDecomposition R M r)
    (hmin : ∀ f ∈ d.factors, r ∉ f.prime.asIdeal →
      ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
        p.asIdeal ≤ f.prime.asIdeal → p = f.prime) :
    elementEulerCharacteristic R M r d.finiteLength =
      ∑ f ∈ d.factors.toFinset,
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) *
            f.value := by
  calc
    elementEulerCharacteristic R M r d.finiteLength =
        (d.factors.map (ElementEulerPrimeFactor.value R)).sum := d.eq_sum
    _ = ∑ f ∈ d.factors.toFinset, d.factors.count f • f.value :=
      Finset.sum_list_map_count d.factors (ElementEulerPrimeFactor.value R)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      have hfList : f ∈ d.factors := by simpa using hf
      by_cases hr : r ∈ f.prime.asIdeal
      · rw [f.value_eq_ite R]
        simp only [hr, ↓reduceIte, Nat.cast_zero, smul_zero, mul_zero]
      · have hlocal := d.localized_length_eq_countP_of_minimal R
          f.prime (hmin f hfList hr)
        have hcount := f.count_eq_countP_prime R d.factors
        have hNat := congrArg ENat.toNat hlocal
        rw [ENat.toNat_natCast, ← hcount] at hNat
        rw [hNat]
        simp only [nsmul_eq_mul]

omit [IsNoetherianRing R] in
open Classical in
/-- An Euler factor excluding a local parameter is minimal in support.

For finite M over the stated local noetherian ring, r in the maximal ideal and support
dimension at most one, a factor prime excluding r has no smaller support prime. -/
theorem ElementEulerPrimeDecomposition.factor_minimal_support_of_not_mem_of_supportDim_le_one
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {r : R}
    (d : ElementEulerPrimeDecomposition R M r)
    (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R M ≤ 1)
    (f : ElementEulerPrimeFactor R r) (hf : f ∈ d.factors)
    (hrf : r ∉ f.prime.asIdeal) :
    ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
      p.asIdeal ≤ f.prime.asIdeal → p = f.prime := by
  intro p hp hpf
  let fp : Module.support R M :=
    ⟨f.prime, d.factor_mem_support f hf⟩
  have hdim' : Order.krullDim (Module.support R M) ≤ 1 := hdim
  rcases Order.krullDim_le_one_iff.mp hdim' fp with hmin | hmax
  · exact congrArg Subtype.val <|
      hmin.eq_of_le (show (⟨p, hp⟩ : Module.support R M) ≤ fp from hpf)
  · let closed : PrimeSpectrum R :=
      ⟨IsLocalRing.maximalIdeal R, by infer_instance⟩
    have hfAnn : Module.annihilator R M ≤ f.prime.asIdeal :=
      Module.mem_support_iff_of_finite.mp (d.factor_mem_support f hf)
    have hfClosed : f.prime.asIdeal ≤ closed.asIdeal :=
      IsLocalRing.le_maximalIdeal f.prime.isPrime.ne_top
    have hclosedSupport : closed ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr (hfAnn.trans hfClosed)
    have heq : fp = ⟨closed, hclosedSupport⟩ :=
      hmax.eq_of_le hfClosed
    have hprime : f.prime.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg (fun x : Module.support R M => x.1.asIdeal) heq
    exact False.elim (hrf (hprime.symm ▸ hr))

omit [IsNoetherianRing R] in
open Classical in
/-- A regular-module factor excluding the parameter is a minimal ring prime.

For the regular module in the stated local support-dimension setting, each factor prime
excluding r is minimal. -/
theorem ElementEulerPrimeDecomposition.factor_prime_isMin_of_not_mem_of_supportDim_le_one
    [IsLocalRing R] {r : R}
    (d : ElementEulerPrimeDecomposition R R r)
    (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R R ≤ 1)
    (f : ElementEulerPrimeFactor R r) (hf : f ∈ d.factors)
    (hrf : r ∉ f.prime.asIdeal) : IsMin f.prime := by
  intro p hpf
  have hpSupport : p ∈ Module.support R R := by
    rw [Module.mem_support_iff_of_finite]
    have hAnn : Module.annihilator R R = ⊥ :=
      Module.annihilator_eq_bot.mpr
        ((faithfulSMul_iff_algebraMap_injective R R).mpr
          fun {_ _} h => h)
    rw [hAnn]
    exact bot_le
  have heq := d.factor_minimal_support_of_not_mem_of_supportDim_le_one
    R hr hdim f hf hrf p hpSupport hpf
  subst p
  exact le_rfl

omit [IsNoetherianRing R] in
open Classical in
/-- The generic-multiplicity Euler sum in support dimension at most one.

For finite M, the local and support-dimension hypotheses give χ_r(M) as the distinct-factor
sum of localized multiplicity times factor value. -/
theorem ElementEulerPrimeDecomposition.eq_sum_localizedLength_mul_of_supportDim_le_one
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {r : R}
    (d : ElementEulerPrimeDecomposition R M r)
    (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R M ≤ 1) :
    elementEulerCharacteristic R M r d.finiteLength =
      ∑ f ∈ d.factors.toFinset,
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) *
            f.value := by
  apply d.eq_sum_localizedLength_mul R
  exact d.factor_minimal_support_of_not_mem_of_supportDim_le_one
    R hr hdim

omit [IsNoetherianRing R] in
open Classical in
/-- The generic-multiplicity sum with explicit principal quotient contributions.

Under the same hypotheses, each weighted factor contributes zero when it contains r and
otherwise the length of its principal quotient by r. -/
theorem ElementEulerPrimeDecomposition.eq_sum_localizedLength_mul_ite_of_supportDim_le_one
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {r : R}
    (d : ElementEulerPrimeDecomposition R M r)
    (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R M ≤ 1) :
    elementEulerCharacteristic R M r d.finiteLength =
      ∑ f ∈ d.factors.toFinset,
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) *
            ((if r ∈ f.prime.asIdeal then 0 else
              (Module.length R
                ((R ⧸ f.prime.asIdeal) ⧸
                  (LinearMap.lsmul R (R ⧸ f.prime.asIdeal) r).range)).toNat :
                ℕ) : ℤ) := by
  rw [d.eq_sum_localizedLength_mul_of_supportDim_le_one R hr hdim]
  apply Finset.sum_congr rfl
  intro f _
  rw [f.value_eq_ite R]

/-- Existence of a finite prime Euler decomposition.

For finite M over a noetherian ring, finite length of M/rM suffices to construct the finite
multiplication data, prime-factor list and its localized-length and Euler identities. -/
theorem exists_elementEulerPrimeDecomposition
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r : R)
    (hcoker : Module.length R
      (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    Nonempty (ElementEulerPrimeDecomposition R M r) := by
  induction (inferInstance : Module.Finite R M) using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      have hN : Module.length R N ≠ ⊤ := by
        rw [Module.length_eq_zero]
        exact ENat.zero_ne_top
      let h := ElementEulerFiniteLength.of_module_length R N r hN
      refine ⟨{
        finiteLength := h
        factors := []
        factor_mem_support := by simp
        localized_length_eq := ?_
        eq_sum := ?_ }⟩
      · intro q
        simp only [List.map_nil, List.sum_nil]
        rw [Module.length_eq_zero_iff]
        infer_instance
      simp [elementEulerCharacteristic]
  | quotient N p e =>
      have hpQuotient : IsAssociatedPrime p.asIdeal (R ⧸ p.asIdeal) := by
        rw [isAssociatedPrime_iff_exists_injective_linearMap]
        exact ⟨inferInstance, LinearMap.id, Function.injective_id⟩
      have hpN : IsAssociatedPrime p.asIdeal N :=
        (e.isAssociatedPrime_iff).mpr hpQuotient
      let hpData :=
        ElementEulerFiniteLength.quotient_prime_of_isAssociatedPrime
          R N r p hpN hcoker
      let hN := hpData.equiv R (R ⧸ p.asIdeal) r e.symm
      let factor : ElementEulerPrimeFactor R r :=
        { prime := p, finiteLength := hpData }
      have hpSupport : p ∈ Module.support R N :=
        Module.mem_support_iff_of_finite.mpr (by
          simpa only [Submodule.annihilator_top] using hpN.annihilator_le)
      refine ⟨{
        finiteLength := hN
        factors := [factor]
        factor_mem_support := ?_
        localized_length_eq := ?_
        eq_sum := ?_ }⟩
      · intro f hf
        simp only [List.mem_singleton] at hf
        subst f
        exact hpSupport
      · intro q
        let S := q.asIdeal.primeCompl
        let Q := Localization.AtPrime q.asIdeal
        let eLoc : LocalizedModule S N ≃ₗ[Q]
            LocalizedModule S (R ⧸ p.asIdeal) :=
          LinearEquiv.ofBijective
            (LocalizedModule.map S e.toLinearMap)
            ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
              LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        exact eLoc.length_eq
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      simpa only [factor, ElementEulerPrimeFactor.value] using
        elementEulerCharacteristic_equiv R N r e hN
  | exact N₁ N₂ N₃ i p hi hp hip ih₁ ih₃ =>
      have hcoker₃ := elementCokernel_length_ne_top_of_surjective
        R r p hp hcoker
      obtain ⟨d₃⟩ := ih₃ hcoker₃
      have hcoker₁ := elementLeftCokernel_length_ne_top_of_shortExact
        R r i p hi hp hip hcoker d₃.finiteLength.kernel_ne_top
      obtain ⟨d₁⟩ := ih₁ hcoker₁
      let h₂ := ElementEulerFiniteLength.of_shortExact
        R r i p hi hp hip d₁.finiteLength d₃.finiteLength
      refine ⟨{
        finiteLength := h₂
        factors := d₁.factors ++ d₃.factors
        factor_mem_support := by
          intro factor hfactor
          rw [List.mem_append] at hfactor
          rcases hfactor with hfactor | hfactor
          · exact Module.support_subset_of_injective i hi
              (d₁.factor_mem_support factor hfactor)
          · exact Module.support_subset_of_surjective p hp
              (d₃.factor_mem_support factor hfactor)
        localized_length_eq := by
          intro q
          let S := q.asIdeal.primeCompl
          let Q := Localization.AtPrime q.asIdeal
          let iLoc : LocalizedModule S N₁ →ₗ[Q] LocalizedModule S N₂ :=
            LocalizedModule.map S i
          let pLoc : LocalizedModule S N₂ →ₗ[Q] LocalizedModule S N₃ :=
            LocalizedModule.map S p
          have hLocExact : Function.Exact iLoc pLoc :=
            LocalizedModule.map_exact S i p hip
          have hiLoc : Function.Injective iLoc :=
            LocalizedModule.map_injective S i hi
          have hpLoc : Function.Surjective pLoc :=
            LocalizedModule.map_surjective S p hp
          calc
            Module.length Q (LocalizedModule S N₂) =
                Module.length Q (LocalizedModule S N₁) +
                  Module.length Q (LocalizedModule S N₃) :=
              Module.length_eq_add_of_exact iLoc pLoc hiLoc hpLoc hLocExact
            _ = (d₁.factors.map fun f => f.localLengthAt R q).sum +
                  (d₃.factors.map fun f => f.localLengthAt R q).sum := by
              rw [d₁.localized_length_eq q, d₃.localized_length_eq q]
            _ = ((d₁.factors ++ d₃.factors).map
                  fun f => f.localLengthAt R q).sum := by
              simp
        eq_sum := ?_ }⟩
      calc
        elementEulerCharacteristic R N₂ r h₂ =
            elementEulerCharacteristic R N₁ r d₁.finiteLength +
              elementEulerCharacteristic R N₃ r d₃.finiteLength :=
          elementEulerCharacteristic_additive R r i p hi hp hip
            d₁.finiteLength h₂ d₃.finiteLength
        _ = (d₁.factors.map (ElementEulerPrimeFactor.value R)).sum +
              (d₃.factors.map (ElementEulerPrimeFactor.value R)).sum := by
          rw [d₁.eq_sum, d₃.eq_sum]
        _ = ((d₁.factors ++ d₃.factors).map
              (ElementEulerPrimeFactor.value R)).sum := by
          simp

end Module
