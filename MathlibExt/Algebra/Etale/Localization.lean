/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean` and
`P2M/Sol/S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Localizations of étale algebras

The localization of an étale algebra at a prime is a domain and integrally
closed, proved by embedding it into a field via the generic fibre.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace EtaleLocNormalAux

private theorem isIntegral_of_isIdempotentElem {T B : Type*} [CommRing T] [CommRing B]
    [Algebra T B] {e : B} (he : IsIdempotentElem e) : IsIntegral T e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_one, mul_sub, mul_one, he.eq, sub_self]

private theorem tensorMap_integralClosure_mem_bot (R K : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [Algebra R S] (y : S ⊗[R] (integralClosure R K)) :
    (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val) y
      ∈ (⊥ : Subalgebra S (S ⊗[R] K)) := by
  refine TensorProduct.inductionOn y ?_ ?_
  · intro s k
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((mem_integralClosure_iff R K).mp k.2)
    rw [Algebra.TensorProduct.map_tmul, Algebra.mem_bot]
    refine ⟨r • s, ?_⟩
    calc algebraMap S (S ⊗[R] K) (r • s)
        = (r • s) ⊗ₜ[R] (1 : K) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
            RingHom.id_apply]
      _ = s ⊗ₜ[R] (r • (1 : K)) := TensorProduct.smul_tmul r s 1
      _ = s ⊗ₜ[R] (algebraMap R K r) := by rw [Algebra.algebraMap_eq_smul_one]
      _ = (AlgHom.id S S) s ⊗ₜ[R] ((integralClosure R K).val k) := by rw [hr]; simp
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

private theorem smooth_integrallyClosed_in_genericFibre (R K : Type u) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    integralClosure S (S ⊗[R] K) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, hy⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2 ⟨x, hx⟩
  have hy' : (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val) y = x := by
    have h := congrArg Subtype.val hy
    simpa only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict] using h
  rw [← hy']
  exact tensorMap_integralClosure_mem_bot R K S y

private theorem exists_algebraMap_eq_of_isIntegral_genericFibre (R K : Type u) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    {x : S ⊗[R] K} (hx : IsIntegral S x) : ∃ s : S, algebraMap S (S ⊗[R] K) s = x := by
  have hmem : x ∈ integralClosure S (S ⊗[R] K) :=
    (mem_integralClosure_iff S (S ⊗[R] K)).mpr hx
  rw [smooth_integrallyClosed_in_genericFibre R K S, Algebra.mem_bot] at hmem
  exact hmem

private theorem algebraMap_genericFibre_injective (R K : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S] :
    Function.Injective (algebraMap S (S ⊗[R] K)) := by
  have h := Algebra.TensorProduct.includeLeft_injective (S := S) (A := S) (B := K)
    (IsFractionRing.injective R K)
  intro a b hab
  apply h
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.algebraMap_apply]
    using hab

private theorem isIntegrallyClosed_of_integralClosure_eq_bot (T A : Type*) [CommRing T]
    [IsDomain T] [CommRing A] [IsDomain A] [Algebra T A] [FaithfulSMul T A]
    [IsIntegrallyClosed A] (h : integralClosure T A = ⊥) :
    IsIntegrallyClosed T := by
  have hg : Function.Injective (algebraMap T (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq T A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp
      (FaithfulSMul.algebraMap_injective T A)
  have hg' : Function.Injective (Algebra.ofId T (FractionRing A)) := fun a b hab =>
    hg (by simpa [Algebra.ofId_apply] using hab)
  let φ : FractionRing T →ₐ[T] FractionRing A :=
    IsFractionRing.liftAlgHom (K := FractionRing T) hg'
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  have h1 : IsIntegral T (φ x) := hx.map φ
  have h2 : IsIntegral A (φ x) := h1.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : IsIntegral T a := by
    refine IsIntegral.tower_bot (IsFractionRing.injective A (FractionRing A)) ?_
    rw [ha]
    exact h1
  have h4 : a ∈ (⊥ : Subalgebra T A) := by
    rw [← h]
    exact (mem_integralClosure_iff T A).mpr h3
  rw [Algebra.mem_bot] at h4
  obtain ⟨t, ht⟩ := h4
  refine ⟨t, ?_⟩
  have hφinj : Function.Injective φ := RingHom.injective (φ : FractionRing T →+* FractionRing A)
  apply hφinj
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply T A (FractionRing A), ht]
  exact ha

end EtaleLocNormalAux

open EtaleLocNormalAux in
/-- The localization of an étale algebra at a prime is a domain and
integrally closed. -/
theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q]
    [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by
  classical
  have hq : q.IsPrime := inferInstance
  let L := FractionRing P
  let B₀ := A ⊗[P] L
  obtain ⟨I, hI, F, hF, hFalg, e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod L (L ⊗[P] A)).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  let e₀ : B₀ ≃+* (Π j, F j) := (Algebra.TensorProduct.comm P A L).toRingEquiv.trans e.toRingEquiv
  let θ : A →+* (Π j, F j) := e₀.toRingHom.comp (algebraMap A B₀)
  have hθ : ∀ a, θ a = e₀ (algebraMap A B₀ a) := fun a => rfl
  have hinj : Function.Injective (algebraMap A B₀) := algebraMap_genericFibre_injective P L A
  have hθinj : Function.Injective θ := e₀.injective.comp hinj
  have hIC : ∀ y : B₀, IsIntegral A y → ∃ a, algebraMap A B₀ a = y :=
    fun y hy => exists_algebraMap_eq_of_isIntegral_genericFibre P L A hy
  have hε : ∀ j : I, ∃ ε : A, θ ε = Pi.single j 1 := by
    intro j
    have hid : IsIdempotentElem (e₀.symm (Pi.single j 1) : B₀) := by
      have hthis : IsIdempotentElem (Pi.single j (1 : F j) : Π j, F j) := by
        simp [IsIdempotentElem, ← Pi.single_mul]
      simpa [IsIdempotentElem, map_mul] using congrArg e₀.symm hthis.eq
    obtain ⟨a, ha⟩ := hIC _ (isIntegral_of_isIdempotentElem hid)
    exact ⟨a, by rw [hθ, ha, RingEquiv.apply_symm_apply]⟩
  choose ε hε using hε
  have hsum : ∑ j, ε j = 1 := by
    apply hθinj
    rw [map_sum, map_one]
    simp only [hε]
    exact Finset.univ_sum_single (1 : Π j, F j) ▸ by simp
  obtain ⟨i, hi⟩ : ∃ i, ε i ∉ q := by
    by_contra h
    push Not at h
    have hthis : (1 : A) ∈ q := hsum ▸ q.sum_mem fun j _ => h j
    exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr hthis)
  let ρ : A →+* F i := (Pi.evalRingHom F i).comp θ
  have hρ : ∀ a, ρ a = θ a i := fun a => rfl
  have hρε : ∀ a, θ (a * ε i) = Pi.single i (ρ a) := by
    intro a
    rw [map_mul, hε]
    ext j
    by_cases hj : j = i
    · subst hj; simp [hρ]
    · simp [hj]
  have hker : ∀ a, ρ a = 0 → a * ε i = 0 := by
    intro a ha
    apply hθinj
    rw [hρε, ha, Pi.single_zero, map_zero]
  have hunit : ∀ s : q.primeCompl, IsUnit (ρ s) := by
    intro s
    rw [isUnit_iff_ne_zero]
    intro h0
    have hthis := hker s h0
    rcases hq.mem_or_mem (hthis ▸ q.zero_mem : (s : A) * ε i ∈ q) with h | h
    · exact s.2 h
    · exact hi h
  let ρ' : A_q →+* F i := IsLocalization.lift (M := q.primeCompl) hunit
  have hρ' : ∀ a, ρ' (algebraMap A A_q a) = ρ a := fun a => IsLocalization.lift_eq hunit a
  have hρ'inj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    rw [IsLocalization.lift_mk'] at hx
    have ha : ρ a = 0 := by simpa using hx
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨ε i, hi⟩, by simpa [mul_comm] using hker a ha⟩
  have hdom : IsDomain A_q := Function.Injective.isDomain ρ' hρ'inj
  refine ⟨hdom, ?_⟩
  let : Algebra A_q (F i) := ρ'.toAlgebra
  let : Algebra A (F i) := ρ.toAlgebra
  have : IsScalarTower A A_q (F i) := IsScalarTower.of_algebraMap_eq fun a => (hρ' a).symm
  have : FaithfulSMul A_q (F i) := (faithfulSMul_iff_algebraMap_injective A_q (F i)).mpr hρ'inj
  refine isIntegrallyClosed_of_integralClosure_eq_bot A_q (F i) ?_
  refine le_antisymm ?_ bot_le
  intro z hz
  rw [mem_integralClosure_iff] at hz
  obtain ⟨⟨m, hm⟩, hmz⟩ := IsIntegral.exists_multiple_integral_of_isLocalization q.primeCompl z hz
  set w : F i := (⟨m, hm⟩ : q.primeCompl) • z with hw
  obtain ⟨p, hpm, hpw⟩ := hmz
  let y : B₀ := e₀.symm (Pi.single i w)
  have hy : IsIntegral A y := by
    refine ⟨Polynomial.X * p, Polynomial.monic_X.mul hpm, ?_⟩
    apply e₀.injective
    rw [map_zero]
    change e₀.toRingHom (Polynomial.eval₂ (algebraMap A B₀) y (Polynomial.X * p)) = 0
    rw [Polynomial.hom_eval₂]
    have hy' : e₀.toRingHom y = Pi.single i w := e₀.apply_symm_apply _
    rw [hy']
    funext j
    change (Pi.evalRingHom F j) (Polynomial.eval₂
      (e₀.toRingHom.comp (algebraMap A B₀)) (Pi.single i w) (Polynomial.X * p)) = 0
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    by_cases hj : j = i
    · rw [hj]
      have hthis : ((Pi.evalRingHom F i).comp (e₀.toRingHom.comp (algebraMap A B₀))) =
          algebraMap A (F i) := rfl
      rw [hthis, Pi.evalRingHom_apply, Pi.single_eq_same, hpw, mul_zero]
    · rw [Pi.evalRingHom_apply, Pi.single_eq_of_ne hj, zero_mul]
  obtain ⟨a₀, ha₀⟩ := hIC y hy
  have hρa₀ : ρ a₀ = w := by
    rw [hρ, hθ, ha₀]
    simp [y]
  rw [Algebra.mem_bot]
  refine ⟨IsLocalization.mk' A_q a₀ (⟨m, hm⟩ : q.primeCompl), ?_⟩
  change ρ' _ = z
  have hmu : w = ρ m * z := by rw [hw, Submonoid.smul_def, Algebra.smul_def]; rfl
  rw [IsLocalization.lift_mk'_spec]
  change ρ a₀ = ρ m * z
  rw [hρa₀, hmu]
