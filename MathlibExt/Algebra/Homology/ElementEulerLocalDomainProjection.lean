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

public import MathlibExt.Algebra.Homology.ElementEulerPrimeFiltration
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# A one-element Euler formula over a local domain

Let R be a noetherian local domain of Krull dimension at most one, M finitely generated, and r
a nonzero element of the maximal ideal. With finite multiplication kernel and cokernel
lengths, χ_r(M) equals the generic localized length of M times ℓ_R(R/rR). The generic length
is also Module.finrank R M.

If multiplication by r is injective on M, this becomes the corresponding formula for
ℓ_R(M/rM). The ring and module universes remain independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v

namespace Module

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem prime_eq_bot_of_parameter_not_mem
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : ringKrullDim R ≤ 1) (p : PrimeSpectrum R)
    (hp : r ∉ p.asIdeal) : p = ⊥ := by
  by_contra hne
  have hmax : IsMax p :=
    Order.krullDim_le_one_iff_forall_isMax.mp hdim p hne
  let closed : PrimeSpectrum R :=
    ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  have hle : p ≤ closed := IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  have heq : p = closed := hmax.eq_of_le hle
  exact hp ((congrArg PrimeSpectrum.asIdeal heq).symm ▸ hr)

omit [IsNoetherianRing R] in
open Classical in
private theorem primeFactor_value_eq_bot_parameter_length
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) (hr0 : r ≠ 0)
    (hdim : ringKrullDim R ≤ 1) (f : ElementEulerPrimeFactor R r) :
    f.value = if f.prime = ⊥ then
      ((Module.length R (R ⧸ (LinearMap.lsmul R R r).range)).toNat : ℤ)
      else 0 := by
  classical
  by_cases hp : f.prime = ⊥
  · simp only [hp, ↓reduceIte]
    have hbot : (f.prime.asIdeal : Submodule R R) = ⊥ := by
      rw [hp, PrimeSpectrum.asIdeal_bot]
    let e : (R ⧸ f.prime.asIdeal) ≃ₗ[R] R :=
      Submodule.quotEquivOfEqBot f.prime.asIdeal hbot
    have hinj : Function.Injective (LinearMap.lsmul R R r) := by
      intro x y hxy
      exact mul_left_cancel₀ hr0 hxy
    exact (elementEulerCharacteristic_equiv R (R ⧸ f.prime.asIdeal)
      r e f.finiteLength).trans
        (elementEulerCharacteristic_eq_quotient_of_injective R R r hinj
          (f.finiteLength.equiv R (R ⧸ f.prime.asIdeal) r e))
  · have hrp : r ∈ f.prime.asIdeal := by
      by_contra hnot
      exact hp (prime_eq_bot_of_parameter_not_mem R r hr hdim f.prime hnot)
    rw [f.value_eq_ite R]
    simp only [hp, hrp, ↓reduceIte, Nat.cast_zero]

omit [IsLocalRing R] [IsNoetherianRing R] in
private theorem genericLength_toNat_eq_finrank
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (Module.length (Localization.AtPrime (⊥ : PrimeSpectrum R).asIdeal)
      (LocalizedModule (⊥ : PrimeSpectrum R).asIdeal.primeCompl M)).toNat =
        Module.finrank R M := by
  let S : Submonoid R := (⊥ : PrimeSpectrum R).asIdeal.primeCompl
  let K := Localization.AtPrime (⊥ : PrimeSpectrum R).asIdeal
  have hs : S = nonZeroDivisors R := Ideal.primeCompl_bot
  let : IsFractionRing R K := by
    change IsLocalization (nonZeroDivisors R) K
    rw [← hs]
    infer_instance
  let : Field K := IsFractionRing.toField R
  change (Module.length K (LocalizedModule S M)).toNat = Module.finrank R M
  rw [Module.length_eq_finrank, ENat.toNat_natCast]
  exact (IsLocalization.finrank_eq K S hs.le).trans
    (IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hs.le)

/-- The local-domain Euler formula with generic multiplicity.

Under the stated local-domain, dimension, parameter and finiteness hypotheses,
χ_r(M)=ℓ_{R_(0)}(M_(0))·ℓ_R(R/rR). -/
theorem elementEulerCharacteristic_eq_genericLength_mul_of_localDomain
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) (hr0 : r ≠ 0)
    (hdim : ringKrullDim R ≤ 1) (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h =
      ((Module.length (Localization.AtPrime (⊥ : PrimeSpectrum R).asIdeal)
        (LocalizedModule (⊥ : PrimeSpectrum R).asIdeal.primeCompl M)).toNat : ℤ) *
          ((Module.length R (R ⧸ (LinearMap.lsmul R R r).range)).toNat : ℤ) := by
  classical
  obtain ⟨d⟩ := exists_elementEulerPrimeDecomposition R M r h.cokernel_ne_top
  have hlocal := d.localized_length_eq_countP_of_minimal R (⊥ : PrimeSpectrum R)
    (fun p _ hp => le_antisymm hp bot_le)
  have hsum : (d.factors.map (ElementEulerPrimeFactor.value R)).sum =
      (d.factors.countP (fun f => decide (f.prime = ⊥)) : ℤ) *
        ((Module.length R (R ⧸ (LinearMap.lsmul R R r).range)).toNat : ℤ) := by
    induction d.factors with
    | nil => simp
    | cons f fs ih =>
        rw [List.map_cons, List.sum_cons,
          primeFactor_value_eq_bot_parameter_length R r hr hr0 hdim f]
        by_cases hp : f.prime = ⊥
        · simp [hp, ih, add_mul, add_comm]
        · simp [hp, ih]
  calc
    elementEulerCharacteristic R M r h =
        (d.factors.map (ElementEulerPrimeFactor.value R)).sum := d.eq_sum
    _ = _ := by
      rw [hlocal, ENat.toNat_natCast]
      exact hsum

/-- The local-domain Euler formula with module rank.

Under the same hypotheses, χ_r(M)=Module.finrank R M times ℓ_R(R/rR), interpreted as integers. -/
theorem elementEulerCharacteristic_eq_finrank_mul_of_localDomain
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) (hr0 : r ≠ 0)
    (hdim : ringKrullDim R ≤ 1) (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h =
      (Module.finrank R M : ℤ) *
        ((Module.length R (R ⧸ (LinearMap.lsmul R R r).range)).toNat : ℤ) := by
  rw [elementEulerCharacteristic_eq_genericLength_mul_of_localDomain R M r hr hr0 hdim h,
    genericLength_toNat_eq_finrank R M]

/-- The local-domain quotient length formula for injective multiplication.

If μ_r is injective and M/rM has finite length, its length equals the generic localized length
of M times ℓ_R(R/rR), under the stated local-domain parameter hypotheses. -/
theorem length_lsmul_cokernel_toNat_eq_genericLength_mul_of_localDomain
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) (hr0 : r ≠ 0)
    (hdim : ringKrullDim R ≤ 1)
    (hinj : Function.Injective (LinearMap.lsmul R M r))
    (hquot : Module.length R (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    (Module.length R (M ⧸ (LinearMap.lsmul R M r).range)).toNat =
      (Module.length (Localization.AtPrime (⊥ : PrimeSpectrum R).asIdeal)
        (LocalizedModule (⊥ : PrimeSpectrum R).asIdeal.primeCompl M)).toNat *
          (Module.length R (R ⧸ (LinearMap.lsmul R R r).range)).toNat := by
  let h := ElementEulerFiniteLength.of_injective R M r hinj hquot
  have he := elementEulerCharacteristic_eq_genericLength_mul_of_localDomain
    R M r hr hr0 hdim h
  rw [elementEulerCharacteristic_eq_quotient_of_injective R M r hinj h] at he
  exact Int.natCast_inj.mp (by simpa only [Nat.cast_mul] using he)

end Module
