/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.PID
public import MathlibExt.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local-global invertibility of fractional ideals

This is ATLAS `NumberTheoryI` Section 3.1 (Lemma 3.4, Theorem 3.2, Corollary 3.5): for a
fractional ideal `I` of a Noetherian domain `A`, invertibility of `I` is a local property,
testable one maximal (equivalently, one prime) ideal at a time, and locally it reduces to being
principal.

## Main results

* `fractionalIdeal_isUnit_iff_isPrincipal`: in a Noetherian **local** domain, a nonzero fractional
  ideal is invertible iff it is principal (Lemma 3.4).
* `FractionalIdeal.isUnit_iff_isUnit_localizeAtPrime`: in a Noetherian domain, a fractional ideal
  is invertible iff its localization at every maximal ideal is invertible (Theorem 3.2, first
  half).
* `FractionalIdeal.isUnit_iff_isUnit_localizeAtPrime_all_primes`: the same, with "maximal" relaxed
  to "prime" (Theorem 3.2, second half).
* `FractionalIdeal.isUnit_iff_isLocallyPrincipal`: a nonzero fractional ideal is invertible iff it
  is locally principal, i.e. its localization at every maximal ideal is principal (Corollary 3.5).
* `FractionalIdeal.localizeAtPrime_inv`: localization commutes with inversion,
  by the existing localization/division theorem in
  `MathlibExt.RingTheory.FractionalIdeal.Extended`.

None of this is in Mathlib: `Mathlib.RingTheory.DedekindDomain.PID` only treats the *global*
statement that an invertible ideal of a ring with finitely many maximal ideals is principal, with
no local-global equivalence for invertibility itself.
-/

open scoped nonZeroDivisors

@[expose] public section

/-- **Lemma 3.4.** A nonzero fractional ideal of a Noetherian local domain is invertible iff it is
principal. The forward direction specializes
`FractionalIdeal.isPrincipal.of_finite_maximals_of_inv` to the singleton set of maximal ideals of a
local ring; the converse is the general fact that a principal fractional ideal is invertible. -/
theorem fractionalIdeal_isUnit_iff_isPrincipal
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    IsUnit I ↔ (I : Submodule A K).IsPrincipal := by
  constructor
  · intro hunit
    have hfin : {J : Ideal A | J.IsMaximal}.Finite := by
      apply Set.Finite.subset (Set.finite_singleton (IsLocalRing.maximalIdeal A))
      intro J hJ
      exact Set.mem_singleton_iff.mpr (IsLocalRing.eq_maximalIdeal hJ)
    obtain ⟨u, hu⟩ := hunit
    have hinv : I * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
    exact FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hfin I ↑u⁻¹ hinv
  · intro hprinc
    have : (I : Submodule A K).IsPrincipal := hprinc
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      (FractionalIdeal.invertible_of_principal K I hI)

namespace FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The localization of a fractional ideal of `A` at a prime `𝔪`, viewed inside the (shared)
fraction field of `A`. -/
noncomputable def localizeAtPrime
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A) :=
  extendedHom (FractionRing A) (Localization.AtPrime 𝔪) I

theorem localizeAtPrime_ne_zero
    (𝔪 : Ideal A) [𝔪.IsPrime]
    {I : FractionalIdeal A⁰ (FractionRing A)} (hI : I ≠ 0) :
    I.localizeAtPrime 𝔪 ≠ 0 :=
  (extendedHom_eq_zero_iff (FractionRing A) (Localization.AtPrime 𝔪)).not.mpr hI

/-- A fractional ideal is locally principal if its localization at every maximal ideal is
principal. -/
def IsLocallyPrincipal (I : FractionalIdeal A⁰ (FractionRing A)) : Prop :=
  ∀ (𝔪 : Ideal A) [𝔪.IsMaximal],
    ((I.localizeAtPrime 𝔪 :
      Submodule (Localization.AtPrime 𝔪) (FractionRing A)).IsPrincipal)

theorem isUnit_localizeAtPrime_of_isUnit
    (I : FractionalIdeal A⁰ (FractionRing A))
    (hI : IsUnit I) (𝔪 : Ideal A) [𝔪.IsPrime] :
    IsUnit (I.localizeAtPrime 𝔪) :=
  hI.map (extendedHom (FractionRing A) (Localization.AtPrime 𝔪))

/-- Localization commutes with inversion of fractional ideals. -/
@[simp] theorem localizeAtPrime_inv
    [IsNoetherianRing A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    localizeAtPrime 𝔪 (I⁻¹) = (localizeAtPrime 𝔪 I)⁻¹ := by
  by_cases hI0 : I = 0
  · subst hI0; simp [localizeAtPrime, inv_zero']
  simpa only [localizeAtPrime, inv_eq, map_one] using
    extendedHom_div (B := Localization.AtPrime 𝔪) 𝔪.primeCompl 1 I hI0

/-- The inverse/localization inequality follows from equality. -/
theorem inv_localizeAtPrime_le
    [IsNoetherianRing A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    (localizeAtPrime 𝔪 I)⁻¹ ≤ localizeAtPrime 𝔪 (I⁻¹) :=
  (localizeAtPrime_inv 𝔪 I).symm.le

/-- **Theorem 3.2** (maximal-ideal form). A fractional ideal of a Noetherian domain is invertible
iff its localization at every maximal ideal is invertible. -/
theorem isUnit_iff_isUnit_localizeAtPrime
    [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    IsUnit I ↔ ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], IsUnit (I.localizeAtPrime 𝔪) := by
  constructor
  · exact fun hI 𝔪 _ => isUnit_localizeAtPrime_of_isUnit I hI 𝔪
  · intro h
    rw [← FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)]
    have hle : I * I⁻¹ ≤ 1 := by
      rw [FractionalIdeal.inv_eq]; exact FractionalIdeal.mul_one_div_le_one
    obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
    suffices hJtop : J = ⊤ by
      rw [← hJ, hJtop, FractionalIdeal.coeIdeal_top]
    by_contra hJne
    obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := J.exists_le_maximal hJne
    have : 𝔪.IsMaximal := h𝔪max
    have hunit := h 𝔪
    rw [← FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)] at hunit
    have step1 : (1 : FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A)) ≤
        localizeAtPrime 𝔪 I * localizeAtPrime 𝔪 (I⁻¹) :=
      hunit ▸ mul_le_mul' le_rfl (inv_localizeAtPrime_le 𝔪 I)
    have step2 : localizeAtPrime 𝔪 I * localizeAtPrime 𝔪 (I⁻¹) =
        localizeAtPrime 𝔪 (I * I⁻¹) := by
      exact (map_mul (extendedHom (FractionRing A) (Localization.AtPrime 𝔪))
        I I⁻¹).symm
    have step3 : localizeAtPrime 𝔪 (I * I⁻¹) =
        ↑(J.map (algebraMap A (Localization.AtPrime 𝔪))) := by
      have : I * I⁻¹ = ↑J := hJ.symm
      rw [this]
      simp only [localizeAtPrime]
      exact FractionalIdeal.extendedHom_coeIdeal_eq_map (FractionRing A)
        (Localization.AtPrime 𝔪) J
    have h1le : (1 : FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A)) ≤
        ↑(J.map (algebraMap A (Localization.AtPrime 𝔪))) :=
      step1.trans (step2.le.trans step3.le)
    have hJmap_top : J.map (algebraMap A (Localization.AtPrime 𝔪)) = ⊤ := by
      rw [← FractionalIdeal.coeIdeal_top] at h1le
      exact le_antisymm le_top ((FractionalIdeal.coeIdeal_le_coeIdeal _).mp h1le)
    have h𝔪map_ne_top : 𝔪.map (algebraMap A (Localization.AtPrime 𝔪)) ≠ ⊤ :=
      Ideal.IsPrime.ne_top'
    exact h𝔪map_ne_top (eq_top_iff.mpr (hJmap_top ▸ Ideal.map_mono h𝔪le))

/-- **Theorem 3.2** (prime-ideal form). A fractional ideal of a Noetherian domain is invertible iff
its localization at every prime ideal is invertible. -/
theorem isUnit_iff_isUnit_localizeAtPrime_all_primes
    [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    IsUnit I ↔ ∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsUnit (localizeAtPrime 𝔭 I) := by
  constructor
  · intro hI 𝔭 _
    exact isUnit_localizeAtPrime_of_isUnit I hI 𝔭
  · intro h
    rw [isUnit_iff_isUnit_localizeAtPrime]
    intro 𝔪 h𝔪
    have : 𝔪.IsPrime := h𝔪.isPrime
    exact h 𝔪

/-- **Corollary 3.5.** A nonzero fractional ideal of a Noetherian domain is invertible iff it is
locally principal. -/
theorem isUnit_iff_isLocallyPrincipal
    [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) (hI : I ≠ 0) :
    IsUnit I ↔ I.IsLocallyPrincipal := by
  rw [isUnit_iff_isUnit_localizeAtPrime]
  constructor
  · intro h 𝔪 h𝔪
    have hne : I.localizeAtPrime 𝔪 ≠ 0 := localizeAtPrime_ne_zero 𝔪 hI
    exact (fractionalIdeal_isUnit_iff_isPrincipal _ _ _ hne).mp (h 𝔪)
  · intro h 𝔪 h𝔪
    have hne : I.localizeAtPrime 𝔪 ≠ 0 := localizeAtPrime_ne_zero 𝔪 hI
    exact (fractionalIdeal_isUnit_iff_isPrincipal _ _ _ hne).mpr (h 𝔪)

end FractionalIdeal

end
