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
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Minimal-prime formulas for a local one-element Euler characteristic

For a noetherian local ring with support dimension at most one, the regular-module invariant
χ_r(R) is the finite-support sum over minimal primes p of ℓ_{R_p}(R_p) times the principal
quotient length on R/p when r ∉ p, and zero when r ∈ p.

The formula includes every r with finite multiplication kernel and cokernel lengths, including
units. Subtracting two such invariants gives the same minimal-prime sum with the corresponding
difference of principal quotient contributions.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u v

namespace Module

open Classical in
private theorem minimalTerm_hasFiniteSupport
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (r : R) (h : Module.ElementEulerFiniteLength R R r) :
    Function.HasFiniteSupport (fun p : PrimeSpectrum R => if IsMin p then
      if r ∈ p.asIdeal then 0 else
        ((Module.length (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
            (Module.length R ((R ⧸ p.asIdeal) ⧸
              (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range)).toNat
      else 0) := by
  classical
  let d := Classical.choice (Module.exists_elementEulerPrimeDecomposition R R r h.cokernel_ne_top)
  let s := d.factors.toFinset.image (fun f => f.prime)
  apply s.finite_toSet.subset
  intro p hp
  have hmin : IsMin p := by
    by_contra hnot
    exact hp (by simp [hnot])
  obtain ⟨f, hf, hfp⟩ := d.exists_factor_prime_eq_of_isMin R p hmin
  exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, hfp⟩

open Classical in
/-- The actual finite one-element Euler operator is the complete original
minimal-prime quotient-length sum in a one-dimensional local coefficient ring. -/
private theorem elementEulerCharacteristic_eq_finsum_minimal_maximal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R R ≤ 1) (h : Module.ElementEulerFiniteLength R R r) :
    Module.elementEulerCharacteristic R R r h =
      ∑ᶠ p : PrimeSpectrum R, if IsMin p then
        if r ∈ p.asIdeal then 0 else
          ((Module.length (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
              (Module.length R ((R ⧸ p.asIdeal) ⧸
                (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range)).toNat
        else 0 := by
  classical
  let d := Classical.choice (Module.exists_elementEulerPrimeDecomposition R R r h.cokernel_ne_top)
  let sf := d.factors.toFinset
  let s := sf.image (fun f => f.prime)
  let term : PrimeSpectrum R → ℤ := fun p => if IsMin p then
    if r ∈ p.asIdeal then 0 else
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
          (Module.length R ((R ⧸ p.asIdeal) ⧸
            (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range)).toNat
    else 0
  have hterm (f : Module.ElementEulerPrimeFactor R r) (hf : f ∈ sf) :
      term f.prime =
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl R)).toNat : ℤ) * f.value R := by
    rw [Module.ElementEulerPrimeFactor.value_eq_ite R]
    by_cases hrf : r ∈ f.prime.asIdeal
    · simp [term, hrf]
    · have hfList : f ∈ d.factors := List.mem_toFinset.mp hf
      have hmin := d.factor_prime_isMin_of_not_mem_of_supportDim_le_one R hr hdim f hfList hrf
      simp [term, hrf, hmin]
  have hs : Function.support term ⊆ (s : Set (PrimeSpectrum R)) := by
    intro p hp
    by_contra hps
    have hmin : IsMin p := by
      by_contra hnot
      exact hp (by simp [term, hnot])
    obtain ⟨f, hf, hfp⟩ := d.exists_factor_prime_eq_of_isMin R p hmin
    apply hps
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, hfp⟩
  calc
    Module.elementEulerCharacteristic R R r h =
        ∑ f ∈ sf, ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl R)).toNat : ℤ) * f.value R :=
      d.eq_sum_localizedLength_mul_of_supportDim_le_one R hr hdim
    _ = ∑ f ∈ sf, term f.prime := by
      apply Finset.sum_congr rfl
      intro f hf
      exact (hterm f hf).symm
    _ = ∑ p ∈ s, term p := by
      dsimp only [s]
      exact (Finset.sum_image (fun f hf g hg he =>
        (Module.ElementEulerPrimeFactor.eq_iff_prime_eq R).mpr he)).symm
    _ = ∑ᶠ p : PrimeSpectrum R, term p :=
      (finsum_eq_sum_of_support_subset term hs).symm


private theorem unitCokernel_length_zero
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (hu : IsUnit r) :
    Module.length R (M ⧸ (LinearMap.lsmul R M r).range) = 0 := by
  have hsur : Function.Surjective (LinearMap.lsmul R M r) := hu.smul_bijective.2
  rw [LinearMap.range_eq_top.mpr hsur]
  simp

private theorem unitEuler_eq_zero
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (h : Module.ElementEulerFiniteLength R M r) (hu : IsUnit r) :
    Module.elementEulerCharacteristic R M r h = 0 := by
  have hinj : Function.Injective (LinearMap.lsmul R M r) := hu.smul_bijective.1
  unfold Module.elementEulerCharacteristic
  rw [unitCokernel_length_zero R M r hu, LinearMap.ker_eq_bot.mpr hinj, Module.length_bot]
  simp

open Classical in
/-- The complete minimal-prime sum for a one-element Euler characteristic.

For the stated local noetherian ring and support-dimension bound, χ_r(R) is the sum over
minimal primes of their generic localized lengths times the principal quotient contribution,
zero for primes containing r. -/
theorem elementEulerCharacteristic_eq_finsum_minimal_full
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (r : R) (hdim : Module.supportDim R R ≤ 1)
    (h : Module.ElementEulerFiniteLength R R r) :
    Module.elementEulerCharacteristic R R r h =
      ∑ᶠ p : PrimeSpectrum R, if IsMin p then
        if r ∈ p.asIdeal then 0 else
          ((Module.length (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
              (Module.length R ((R ⧸ p.asIdeal) ⧸
                (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range)).toNat
        else 0 := by
  classical
  by_cases hu : IsUnit r
  · have hzero (p : PrimeSpectrum R) :
        (if IsMin p then
          if r ∈ p.asIdeal then 0 else
            ((Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
                (Module.length R ((R ⧸ p.asIdeal) ⧸
                  (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range)).toNat
          else 0) = 0 := by
      by_cases hmin : IsMin p <;>
        simp [hmin, unitCokernel_length_zero R (R ⧸ p.asIdeal) r hu]
    rw [unitEuler_eq_zero R R r h hu]
    simp_rw [hzero]
    simp
  · have hr : r ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal r).mpr hu
    exact elementEulerCharacteristic_eq_finsum_minimal_maximal R r hr hdim h

open Classical in
/-- The difference of two one-element Euler invariants on a common prime index.

For a,b with finite multiplication lengths, χ_a(R)−χ_b(R) is the minimal-prime sum of generic
multiplicities times the difference of their principal quotient contributions. -/
theorem elementEulerDifference_eq_finsum_minimal_full
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (a b : R)
    (hdim : Module.supportDim R R ≤ 1)
    (hA : Module.ElementEulerFiniteLength R R a) (hB : Module.ElementEulerFiniteLength R R b) :
    Module.elementEulerCharacteristic R R a hA - Module.elementEulerCharacteristic R R b hB =
      ∑ᶠ p : PrimeSpectrum R, if IsMin p then
        ((Module.length (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
            ((if a ∈ p.asIdeal then 0 else
              (Module.length R ((R ⧸ p.asIdeal) ⧸
                (LinearMap.lsmul R (R ⧸ p.asIdeal) a).range)).toNat : ℤ) -
             (if b ∈ p.asIdeal then 0 else
              (Module.length R ((R ⧸ p.asIdeal) ⧸
                (LinearMap.lsmul R (R ⧸ p.asIdeal) b).range)).toNat : ℤ))
        else 0 := by
  classical
  let f : PrimeSpectrum R → ℤ := fun p => if IsMin p then
    if a ∈ p.asIdeal then 0 else
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
          (Module.length R ((R ⧸ p.asIdeal) ⧸
            (LinearMap.lsmul R (R ⧸ p.asIdeal) a).range)).toNat
    else 0
  let g : PrimeSpectrum R → ℤ := fun p => if IsMin p then
    if b ∈ p.asIdeal then 0 else
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl R)).toNat : ℤ) *
          (Module.length R ((R ⧸ p.asIdeal) ⧸
            (LinearMap.lsmul R (R ⧸ p.asIdeal) b).range)).toNat
    else 0
  have hf : Function.HasFiniteSupport f := minimalTerm_hasFiniteSupport R a hA
  have hg : Function.HasFiniteSupport g := minimalTerm_hasFiniteSupport R b hB
  have hfa : Module.elementEulerCharacteristic R R a hA = ∑ᶠ p, f p :=
    elementEulerCharacteristic_eq_finsum_minimal_full R a hdim hA
  have hgb : Module.elementEulerCharacteristic R R b hB = ∑ᶠ p, g p :=
    elementEulerCharacteristic_eq_finsum_minimal_full R b hdim hB
  rw [hfa, hgb, ← finsum_sub_distrib hf hg]
  apply finsum_congr
  intro p
  by_cases hmin : IsMin p
  · by_cases hap : a ∈ p.asIdeal <;> by_cases hbp : b ∈ p.asIdeal <;>
      simp [f, g, hmin, hap, hbp, mul_sub]
  · simp [f, g, hmin]

end Module
