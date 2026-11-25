/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.Localization.AtPrimeSurjective
public import MathlibExt.Algebra.Category.ModuleCat.Length
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Module localization under a surjective scalar map

For a surjective ring map `R → S`, localizing an `S`-module at a prime
of `S` agrees with localizing its restriction at the inverse-image prime.
The comparison is linear over the actual local ring of `R`. Its composition
length agrees with the length over the local ring of `S`, including infinite
length. The two ring universes and the module universe are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace ModuleCat

universe r s m

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]

/-- Localization under a surjective algebra map, retaining an existing
base-ring module action related by its actual scalar tower. -/
def localizedModuleEquivOfSurjective [Algebra R S]
    (hf : Function.Surjective (algebraMap R S)) (p : Ideal S) [p.IsPrime]
    (M : Type m) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    LocalizedModule.AtPrime (p.comap (algebraMap R S)) M ≃ₗ[
        Localization.AtPrime (p.comap (algebraMap R S))]
      (restrictScalars
        (Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl)).obj
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) := by
  let f := algebraMap R S
  let q := p.comap f
  letI : p.LiesOver q := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver q p
  letI : IsScalarTower R S (LocalizedModule.AtPrime p M) := inferInstance
  letI : Module (Localization.AtPrime q) (LocalizedModule.AtPrime p M) :=
    Module.compHom _ (Localization.localRingHom q p f rfl)
  letI : IsScalarTower R (Localization.AtPrime q) (LocalizedModule.AtPrime p M) := by
    apply IsScalarTower.of_algebraMap_smul
    intro x y
    change (Localization.localRingHom q p f rfl
      (algebraMap R (Localization.AtPrime q) x)) • y = _
    rw [Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_smul (Localization.AtPrime p)]
    exact IsScalarTower.algebraMap_smul S x y
  let g := LocalizedModule.mkLinearMap p.primeCompl M
  have hcompl : Algebra.algebraMapSubmonoid S q.primeCompl = p.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f hf p
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid S q.primeCompl) g := by
    rw [hcompl]
    exact localizedModuleIsLocalizedModule _
  letI : IsLocalizedModule q.primeCompl (g.restrictScalars R) :=
    IsLocalizedModule.restrictScalars q.primeCompl g
  exact IsLocalizedModule.mapEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl M)
    (g.restrictScalars R) (Localization.AtPrime q) (LinearEquiv.refl R M)

/-- The actual local module comparison along a surjective scalar map. -/
def localizedQuotientModuleEquiv (f : R →+* S) (hf : Function.Surjective f)
    (p : Ideal S) [p.IsPrime] (M : ModuleCat.{m} S) :
    LocalizedModule.AtPrime (p.comap f) ((restrictScalars f).obj M) ≃ₗ[
        Localization.AtPrime (p.comap f)]
      (restrictScalars (Localization.localRingHom (p.comap f) p f rfl)).obj
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact localizedModuleEquivOfSurjective hf p M

/-- Local composition lengths agree under the actual local quotient map. -/
theorem localizedQuotientModuleLength (f : R →+* S) (hf : Function.Surjective f)
    (p : Ideal S) [p.IsPrime] (M : ModuleCat.{m} S) :
    Module.length (Localization.AtPrime (p.comap f))
        (LocalizedModule.AtPrime (p.comap f) ((restrictScalars f).obj M)) =
      Module.length (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
  (localizedQuotientModuleEquiv f hf p M).length_eq.trans
    (restrictScalars_length_eq
      (Localization.localRingHom (p.comap f) p f rfl)
      (Localization.localRingHom_surjective f hf p)
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)))

/-- A prime belongs to the support of an `S`-module precisely when its
inverse image belongs to the support of the restricted module. -/
theorem mem_support_restrictScalars_comap (f : R →+* S) (hf : Function.Surjective f)
    (p : PrimeSpectrum S) (M : ModuleCat.{m} S) :
    PrimeSpectrum.comap f p ∈ Module.support R ((restrictScalars f).obj M) ↔
      p ∈ Module.support S M := by
  let e := localizedQuotientModuleEquiv f hf p.asIdeal M
  change Nontrivial (LocalizedModule.AtPrime (p.asIdeal.comap f)
      ((restrictScalars f).obj M)) ↔ Nontrivial (LocalizedModule.AtPrime p.asIdeal M)
  constructor
  · intro h
    exact @Equiv.nontrivial _ _ e.toEquiv.symm h
  · intro h
    exact @Equiv.nontrivial _ _ e.toEquiv h

/-- The kernel of the scalar map annihilates the actual restricted module. -/
theorem ker_le_annihilator_restrictScalars (f : R →+* S) (M : ModuleCat.{m} S) :
    RingHom.ker f ≤ Module.annihilator R ((restrictScalars f).obj M) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  change f r • (show M from x) = 0
  rw [RingHom.mem_ker.mp hr, zero_smul]

/-- For arbitrary modules, support under a surjective scalar map is the
image of the actual support; no finite-generation hypothesis is needed. -/
theorem support_restrictScalars_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{m} S) :
    Module.support R ((restrictScalars f).obj M) =
      PrimeSpectrum.comap f '' Module.support S M := by
  ext p
  constructor
  · intro hp
    have hk : RingHom.ker f ≤ p.asIdeal :=
      (ker_le_annihilator_restrictScalars f M).trans
        (Module.annihilator_le_of_mem_support hp)
    have : (p.asIdeal.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hk
    let q : PrimeSpectrum S := ⟨p.asIdeal.map f, inferInstance⟩
    have hq : PrimeSpectrum.comap f q = p := by
      apply PrimeSpectrum.ext
      exact (Ideal.comap_map_of_surjective f hf p.asIdeal).trans (sup_eq_left.mpr hk)
    refine ⟨q, ?_, hq⟩
    exact (mem_support_restrictScalars_comap f hf q M).mp (hq.symm ▸ hp)
  · rintro ⟨q, hq, rfl⟩
    exact (mem_support_restrictScalars_comap f hf q M).mpr hq

/-- Actual local lengths under a surjective algebra map, preserving the
existing base-ring module instead of changing its scalar action. -/
theorem localizedModuleLengthOfSurjective [Algebra R S]
    (hf : Function.Surjective (algebraMap R S)) (p : Ideal S) [p.IsPrime]
    (M : Type m) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.length (Localization.AtPrime (p.comap (algebraMap R S)))
        (LocalizedModule.AtPrime (p.comap (algebraMap R S)) M) =
      Module.length (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
  (localizedModuleEquivOfSurjective hf p M).length_eq.trans
    (restrictScalars_length_eq
      (Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl)
      (Localization.localRingHom_surjective (algebraMap R S) hf p)
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)))

/-- Support at an inverse-image prime under an actual surjective algebra
map, with the original base-ring module action retained. -/
theorem mem_support_comap_of_surjective [Algebra R S]
    (hf : Function.Surjective (algebraMap R S)) (p : PrimeSpectrum S)
    (M : Type m) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    PrimeSpectrum.comap (algebraMap R S) p ∈ Module.support R M ↔
      p ∈ Module.support S M := by
  change Nontrivial (LocalizedModule.AtPrime (p.asIdeal.comap (algebraMap R S)) M) ↔
    Nontrivial (LocalizedModule.AtPrime p.asIdeal M)
  let e := localizedModuleEquivOfSurjective hf p.asIdeal M
  exact ⟨fun h => @Equiv.nontrivial _ _ e.toEquiv.symm h,
    fun h => @Equiv.nontrivial _ _ e.toEquiv h⟩

/-- A native module's support under a surjective algebra map is exactly
 the image of its support over the scalar algebra. -/
theorem _root_.Module.support_eq_image_of_surjective [Algebra R S]
    (hf : Function.Surjective (algebraMap R S))
    (M : Type m) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.support R M = PrimeSpectrum.comap (algebraMap R S) '' Module.support S M := by
  ext p
  constructor
  · intro hp
    have hk : RingHom.ker (algebraMap R S) ≤ p.asIdeal := by
      apply le_trans ?_ (Module.annihilator_le_of_mem_support hp)
      intro r hr
      apply Module.mem_annihilator.mpr
      intro x
      rw [← IsScalarTower.algebraMap_smul S r x, RingHom.mem_ker.mp hr, zero_smul]
    have : (p.asIdeal.map (algebraMap R S)).IsPrime := Ideal.map_isPrime_of_surjective hf hk
    let q : PrimeSpectrum S := ⟨p.asIdeal.map (algebraMap R S), inferInstance⟩
    have hq : PrimeSpectrum.comap (algebraMap R S) q = p := by
      apply PrimeSpectrum.ext
      exact (Ideal.comap_map_of_surjective (algebraMap R S) hf p.asIdeal).trans
        (sup_eq_left.mpr hk)
    refine ⟨q, ?_, hq⟩
    exact (mem_support_comap_of_surjective hf q M).mp (hq.symm ▸ hp)
  · rintro ⟨q, hq, rfl⟩
    exact (mem_support_comap_of_surjective hf q M).mpr hq

end ModuleCat
