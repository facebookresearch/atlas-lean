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
# Localization, length and support under surjective scalar maps

Let f:R→S be a surjective homomorphism of commutative rings. For a prime p of S and q=f⁻¹(p),
localizing an S-module M at p is canonically the localization of its R-restriction at q, viewed
over R_q through the surjective local-ring map R_q→S_p. The comparison sends a fraction m/r to
m/f(r), and gives ℓ_{R_q}((U_fM)_q)=ℓ_{S_p}(M_p), including infinite lengths.

The same comparison identifies support at corresponding primes. For arbitrary M,
Supp_R(U_fM)=comap(f)(Supp_S(M)); the kernel of f annihilates U_fM. When an R-algebra structure
on S and compatible R,S-actions on M are already given, the formulas apply to those actions.
Ring and module universes are independent, and finite generation is not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace ModuleCat

universe r s m

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. Assume S is an R-algebra with surjective algebra map, p⊂S is prime, and
M has R- and S-module structures satisfying r•x=algebraMap(R,S)(r)•x. Put q=p∩R and ψ:R_q→S_p.
This is the R_q-linear isomorphism M_q≅U_ψ(M_p), induced by m/r↦m/algebraMap(r). It uses the
given R-action on M. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. For a surjective ring map f:R→S, a prime p⊂S and any S-module M, put
q=f⁻¹(p) and ψ:R_q→S_p. The canonical R_q-linear isomorphism (U_fM)_q≅U_ψ(M_p) sends m/r to
m/f(r). Its inverse uses surjectivity of f on the complements of the corresponding primes. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. For surjective f:R→S, prime p⊂S and any S-module M, let q=f⁻¹(p). Then
ℓ_{R_q}((U_fM)_q)=ℓ_{S_p}(M_p) as extended natural numbers. The localized-module isomorphism and
surjectivity of R_q→S_p preserve the submodule-length computation, including infinite length. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. For surjective f:R→S, p∈Spec(S) and an S-module M, the inverse-image
prime comap(f)(p) belongs to Supp_R(U_fM) if and only if p belongs to Supp_S(M). The canonical
localized-module isomorphism identifies the two localizations, whose nontriviality defines
support. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. For any ring homomorphism f:R→S and S-module M, ker(f)⊆Ann_R(U_fM). If
r∈ker(f), its action on the restricted module is f(r)•x=0 for every x∈M. This statement does not
require f to be surjective. -/
theorem ker_le_annihilator_restrictScalars (f : R →+* S) (M : ModuleCat.{m} S) :
    RingHom.ker f ≤ Module.annihilator R ((restrictScalars f).obj M) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  change f r • (show M from x) = 0
  rw [RingHom.mem_ker.mp hr, zero_smul]

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. For surjective f:R→S and an arbitrary S-module M,
Supp_R(U_fM)=comap(f)(Supp_S(M)) as subsets of Spec(R). Every prime supporting U_fM contains
ker(f), and the localized-module comparison identifies it with the inverse image of a supporting
prime of S. No finite-generation hypothesis on M is imposed. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. Assume S is an R-algebra with surjective algebra map and M has
compatible R,S-actions, r•x=algebraMap(r)•x. For a prime p⊂S and q=p∩R, the local lengths
satisfy ℓ_{R_q}(M_q)=ℓ_{S_p}(M_p), with the given module structures used in both localizations.
The equality is in extended natural numbers. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. Let S be an R-algebra with surjective algebra map and M carry compatible
R,S-actions. For p∈Spec(S), comap(algebraMap)(p)∈Supp_R(M) if and only if p∈Supp_S(M).
Compatibility means r•x=algebraMap(r)•x, and the two localizations are related by the canonical
linear comparison over the local ring of R. -/
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

/-- Let R,S be commutative rings in independent universes r,s, and let the module carrier universe m
be independent of both. If S is an R-algebra with surjective algebra map and M has compatible
R,S-module structures, then Supp_R(M)=comap(algebraMap)(Supp_S(M)). This set equality uses the
given base-ring action and holds for arbitrary M, including modules that are not finitely
generated. -/
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
