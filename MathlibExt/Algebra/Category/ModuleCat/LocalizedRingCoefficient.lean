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

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnderSurjection

/-!
# Localized ring coefficients under a surjective scalar map

Let f : R → S be a surjective map of commutative rings, let p be a prime ideal of S and put q
= f⁻¹p. Localizing the R-module obtained by restricting a lifted copy of S at q gives the
restriction of a lifted copy of S_p along the canonical local ring map R_q → S_p.

The isomorphism retains the separate ring universes and the coefficient lift height
max(u,v,m).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat
universe u v m

/-- The localized restricted ring-coefficient isomorphism.

For surjective f : R → S and prime p ⊆ S, the localization at q = p.comap f of the restricted
lifted S-module is isomorphic to the lifted S_p-module restricted along
Localization.localRingHom q p f. -/
def localizedRingCoefficientIso
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    ModuleCat.of (Localization.AtPrime (p.comap f))
        (LocalizedModule.AtPrime (p.comap f)
          ((restrictScalars f).obj (ModuleCat.of S (ULift.{max u v m} S)))) ≅
      (restrictScalars (Localization.localRingHom (p.comap f) p f rfl)).obj
        (ModuleCat.of (Localization.AtPrime p)
          (ULift.{max u v m} (Localization.AtPrime p))) := by
  let C := ModuleCat.of S (ULift.{max u v m} S)
  let e₀ := (localizedQuotientModuleEquiv f hf p C).toModuleIso
  let e₁ : LocalizedModule.AtPrime p (ULift.{max u v m} S) ≃ₗ[Localization.AtPrime p]
      Localization.AtPrime p :=
    IsLocalizedModule.mapEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (ULift.{max u v m} S))
      (Algebra.linearMap S (Localization.AtPrime p)) (Localization.AtPrime p)
      (ULift.moduleEquiv : ULift.{max u v m} S ≃ₗ[S] S)
  let e₂ := (e₁.trans
    (ULift.moduleEquiv : ULift.{max u v m} (Localization.AtPrime p) ≃ₗ[
      Localization.AtPrime p] Localization.AtPrime p).symm).toModuleIso
  exact e₀ ≪≫ (restrictScalars
    (Localization.localRingHom (p.comap f) p f rfl)).mapIso e₂

end ModuleCat
