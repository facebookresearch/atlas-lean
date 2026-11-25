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

/-! # Actual localized ring coefficients under a surjective scalar map -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat
universe u v m

/-- Localizing the actual restricted ring coefficient gives its original
localized ring coefficient with the literal local scalar map. -/
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
