/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits

public section
noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u v w

/-- The canonical comparison accepts independent source-ring, target-ring
and module universes, with the literal localized coefficient carrier. -/
example (R : Type u) (Q : Type v) [CommRing R] [CommRing Q]
    (f : R →+* Q) (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) :
    LocalizedModule q.asIdeal.primeCompl ((ModuleCat.extendScalars f).obj M) ≃ₗ[
      Localization.AtPrime q.asIdeal]
      (ModuleCat.extendScalars
        (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl)).obj
        (ModuleCat.of (Localization.AtPrime (q.asIdeal.comap f))
          (LocalizedModule (q.asIdeal.comap f).primeCompl M)) :=
  ModuleCat.localizedExtensionLinearEquiv R Q f q M

/-- Every actual localized unit tensor is preserved by the public comparison. -/
example (R : Type u) (Q : Type v) [CommRing R] [CommRing Q]
    (f : R →+* Q) (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) (m : M) :
    ModuleCat.localizedExtensionLinearEquiv R Q f q M
      (LocalizedModule.mk ((1 : Q) ⊗ₜ[R, f] m) (1 : q.asIdeal.primeCompl)) =
      (1 : Localization.AtPrime q.asIdeal) ⊗ₜ[
        Localization.AtPrime (q.asIdeal.comap f),
        Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl]
        (LocalizedModule.mk m (1 : (q.asIdeal.comap f).primeCompl)) :=
  ModuleCat.localizedExtensionLinearEquiv_mk_one_tmul R Q f q M m

/-- Flat localization preserves the full ENat length formula, without a
finite-length hypothesis on the original coefficient module. -/
example (R : Type u) (Q : Type v) [CommRing R] [CommRing Q]
    (f : R →+* Q) (hf : f.Flat) (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl ((ModuleCat.extendScalars f).obj M)) =
      Module.length (Localization.AtPrime (q.asIdeal.comap f))
        (LocalizedModule (q.asIdeal.comap f).primeCompl M) *
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⧸
          (IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.comap f))).map
            (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl)) :=
  ModuleCat.localizedExtension_length_baseChange R Q f hf q M
