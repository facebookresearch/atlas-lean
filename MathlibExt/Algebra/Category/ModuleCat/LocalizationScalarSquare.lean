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

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits
public import Mathlib.RingTheory.Localization.Module

/-!
# Scalar extension and restriction in a localization square

Consider a commuting square of commutative rings R → A, R → R′, A → A′ and R′ → A′, with maps
φ,γ,δ,ψ satisfying ψγ = δφ. Assume γ localizes R at a submonoid T and δ localizes A at the
image φ(T).

For an A-module M, there is a natural R′-linear isomorphism R′ ⊗_R (M restricted along φ) ≅
(A′ ⊗_A M) restricted along ψ. It sends r ⊗ m to ψ(r) ⊗ m and in particular preserves the
element inserted as 1 ⊗ m. The scalar maps are the specified maps of the square.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u

variable (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
variable (φ : R →+* A) (γ : R →+* R') (δ : A →+* A') (ψ : R' →+* A')
variable (T : Submonoid R) (h : ψ.comp γ = δ.comp φ)

/-- The module comparison in a commuting localization square.

If γ and δ are the localizations at T and φ(T), respectively, scalar extension along γ after
restriction along φ is naturally identified with scalar extension along δ followed by
restriction along ψ. -/
def localizationScalarSquareIso
    (hR : letI : Algebra R R' := γ.toAlgebra; IsLocalization T R')
    (hA : letI : Algebra A A' := δ.toAlgebra; IsLocalization (T.map φ) A')
    (M : ModuleCat.{u} A) :
    (extendScalars γ).obj ((restrictScalars φ).obj M) ≅
      (restrictScalars ψ).obj ((extendScalars δ).obj M) := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra R R' := γ.toAlgebra
  letI : Algebra A A' := δ.toAlgebra
  letI : IsLocalization T R' := hR
  letI : IsLocalization (T.map φ) A' := hA
  let N := ModuleCat.of A' (A' ⊗[A] M)
  let NR := (restrictScalars ψ).obj N
  letI : Module R M := Module.compHom M φ
  letI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Algebra R A' := (δ.comp φ).toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq
    (fun r => by simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])
  letI : Module R NR := Module.compHom NR γ
  letI : Module A NR := Module.compHom NR δ
  letI : IsScalarTower R R' NR := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  letI : IsScalarTower A A' NR := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  letI : IsScalarTower R A NR := by
    apply IsScalarTower.of_algebraMap_smul
    intro r n
    change δ (φ r) • n = ψ (γ r) • n
    exact congrArg (fun c : A' => c • n) (DFunLike.congr_fun h r).symm
  let MR := (restrictScalars φ).obj M
  let fE : MR →ₗ[R] R' ⊗[R] MR := TensorProduct.mk R R' MR 1
  let fN : M →ₗ[A] NR := TensorProduct.mk A A' M 1
  letI : IsLocalizedModule T fE :=
    (isLocalizedModule_iff_isBaseChange T R' fE).mpr (TensorProduct.isBaseChange R MR R')
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid A T) fN := by
    change IsLocalizedModule (T.map φ) fN
    exact (isLocalizedModule_iff_isBaseChange (T.map φ) A' fN).mpr
      (TensorProduct.isBaseChange A M A')
  letI : IsLocalizedModule T (fN.restrictScalars R) := IsLocalizedModule.restrictScalars T fN
  let e : R' ⊗[R] MR ≃ₗ[R'] NR :=
    IsLocalizedModule.mapEquiv T fE (fN.restrictScalars R) R' (LinearEquiv.refl R MR)
  let eE := extendedCarrierTensorEquiv R R' γ MR
  let eN := extendedCarrierTensorEquiv A A' δ M
  exact eE.toModuleIso ≪≫ e.toModuleIso ≪≫
    (restrictScalars ψ).mapIso eN.symm.toModuleIso

/-- The localization-square comparison on inserted module elements.

For m ∈ M, the comparison sends 1 ⊗_R m to 1 ⊗_A m. -/
theorem localizationScalarSquareIso_hom_one_tmul
    (hR : letI : Algebra R R' := γ.toAlgebra; IsLocalization T R')
    (hA : letI : Algebra A A' := δ.toAlgebra; IsLocalization (T.map φ) A')
    (M : ModuleCat.{u} A) (m : M) :
    (localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M).hom
      ((1 : R') ⊗ₜ[R, γ] m) = (1 : A') ⊗ₜ[A, δ] m := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra R R' := γ.toAlgebra
  let : Algebra A A' := δ.toAlgebra
  let : IsLocalization T R' := hR
  let : IsLocalization (T.map φ) A' := hA
  let N := ModuleCat.of A' (A' ⊗[A] M)
  let NR := (restrictScalars ψ).obj N
  let : Module R M := Module.compHom M φ
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Algebra R A' := (δ.comp φ).toAlgebra
  let : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq
    (fun r => by simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])
  let : Module R NR := Module.compHom NR γ
  let : Module A NR := Module.compHom NR δ
  let : IsScalarTower R R' NR := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  let : IsScalarTower A A' NR := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  let : IsScalarTower R A NR := by
    apply IsScalarTower.of_algebraMap_smul
    intro r n
    change δ (φ r) • n = ψ (γ r) • n
    exact congrArg (fun c : A' => c • n) (DFunLike.congr_fun h r).symm
  let MR := (restrictScalars φ).obj M
  let fE : MR →ₗ[R] R' ⊗[R] MR := TensorProduct.mk R R' MR 1
  let fN : M →ₗ[A] NR := TensorProduct.mk A A' M 1
  let : IsLocalizedModule T fE :=
    (isLocalizedModule_iff_isBaseChange T R' fE).mpr (TensorProduct.isBaseChange R MR R')
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid A T) fN := by
    change IsLocalizedModule (T.map φ) fN
    exact (isLocalizedModule_iff_isBaseChange (T.map φ) A' fN).mpr
      (TensorProduct.isBaseChange A M A')
  let : IsLocalizedModule T (fN.restrictScalars R) := IsLocalizedModule.restrictScalars T fN
  let e : R' ⊗[R] MR ≃ₗ[R'] NR :=
    IsLocalizedModule.mapEquiv T fE (fN.restrictScalars R) R' (LinearEquiv.refl R MR)
  let eE := extendedCarrierTensorEquiv R R' γ MR
  let eN := extendedCarrierTensorEquiv A A' δ M
  have hm : e (fE m) = fN m :=
    (IsLocalizedModule.mapEquiv_apply T fE (fN.restrictScalars R) R'
      (LinearEquiv.refl R MR) (fE m)).trans
      (IsLocalizedModule.map_apply T fE (fN.restrictScalars R)
        (LinearEquiv.refl R MR).toLinearMap m)
  have hE : eE ((1 : R') ⊗ₜ[R, γ] m) = fE m :=
    extendedCarrierTensorEquiv_tmul R R' γ MR 1 m
  have hN : eN ((1 : A') ⊗ₜ[A, δ] m) = fN m :=
    extendedCarrierTensorEquiv_tmul A A' δ M 1 m
  change eN.symm (e (eE ((1 : R') ⊗ₜ[R, γ] m))) = _
  exact (congrArg (fun x => eN.symm (e x)) hE).trans
    ((congrArg (fun x => eN.symm x) hm).trans
      ((congrArg (fun x => eN.symm x) hN.symm).trans (eN.symm_apply_apply _)))

/-- The localization-square comparison on pure tensors.

For r ∈ R′ and m ∈ M, the comparison sends r ⊗_R m to ψ(r) ⊗_A m in the target restricted
R′-module. -/
theorem localizationScalarSquareIso_hom_tmul
    (hR : letI : Algebra R R' := γ.toAlgebra; IsLocalization T R')
    (hA : letI : Algebra A A' := δ.toAlgebra; IsLocalization (T.map φ) A')
    (M : ModuleCat.{u} A) (r : R') (m : M) :
    (localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M).hom
      (r ⊗ₜ[R, γ] m) = ψ r ⊗ₜ[A, δ] m := by
  let : Algebra R R' := γ.toAlgebra
  let : Algebra A A' := δ.toAlgebra
  let : Module R M := Module.compHom M φ
  let e := localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M
  have hE := ExtendScalars.smul_tmul γ r 1 (show (restrictScalars φ).obj M from m)
  have hN := ExtendScalars.smul_tmul δ (ψ r) 1 m
  rw [mul_one] at hE hN
  have hm := localizationScalarSquareIso_hom_one_tmul R A R' A' φ γ δ ψ T h hR hA M m
  exact (congrArg (fun x => e.hom x) hE.symm).trans
    ((e.hom.hom.map_smul r _).trans
      ((congrArg (fun x : (restrictScalars ψ).obj ((extendScalars δ).obj M) => r • x) hm).trans hN))

/-- Naturality of the localization-square comparison in the coefficient module.

For an A-linear map f : M → N, the comparison commutes with extending the restricted map along
γ and with restricting the extended map along δ. -/
theorem localizationScalarSquareIso_hom_naturality
    (hR : letI : Algebra R R' := γ.toAlgebra; IsLocalization T R')
    (hA : letI : Algebra A A' := δ.toAlgebra; IsLocalization (T.map φ) A')
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (extendScalars γ).map ((restrictScalars φ).map f) ≫
        (localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA N).hom =
      (localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M).hom ≫
        (restrictScalars ψ).map ((extendScalars δ).map f) := by
  apply ExtendScalars.hom_ext
  intro m
  let eM := localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M
  let eN := localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA N
  have hE := ExtendScalars.map_tmul γ ((restrictScalars φ).map f) 1 m
  have hM := localizationScalarSquareIso_hom_one_tmul R A R' A' φ γ δ ψ T h hR hA M m
  have hN := localizationScalarSquareIso_hom_one_tmul R A R' A' φ γ δ ψ T h hR hA N (f m)
  have hF := ExtendScalars.map_tmul δ f 1 m
  change eN.hom ((extendScalars γ).map ((restrictScalars φ).map f) ((1 : R') ⊗ₜ[R, γ] m)) =
    (restrictScalars ψ).map ((extendScalars δ).map f) (eM.hom ((1 : R') ⊗ₜ[R, γ] m))
  exact ((congrArg (fun x => eN.hom x) hE).trans hN).trans
    (((congrArg (fun x => (restrictScalars ψ).map ((extendScalars δ).map f) x) hM).trans hF).symm)

/-- The natural isomorphism of localization and restriction functors.

For the specified localization square, restrictScalars φ followed by extendScalars γ is
naturally isomorphic to extendScalars δ followed by restrictScalars ψ. -/
def localizationScalarSquareNatIso
    (hR : letI : Algebra R R' := γ.toAlgebra; IsLocalization T R')
    (hA : letI : Algebra A A' := δ.toAlgebra; IsLocalization (T.map φ) A') :
    restrictScalars φ ⋙ extendScalars γ ≅ extendScalars δ ⋙ restrictScalars ψ :=
  NatIso.ofComponents (fun M => localizationScalarSquareIso R A R' A' φ γ δ ψ T h hR hA M)
    (fun f => localizationScalarSquareIso_hom_naturality R A R' A' φ γ δ ψ T h hR hA f)

end ModuleCat
