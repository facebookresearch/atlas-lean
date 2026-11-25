/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Localization of modules preserves colimits

Mathlib's module-localization functor uses `Shrink` in order to remain in a
fixed universe, whereas extension of scalars is implemented by a tensor
product.  We identify these functors using the canonical equivalence

`S⁻¹M ≃ S⁻¹R ⊗[R] M`.

The naturality proof is reduced to the canonical maps out of `M` as follows.

1. The comparison sends the shrunk localization map to `m ↦ 1 ⊗ m`.
2. `localizedModuleFunctor.map f` extends `f` across the localization map.
3. `extendScalars.map f` sends `1 ⊗ m` to `1 ⊗ f m`.
4. The universal property of module localization makes these equations
   sufficient for naturality.

Since extension of scalars is a left adjoint, the natural isomorphism then
transfers preservation of arbitrary colimits to module localization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace ModuleCat

/-- The identity equivalence between the restriction-of-scalars carrier used
by `extendScalars` and the localized ring with its usual algebra-module
structure. -/
noncomputable def localizationRestrictScalarsLinearEquiv
    (S : Submonoid R) :
    ((restrictScalars (algebraMap R (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S)) : Type u) ≃ₗ[
          Localization S] Localization S :=
  LinearEquiv.refl (Localization S) (Localization S)

/-- The tensor carrier used by `extendScalars` at a localization is
canonically equivalent to the usual algebra tensor product. -/
noncomputable def extendScalarsLocalizationTensorEquiv
    (S : Submonoid R) (M : ModuleCat.{u} R) :
    ((extendScalars (algebraMap R (Localization S))).obj M : Type u) ≃ₗ[
      Localization S] (Localization S ⊗[R] M) := by
  let _ : IsScalarTower R (Localization S)
      ((restrictScalars (algebraMap R (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S))) :=
    IsScalarTower.restrictScalars R (Localization S) _
  dsimp only [extendScalars, ExtendScalars.obj']
  exact TensorProduct.AlgebraTensorModule.congr
    (localizationRestrictScalarsLinearEquiv S) (LinearEquiv.refl R M)

/-- The canonical linear equivalence from shrunk module localization to
extension of scalars. -/
noncomputable def localizedModuleLinearEquivExtendScalars
    (S : Submonoid R) (M : ModuleCat.{u} R) :
    M.localizedModule S ≃ₗ[Localization S]
      ((extendScalars (algebraMap R (Localization S))).obj M : Type u) :=
  (Shrink.linearEquiv (Localization S) (LocalizedModule S M)).trans
    ((LocalizedModule.equivTensorProduct S M).trans
      (extendScalarsLocalizationTensorEquiv S M).symm)

/-- The canonical comparison from the shrunk localization of a module to
extension of scalars to the localized ring. -/
noncomputable def localizedModuleIsoExtendScalarsApp
    (S : Submonoid R) (M : ModuleCat.{u} R) :
    (localizedModuleFunctor.{u} S).obj M ≅
      (extendScalars.{u, u, u}
        (algebraMap R (Localization S))).obj M :=
  (localizedModuleLinearEquivExtendScalars S M).toModuleIso

/-- On the canonical localization map, the comparison with extension of
scalars is `m ↦ 1 ⊗ m`. -/
@[simp]
theorem localizedModuleIsoExtendScalarsApp_hom_mk_apply
    (S : Submonoid R) (M : ModuleCat.{u} R) (m : M) :
    (localizedModuleIsoExtendScalarsApp S M).hom
        (M.localizedModuleMkLinearMap S m) =
      (1 : Localization S) ⊗ₜ[R, algebraMap R (Localization S)] m := by
  unfold localizedModuleIsoExtendScalarsApp
  let _ : IsScalarTower R (Localization S)
      ((restrictScalars (algebraMap R (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S))) :=
    IsScalarTower.restrictScalars R (Localization S) _
  change (extendScalarsLocalizationTensorEquiv S M).symm
    (LocalizedModule.equivTensorProduct S M
      (Shrink.linearEquiv (Localization S) (LocalizedModule S M)
        ((Shrink.linearEquiv R (LocalizedModule S M)).symm
          (LocalizedModule.mk m 1)))) = _
  rw [show Shrink.linearEquiv (Localization S) (LocalizedModule S M)
      ((Shrink.linearEquiv R (LocalizedModule S M)).symm
        (LocalizedModule.mk m 1)) = LocalizedModule.mk m 1 by
    exact (equivShrink (LocalizedModule S M)).symm_apply_apply _]
  rw [LocalizedModule.equivTensorProduct_apply_mk]
  change (TensorProduct.AlgebraTensorModule.congr
      (localizationRestrictScalarsLinearEquiv S)
      (LinearEquiv.refl R M)).symm
      (Localization.mk 1 1 ⊗ₜ[R] m) = _
  change (TensorProduct.AlgebraTensorModule.congr
      (localizationRestrictScalarsLinearEquiv S).symm
      (LinearEquiv.refl R M).symm)
      (Localization.mk 1 1 ⊗ₜ[R] m) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul]
  rw [← Localization.mk_one]
  rw [show (localizationRestrictScalarsLinearEquiv S).symm
      (Localization.mk 1 1) = Localization.mk 1 1 by rfl]
  rw [show (LinearEquiv.refl R M).symm m = m by rfl]
  rfl

/-- Naturality of the canonical localization/extension-of-scalars
comparison. -/
theorem localizedModuleIsoExtendScalarsApp_hom_naturality
    (S : Submonoid R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (localizedModuleFunctor.{u} S).map f ≫
        (localizedModuleIsoExtendScalarsApp S N).hom =
      (localizedModuleIsoExtendScalarsApp S M).hom ≫
        (extendScalars.{u, u, u}
          (algebraMap R (Localization S))).map f := by
  apply ModuleCat.hom_ext
  apply (IsLocalizedModule.isBaseChange S (Localization S)
    (M.localizedModuleMkLinearMap S)).algHom_ext
  intro m
  change (localizedModuleIsoExtendScalarsApp S N).hom
      ((localizedModuleFunctor.{u} S).map f
        (M.localizedModuleMkLinearMap S m)) =
    (extendScalars.{u, u, u}
      (algebraMap R (Localization S))).map f
      ((localizedModuleIsoExtendScalarsApp S M).hom
        (M.localizedModuleMkLinearMap S m))
  rw [show (localizedModuleFunctor.{u} S).map f
        (M.localizedModuleMkLinearMap S m) =
      N.localizedModuleMkLinearMap S (f m) by
        change IsLocalizedModule.mapExtendScalars S
            (M.localizedModuleMkLinearMap S)
            (N.localizedModuleMkLinearMap S)
            (Localization S) f.hom
            (M.localizedModuleMkLinearMap S m) = _
        simp [IsLocalizedModule.mapExtendScalars]]
  rw [localizedModuleIsoExtendScalarsApp_hom_mk_apply]
  rw [localizedModuleIsoExtendScalarsApp_hom_mk_apply]
  exact ExtendScalars.map_tmul
    (algebraMap R (Localization S)) f 1 m

/-- Localization of modules is naturally isomorphic to extension of scalars
to the localized ring. -/
noncomputable def localizedModuleFunctorIsoExtendScalars
    (S : Submonoid R) :
    localizedModuleFunctor.{u} S ≅
      extendScalars.{u, u, u}
        (algebraMap R (Localization S)) :=
  NatIso.ofComponents
    (localizedModuleIsoExtendScalarsApp S)
    (fun f ↦ localizedModuleIsoExtendScalarsApp_hom_naturality S f)

/-- Localization of modules preserves all colimits. -/
noncomputable instance localizedModuleFunctor_preservesColimits
    (S : Submonoid R) :
    PreservesColimits (localizedModuleFunctor.{u} S) :=
  preservesColimits_of_natIso
    (localizedModuleFunctorIsoExtendScalars S).symm


section PrimeLocalExtension

universe v w

/-- The actual extension-of-scalars carrier is the ordinary tensor product
with the ring-map scalar action, with independent ring and module universes. -/
def extendedCarrierTensorEquiv
    (R : Type u) (Q : Type v) [CommRing R] [CommRing Q]
    (f : R →+* Q) (M : ModuleCat.{w} R) :
    letI : Algebra R Q := f.toAlgebra
    (extendScalars f).obj M ≃ₗ[Q] Q ⊗[R] M := by
  let : Algebra R Q := f.toAlgebra
  let N : ModuleCat.{v} R := (restrictScalars f).obj (ModuleCat.of Q Q)
  let : IsScalarTower R Q N := IsScalarTower.restrictScalars R Q (ModuleCat.of Q Q)
  exact TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q) (LinearEquiv.refl R M)

/-- The actual scalar-extension tensor carrier equivalence preserves each
original tensor value. -/
theorem extendedCarrierTensorEquiv_tmul
    (R : Type u) (Q : Type v) [CommRing R] [CommRing Q]
    (f : R →+* Q) (M : ModuleCat.{w} R) (q : Q) (m : M) :
    letI : Algebra R Q := f.toAlgebra
    extendedCarrierTensorEquiv R Q f M (q ⊗ₜ[R, f] m) = q ⊗ₜ[R] m := by
  let : Algebra R Q := f.toAlgebra
  change TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q)
      (LinearEquiv.refl R M) (q ⊗ₜ[R, f] m) = q ⊗ₜ[R] m
  rfl

/-- Localizing actual extension of scalars agrees with extension along the
induced local ring homomorphism. The rings and coefficient module have
independent universes. -/
def localizedExtensionLinearEquiv
    (R : Type u) (Q : Type v) [CommRing R] [CommRing Q] (f : R →+* Q)
    (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) :
    let r := q.asIdeal.comap f
    let Rr := Localization.AtPrime r
    let Qq := Localization.AtPrime q.asIdeal
    let fl := Localization.localRingHom r q.asIdeal f rfl
    LocalizedModule q.asIdeal.primeCompl ((extendScalars f).obj M) ≃ₗ[Qq]
      (extendScalars fl).obj (ModuleCat.of Rr (LocalizedModule r.primeCompl M)) := by
  let r := q.asIdeal.comap f
  let Rr := Localization.AtPrime r
  let Qq := Localization.AtPrime q.asIdeal
  let fl : Rr →+* Qq := Localization.localRingHom r q.asIdeal f rfl
  algebraize [f, fl]
  let : IsScalarTower R Rr Qq :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map r q.asIdeal f rfl x).symm
  let eQ := (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl ((extendScalars f).obj
    M)).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq)
      (extendedCarrierTensorEquiv R Q f M))
  let eR := (LocalizedModule.equivTensorProduct r.primeCompl M)
  let eL := eQ.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Qq Qq M)
  let eT := (extendedCarrierTensorEquiv Rr Qq fl (ModuleCat.of Rr (LocalizedModule
    r.primeCompl M))).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq) eR).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rr Qq Qq M))
  exact eL.trans eT.symm

/-- The prime-local extension comparison sends the original localized
unit tensor to the same unit tensor of the localized coefficient. -/
theorem localizedExtensionLinearEquiv_mk_one_tmul
    (R : Type u) (Q : Type v) [CommRing R] [CommRing Q] (f : R →+* Q)
    (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) (m : M) :
    localizedExtensionLinearEquiv R Q f q M
      (LocalizedModule.mk ((1 : Q) ⊗ₜ[R, f] m) (1 : q.asIdeal.primeCompl)) =
      (1 : Localization.AtPrime q.asIdeal) ⊗ₜ[
        Localization.AtPrime (q.asIdeal.comap f),
        Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl]
        (LocalizedModule.mk m (1 : (q.asIdeal.comap f).primeCompl)) := by
  let r := q.asIdeal.comap f
  let Rr := Localization.AtPrime r
  let Qq := Localization.AtPrime q.asIdeal
  let fl : Rr →+* Qq := Localization.localRingHom r q.asIdeal f rfl
  algebraize [f, fl]
  let : IsScalarTower R Rr Qq :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map r q.asIdeal f rfl x).symm
  let eQ := (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl ((extendScalars f).obj
    M)).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq)
      (extendedCarrierTensorEquiv R Q f M))
  let eR := LocalizedModule.equivTensorProduct r.primeCompl M
  let eL := eQ.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Qq Qq M)
  let eT := (extendedCarrierTensorEquiv Rr Qq fl (ModuleCat.of Rr (LocalizedModule
    r.primeCompl M))).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq) eR).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rr Qq Qq M))
  change eT.symm (eL (LocalizedModule.mk ((1 : Q) ⊗ₜ[R, f] m) (1 : q.asIdeal.primeCompl))) = _
  apply eT.injective
  rw [LinearEquiv.apply_symm_apply]
  have hL : eL (LocalizedModule.mk ((1 : Q) ⊗ₜ[R, f] m) (1 : q.asIdeal.primeCompl)) =
      (1 : Qq) ⊗ₜ[R] m := by
    have hloc := LocalizedModule.equivTensorProduct_apply_mk (M :=
      (extendScalars f).obj M) q.asIdeal.primeCompl
      ((1 : Q) ⊗ₜ[R, f] m) (1 : q.asIdeal.primeCompl)
    have hcarrier := extendedCarrierTensorEquiv_tmul R Q f M 1 m
    dsimp only [eL, eQ, LinearEquiv.trans_apply]
    have hcongr := TensorProduct.AlgebraTensorModule.congr_tmul
      (LinearEquiv.refl Qq Qq) (extendedCarrierTensorEquiv R Q f M)
      (Localization.mk 1 (1 : q.asIdeal.primeCompl)) ((1 : Q) ⊗ₜ[R, f] m)
    have hvalue := hcongr.trans (congrArg
      (fun z => (Localization.mk 1 (1 : q.asIdeal.primeCompl) : Qq) ⊗ₜ[Q] z) hcarrier)
    have hcancel := TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R Q Qq (M :=
      Qq) (N := M)
      (Localization.mk 1 (1 : q.asIdeal.primeCompl) : Qq) m (1 : Q)
    exact (congrArg (fun z => TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Qq Qq M
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq)
        (extendedCarrierTensorEquiv R Q f M) z)) hloc).trans
      ((congrArg (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Qq Qq M) hvalue).trans
        (hcancel.trans (by simp only [one_smul, Localization.mk_one])))
  have hT : eT ((1 : Qq) ⊗ₜ[Rr, fl] (LocalizedModule.mk m (1 : r.primeCompl))) =
      (1 : Qq) ⊗ₜ[R] m := by
    have hcarrier := extendedCarrierTensorEquiv_tmul Rr Qq fl
      (ModuleCat.of Rr (LocalizedModule r.primeCompl M)) 1 (LocalizedModule.mk m (1 : r.primeCompl))
    have hloc := LocalizedModule.equivTensorProduct_apply_mk (M :=
      M) r.primeCompl m (1 : r.primeCompl)
    dsimp only [eT, LinearEquiv.trans_apply]
    have hcongr := TensorProduct.AlgebraTensorModule.congr_tmul
      (LinearEquiv.refl Qq Qq) eR (1 : Qq) (LocalizedModule.mk m (1 : r.primeCompl))
    have hvalue := hcongr.trans (congrArg (fun z => (1 : Qq) ⊗ₜ[Rr] z) hloc)
    have hcancel := TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R Rr Qq (M :=
      Qq) (N := M)
      (1 : Qq) m (Localization.mk 1 (1 : r.primeCompl) : Rr)
    exact (congrArg (fun z => TensorProduct.AlgebraTensorModule.cancelBaseChange R Rr Qq Qq M
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qq Qq) eR z)) hcarrier).trans
      ((congrArg (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rr Qq Qq M) hvalue).trans
        (hcancel.trans (by simp only [Localization.mk_one, one_smul])))
  exact hL.trans hT.symm

/-- Flat base change at corresponding primes multiplies original module
length by the actual closed fiber length, including infinite module lengths. -/
theorem localizedExtension_length_baseChange
    (R : Type u) (Q : Type v) [CommRing R] [CommRing Q] (f : R →+* Q) (hf : f.Flat)
    (q : PrimeSpectrum Q) (M : ModuleCat.{w} R) :
    let r := q.asIdeal.comap f
    let Rr := Localization.AtPrime r
    let Qq := Localization.AtPrime q.asIdeal
    let fl := Localization.localRingHom r q.asIdeal f rfl
    Module.length Qq (LocalizedModule q.asIdeal.primeCompl ((extendScalars f).obj M)) =
      Module.length Rr (LocalizedModule r.primeCompl M) *
        Module.length Qq (Qq ⧸ (IsLocalRing.maximalIdeal Rr).map fl) := by
  let r := q.asIdeal.comap f
  let Rr := Localization.AtPrime r
  let Qq := Localization.AtPrime q.asIdeal
  let fl : Rr →+* Qq := Localization.localRingHom r q.asIdeal f rfl
  let : Algebra Rr Qq := fl.toAlgebra
  let : IsLocalHom (algebraMap Rr Qq) := Localization.isLocalHom_localRingHom r q.asIdeal f rfl
  let : Module.Flat Rr Qq := (RingHom.flat_algebraMap_iff).mp
    (hf.localRingHom q.asIdeal r rfl)
  let N := ModuleCat.of Rr (LocalizedModule r.primeCompl M)
  have hLocal := (localizedExtensionLinearEquiv R Q f q M).length_eq
  have hTensor := (extendedCarrierTensorEquiv Rr Qq fl N).length_eq
  exact hLocal.trans (hTensor.trans (IsLocalRing.length_baseChange Rr Qq N))

end PrimeLocalExtension

end ModuleCat

end
