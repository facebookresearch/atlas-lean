/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Localization

/-!
# Localization when all denominators already act invertibly

If every element of a submonoid acts bijectively on a module, the identity
map already satisfies the localized-module universal property.  Comparing it
with Mathlib's canonical (universe-shrunk) localized module gives a canonical
linear equivalence, and hence an isomorphism after forgetting to additive
commutative groups.

This file adds no localization construction.  It packages the consequence of
`IsLocalizedModule.linearEquiv` needed by localization arguments whose target
module already inverts every denominator.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v u

namespace IsLocalizedModule

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- If every denominator acts bijectively on `M`, the identity of `M`
exhibits `M` as its own localization. -/
theorem idOfBijectiveSmul
    (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x)) :
    IsLocalizedModule S (.id : M →ₗ[R] M) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun x : M => (s : R) • x)
    exact h s
  surj y := ⟨(y, 1), by simp⟩
  exists_of_eq hxy := ⟨1, by simpa using hxy⟩

end IsLocalizedModule

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The canonical localized module is linearly equivalent to the original
module when every denominator already acts bijectively. -/
noncomputable def localizedModuleLinearEquivOfBijectiveSmul
    (S : Submonoid R) (M : ModuleCat.{v} R)
    (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x)) :
    M.localizedModule S ≃ₗ[R] M := by
  let _ : IsLocalizedModule S (.id : M →ₗ[R] M) :=
    IsLocalizedModule.idOfBijectiveSmul S h
  exact IsLocalizedModule.linearEquiv S
    (M.localizedModuleMkLinearMap S) LinearMap.id

/-- The comparison extends the canonical localization map by the identity. -/
@[simp]
theorem localizedModuleLinearEquivOfBijectiveSmul_apply_mk
    (S : Submonoid R) (M : ModuleCat.{v} R)
    (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x))
    (x : M) :
    localizedModuleLinearEquivOfBijectiveSmul S M h
        (M.localizedModuleMkLinearMap S x) = x := by
  let _ : IsLocalizedModule S (.id : M →ₗ[R] M) :=
    IsLocalizedModule.idOfBijectiveSmul S h
  exact IsLocalizedModule.linearEquiv_apply S
    (M.localizedModuleMkLinearMap S) LinearMap.id x

/-- After forgetting scalars, localization is isomorphic to the original
additive commutative group whenever all denominators already act
bijectively. -/
noncomputable def localizedModuleAddCommGrpIsoOfBijectiveSmul
    (S : Submonoid R) (M : ModuleCat.{v} R)
    (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x)) :
    (forget₂ (ModuleCat.{v} (Localization S)) AddCommGrpCat.{v}).obj
        ((localizedModuleFunctor S).obj M) ≅
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj M :=
  (localizedModuleLinearEquivOfBijectiveSmul S M h).toAddEquiv.toAddCommGrpIso

/-- The underlying additive-group comparison sends the canonical localized
image of `x` back to `x`. -/
@[simp]
theorem localizedModuleAddCommGrpIsoOfBijectiveSmul_hom_mk
    (S : Submonoid R) (M : ModuleCat.{v} R)
    (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x))
    (x : M) :
    (localizedModuleAddCommGrpIsoOfBijectiveSmul S M h).hom
        (M.localizedModuleMkLinearMap S x) = x :=
  localizedModuleLinearEquivOfBijectiveSmul_apply_mk S M h x

end ModuleCat

end
