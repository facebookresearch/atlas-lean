/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Finite restriction of scalars on `FGModuleCat`

For `f : R →+* S`, `f` is of finite restriction when `S` as an `R`-module via
`f` is finitely generated. Then restriction of scalars of a finite `S`-module
is finite over `R`, giving `FGModuleCat S ⥤ FGModuleCat R`.
-/

@[expose] public section

open CategoryTheory

universe v uR uS uT

namespace RingHom

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- `f : R →+* S` is of finite restriction when `S` as an `R`-module via `f.toModule`
is finitely generated. -/
def IsFinite (f : R →+* S) : Prop :=
  @Module.Finite R S _ _ f.toModule

/-- The identity ring homomorphism `R →+* R` is finite, since `R` regarded as a module
over itself via `RingHom.id` is finitely generated. -/
theorem isFinite_id : IsFinite (RingHom.id R) :=
  Module.Finite.self R

/-- Composition preserves finiteness: if `f : R →+* S` is finite and `g : S →+* T` is finite,
then `g.comp f : R →+* T` is finite. The scalar tower `R → S → T` makes `T` finite over `R`
via transitivity of finite modules. -/
theorem isFinite_comp {f : R →+* S} {g : S →+* T}
    (hf : f.IsFinite) (hg : g.IsFinite) : IsFinite (g.comp f) := by
  unfold IsFinite at *
  let : Module R S := f.toModule
  let : Module S T := g.toModule
  let : Module R T := (g.comp f).toModule
  have : Module.Finite R S := hf
  have : Module.Finite S T := hg
  have : IsScalarTower R S T := by
    constructor
    intro r s t
    change g (f r * s) * t = (g.comp f) r * (g s * t)
    rw [RingHom.comp_apply, map_mul, mul_assoc]
  exact Module.Finite.trans S T

end RingHom

namespace FGModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- If `f : R →+* S` is finite, a finite `S`-module `M` is finite as an `R`-module via `f`.
The `R`-action is `Module.compHom M f` and finiteness follows from the tower `R → S → M`
and `Module.Finite.trans`. -/
lemma finite_of_finite (f : R →+* S) (hf : f.IsFinite)
    (M : Type v) [AddCommGroup M] [Module S M] [Module.Finite S M] :
    @Module.Finite R M _ _ (Module.compHom M f) := by
  let : Module R S := f.toModule
  let : Module R M := Module.compHom M f
  have : Module.Finite R S := hf
  have : IsScalarTower R S M := by
    constructor
    intro r s m
    change (f r * s) • m = f r • s • m
    exact (mul_smul (f r) s m)
  exact Module.Finite.trans S M

/-- Restriction along a finite `f : R →+* S` preserves finite generation:
`ModuleCat.restrictScalars.{v} f` sends finite `S`-modules to finite `R`-modules
via `finite_of_finite`. -/
lemma isFG_restrictScalars (f : R →+* S) (hf : f.IsFinite)
    {M : ModuleCat.{v} S} (hM : Module.Finite S M) :
    Module.Finite R ((ModuleCat.restrictScalars.{v} f).obj M) := by
  let : Module.Finite S M := hM
  exact finite_of_finite f hf M

/-- Restriction of scalars for finitely generated modules along a finite ring homomorphism
`f : R →+* S`. On objects it sends a finite `S`-module `M` to the `R`-module obtained by
`Module.compHom M f`; finiteness over `R` follows from `S` being finite over `R` and
`M` finite over `S` via `Module.Finite.trans`. -/
noncomputable def restrictScalars (f : R →+* S) (hf : f.IsFinite) :
    FGModuleCat.{v} S ⥤ FGModuleCat.{v} R :=
  (ModuleCat.isFG (R := R)).lift
    (forget₂ (FGModuleCat.{v} S) (ModuleCat.{v} S) ⋙ ModuleCat.restrictScalars.{v} f)
    (fun X => isFG_restrictScalars f hf X.property)

/-- The underlying `ModuleCat` object of `restrictScalars.{v} f hf` is definitionally
`ModuleCat.restrictScalars.{v} f` applied to the underlying object. -/
@[simp]
lemma restrictScalars_obj_obj (f : R →+* S) (hf : f.IsFinite)
    (X : FGModuleCat.{v} S) :
    ((restrictScalars.{v} f hf).obj X).obj =
      (ModuleCat.restrictScalars.{v} f).obj X.obj :=
  rfl

/-- The underlying `ModuleCat` morphism of `restrictScalars.{v} f hf` is definitionally
`ModuleCat.restrictScalars.{v} f` applied to the underlying morphism. -/
@[simp]
lemma restrictScalars_map_hom (f : R →+* S) (hf : f.IsFinite)
    {X Y : FGModuleCat.{v} S} (g : X ⟶ Y) :
    ((restrictScalars.{v} f hf).map g).hom =
      (ModuleCat.restrictScalars.{v} f).map g.hom :=
  rfl

/-- Comparison isomorphism: restricting along `f : R →+* S` on `FGModuleCat` and then
forgetting to `ModuleCat R` is naturally isomorphic to forgetting from `FGModuleCat S`
to `ModuleCat S` and then restricting on `ModuleCat`. -/
noncomputable def restrictScalarsCompForget₂Iso (f : R →+* S) (hf : f.IsFinite) :
    restrictScalars.{v} f hf ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ≅
      forget₂ (FGModuleCat.{v} S) (ModuleCat.{v} S) ⋙ ModuleCat.restrictScalars.{v} f :=
  (ModuleCat.isFG (R := R)).liftCompιIso
    (forget₂ (FGModuleCat.{v} S) (ModuleCat.{v} S) ⋙ ModuleCat.restrictScalars.{v} f)
    (fun X => isFG_restrictScalars f hf X.property)

/-- Restriction of scalars along a finite homomorphism is additive: it preserves addition
of morphisms because the underlying `ModuleCat.restrictScalars.{v}` is additive. -/
instance (f : R →+* S) (hf : f.IsFinite) :
    (restrictScalars.{v} f hf).Additive where
  map_add := by
    intro X Y g₁ g₂
    have hg : (g₁ + g₂).hom = g₁.hom + g₂.hom := rfl
    have hm : ((restrictScalars.{v} f hf).map g₁ + (restrictScalars.{v} f hf).map g₂).hom =
        ((restrictScalars.{v} f hf).map g₁).hom + ((restrictScalars.{v} f hf).map g₂).hom := rfl
    apply ObjectProperty.hom_ext
    simp only [hg, hm, restrictScalars_map_hom]
    exact (inferInstance : (ModuleCat.restrictScalars.{v} f).Additive).map_add

/-- Finite restriction is faithful because its original underlying module functions are
unchanged. -/
instance restrictScalars_faithful (f : R →+* S) (hf : f.IsFinite) :
    (restrictScalars.{v} f hf).Faithful where
  map_injective := by
    intro X Y g h hgh
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun k => k.hom.hom x) hgh

end FGModuleCat
