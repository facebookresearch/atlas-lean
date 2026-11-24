/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The canonical module localization unit

Bundle Mathlib's actual localization map into a natural transformation from
the identity on modules to localization followed by restriction of scalars.
The ring and module carrier universes are independent, with the standard
`Small` assumption used by the shrunk localized-module functor.

The component formula identifies the underlying function with the canonical
localization map. Naturality retains the actual localized morphism. No
localization carrier, scalar law or invertibility witness is supplied.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped ChangeOfRings

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A] [Small.{v} A] (T : Submonoid A)

/-- The canonical localization maps form a natural transformation into
restriction of scalars of the actual localized modules. -/
@[expose]
def localizedModuleFunctorUnit :
    𝟭 (ModuleCat.{v} A) ⟶
      localizedModuleFunctor T ⋙ restrictScalars (algebraMap A (Localization T)) where
  app M := by
    change M ⟶ RestrictScalars.obj'
      (algebraMap A (Localization T)) (M.localizedModule T)
    let addMap := (M.localizedModuleMkLinearMap T).toAddHom
    have scalarLaw (a : A) (x : M) :
        addMap (a • x) = (algebraMap A (Localization T) a) • addMap x := by
      change M.localizedModuleMkLinearMap T (a • x) =
        (algebraMap A (Localization T) a) • M.localizedModuleMkLinearMap T x
      rw [(M.localizedModuleMkLinearMap T).map_smul, IsScalarTower.algebraMap_smul]
    letI : Module A (M.localizedModule T) :=
      Module.compHom (M.localizedModule T) (algebraMap A (Localization T))
    exact ModuleCat.ofHom
      { toFun := addMap
        map_add' := addMap.map_add
        map_smul' := scalarLaw }
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change N.localizedModuleMkLinearMap T (f x) =
      localizedModuleMap T f (M.localizedModuleMkLinearMap T x)
    change N.localizedModuleMkLinearMap T (f x) =
      IsLocalizedModule.mapExtendScalars T (M.localizedModuleMkLinearMap T)
        (N.localizedModuleMkLinearMap T) (Localization T) f.hom
        (M.localizedModuleMkLinearMap T x)
    simp [IsLocalizedModule.mapExtendScalars]

/-- Every component has exactly the canonical localization function on the
existing shrunk localized-module carrier. -/
@[simp]
theorem localizedModuleFunctorUnit_app_apply (M : ModuleCat.{v} A) (x : M) :
    Hom.hom (A := M)
        (B := (restrictScalars (algebraMap A (Localization T))).obj
          ((localizedModuleFunctor T).obj M))
        ((localizedModuleFunctorUnit T).app M) x = M.localizedModuleMkLinearMap T x := rfl

/-- The canonical localization maps commute with every actual module map
and its localized morphism, after restriction of scalars. -/
@[reassoc]
theorem localizedModuleFunctorUnit_naturality {M N : ModuleCat.{v} A} (f : M ⟶ N) :
    f ≫ (localizedModuleFunctorUnit T).app N =
      (localizedModuleFunctorUnit T).app M ≫
        (restrictScalars (algebraMap A (Localization T))).map
          ((localizedModuleFunctor T).map f) :=
  (localizedModuleFunctorUnit T).naturality f

end ModuleCat

end
