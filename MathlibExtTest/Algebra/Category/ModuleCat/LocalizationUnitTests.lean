/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnit

public section

noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u v

namespace ModuleCatLocalizationUnitTests

variable {A : Type u} [CommRing A] [Small.{v} A] (T : Submonoid A)
  {M N P : ModuleCat.{v} A}

/-- Public inference preserves the independent ring and module universes. -/
example :
    𝟭 (ModuleCat.{v} A) ⟶ ModuleCat.localizedModuleFunctor T ⋙
      ModuleCat.restrictScalars (algebraMap A (Localization T)) :=
  ModuleCat.localizedModuleFunctorUnit T

theorem canonical_component (x : M) :
    (ModuleCat.localizedModuleFunctorUnit T).app M x = M.localizedModuleMkLinearMap T x := by
  exact ModuleCat.localizedModuleFunctorUnit_app_apply T M x

/-- The A-linear component has the prescribed B-module scalar action. -/
theorem restriction_scalar (a : A) (x : M) :
    ModuleCat.Hom.hom (A := M)
        (B := (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
          ((ModuleCat.localizedModuleFunctor T).obj M))
        ((ModuleCat.localizedModuleFunctorUnit T).app M) (a • x) =
      (algebraMap A (Localization T) a) •
        ModuleCat.Hom.hom (A := M)
          (B := (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
            ((ModuleCat.localizedModuleFunctor T).obj M))
          ((ModuleCat.localizedModuleFunctorUnit T).app M) x := by
  let h := ModuleCat.Hom.hom (A := M)
    (B := (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
      ((ModuleCat.localizedModuleFunctor T).obj M))
    ((ModuleCat.localizedModuleFunctorUnit T).app M)
  change h (a • x) = (algebraMap A (Localization T) a) • h x
  rw [h.map_smul]
  exact ModuleCat.restrictScalars.smul_def (algebraMap A (Localization T)) a (h x)

theorem actual_naturality (f : M ⟶ N) :
    f ≫ (ModuleCat.localizedModuleFunctorUnit T).app N =
      (ModuleCat.localizedModuleFunctorUnit T).app M ≫
        (ModuleCat.restrictScalars (algebraMap A (Localization T))).map
          ((ModuleCat.localizedModuleFunctor T).map f) := by
  exact ModuleCat.localizedModuleFunctorUnit_naturality T f

/-- The generated reassociated characteristic rewrites a larger square. -/
theorem naturality_followed_by (f : M ⟶ N)
    (g : (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
      ((ModuleCat.localizedModuleFunctor T).obj N) ⟶ P) :
    f ≫ (ModuleCat.localizedModuleFunctorUnit T).app N ≫ g =
      (ModuleCat.localizedModuleFunctorUnit T).app M ≫
        (ModuleCat.restrictScalars (algebraMap A (Localization T))).map
          ((ModuleCat.localizedModuleFunctor T).map f) ≫ g := by
  exact ModuleCat.localizedModuleFunctorUnit_naturality_assoc T f g

end ModuleCatLocalizationUnitTests
