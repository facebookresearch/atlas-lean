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

public import MathlibExt.Algebra.Category.ModuleCat.Prod.Idempotent
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# `e` and `f` component functors for `ModuleCat (R × S)`

For the central idempotents `e = (1,0)` and `f = (0,1)` in `R × S`, this module
bundles the `e`- and `f`-components of an `(R × S)`-module as objects of
`ModuleCat R` and `ModuleCat S`, and as additive functors
`ModuleCat (R × S) ⥤ ModuleCat R` and `ModuleCat (R × S) ⥤ ModuleCat S`.

The underlying `(R × S)`-linear decomposition is in `ProdIdempotent`; this file
is the `ModuleCat` wrapper with `simp` API for objects and morphisms.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

namespace ProdIdempotent

variable {R : Type uR} [Ring R] {S : Type uS} [Ring S]

/-- `e`-component of an `(R × S)`-module bundled as an `R`-module object. -/
def eSubmoduleAsModuleCat (M : ModuleCat.{v} (R × S)) : ModuleCat.{v} R :=
  ModuleCat.of R (ProdIdempotent.eSubmodule (R := R) (S := S) (M := M))

/-- `f`-component of an `(R × S)`-module bundled as an `S`-module object. -/
def fSubmoduleAsModuleCat (M : ModuleCat.{v} (R × S)) : ModuleCat.{v} S :=
  ModuleCat.of S (ProdIdempotent.fSubmodule (R := R) (S := S) (M := M))

/-- Underlying type of `eSubmoduleAsModuleCat` is `eSubmodule`. -/
@[simp]
lemma eSubmoduleAsModuleCat_coe (M : ModuleCat.{v} (R × S)) :
    (eSubmoduleAsModuleCat (R := R) (S := S) M : Type v) =
      ProdIdempotent.eSubmodule (R := R) (S := S) (M := M) :=
  rfl

/-- Underlying type of `fSubmoduleAsModuleCat` is `fSubmodule`. -/
@[simp]
lemma fSubmoduleAsModuleCat_coe (M : ModuleCat.{v} (R × S)) :
    (fSubmoduleAsModuleCat (R := R) (S := S) M : Type v) =
      ProdIdempotent.fSubmodule (R := R) (S := S) (M := M) :=
  rfl

section Functor

variable {M N O : Type*} [AddCommGroup M] [Module (R × S) M]
  [AddCommGroup N] [Module (R × S) N]
  [AddCommGroup O] [Module (R × S) O]

/-- Mapping `LinearMap.id` through `e`-components is `id`. -/
@[simp]
lemma map_eSubmodule_R_id :
    ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (M := M)
      (LinearMap.id : M →ₗ[R × S] M) = LinearMap.id := by
  ext x : 1
  exact Subtype.ext rfl

/-- Mapping `LinearMap.id` through `f`-components is `id`. -/
@[simp]
lemma map_fSubmodule_S_id :
    ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (M := M)
      (LinearMap.id : M →ₗ[R × S] M) = LinearMap.id := by
  ext x : 1
  exact Subtype.ext rfl

/-- Mapping respects composition on `e`-components. -/
lemma map_eSubmodule_R_comp (f : M →ₗ[R × S] N) (g : N →ₗ[R × S] O) :
    ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (g.comp f) =
      (ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g).comp
        (ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f) := by
  ext x : 1
  exact Subtype.ext rfl

/-- Mapping respects composition on `f`-components. -/
lemma map_fSubmodule_S_comp (f : M →ₗ[R × S] N) (g : N →ₗ[R × S] O) :
    ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (g.comp f) =
      (ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g).comp
        (ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f) := by
  ext x : 1
  exact Subtype.ext rfl

/-- Mapping respects addition on `e`-components. -/
@[simp]
lemma map_eSubmodule_R_add (f g : M →ₗ[R × S] N) :
    ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (f + g) =
      ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f +
        ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g := by
  ext x : 1
  simp only [ProdIdempotent.map_eSubmodule_R, LinearMap.add_apply]
  rfl

/-- Mapping respects addition on `f`-components. -/
@[simp]
lemma map_fSubmodule_S_add (f g : M →ₗ[R × S] N) :
    ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (f + g) =
      ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f +
        ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g := by
  ext x : 1
  simp only [ProdIdempotent.map_fSubmodule_S, LinearMap.add_apply]
  rfl

/-- Mapping sends `0` to `0` on `e`-components. -/
@[simp]
lemma map_eSubmodule_R_zero :
    ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (M := M) (N := N)
      (0 : M →ₗ[R × S] N) = 0 := by
  ext x : 1
  simp only [ProdIdempotent.map_eSubmodule_R, LinearMap.zero_apply]
  rfl

/-- Mapping sends `0` to `0` on `f`-components. -/
@[simp]
lemma map_fSubmodule_S_zero :
    ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (M := M) (N := N)
      (0 : M →ₗ[R × S] N) = 0 := by
  ext x : 1
  simp only [ProdIdempotent.map_fSubmodule_S, LinearMap.zero_apply]
  rfl

end Functor

/-- Functor `ModuleCat (R × S) ⥤ ModuleCat R` extracting the `e = (1,0)` component. -/
def eComponentFunctor : ModuleCat.{v} (R × S) ⥤ ModuleCat.{v} R where
  obj M := eSubmoduleAsModuleCat (R := R) (S := S) M
  map {X Y} f :=
    ModuleCat.ofHom
      (ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_eSubmodule_R (R := R) (S := S)
        (ModuleCat.Hom.hom (𝟙 X)) = LinearMap.id
    have h : ModuleCat.Hom.hom (𝟙 X) = LinearMap.id := rfl
    rw [h]
    simp
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_eSubmodule_R (R := R) (S := S)
        (ModuleCat.Hom.hom (f ≫ g)) =
          (ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g.hom).comp
            (ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom)
    have hfg : ModuleCat.Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl
    rw [hfg]
    exact (map_eSubmodule_R_comp (R := R) (S := S) f.hom g.hom).symm

/-- Functor `ModuleCat (R × S) ⥤ ModuleCat S` extracting the `f = (0,1)` component. -/
def fComponentFunctor : ModuleCat.{v} (R × S) ⥤ ModuleCat.{v} S where
  obj M := fSubmoduleAsModuleCat (R := R) (S := S) M
  map {X Y} f :=
    ModuleCat.ofHom
      (ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_fSubmodule_S (R := R) (S := S)
        (ModuleCat.Hom.hom (𝟙 X)) = LinearMap.id
    have h : ModuleCat.Hom.hom (𝟙 X) = LinearMap.id := rfl
    rw [h]
    simp
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_fSubmodule_S (R := R) (S := S)
        (ModuleCat.Hom.hom (f ≫ g)) =
          (ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g.hom).comp
            (ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom)
    have hfg : ModuleCat.Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl
    rw [hfg]
    exact (map_fSubmodule_S_comp (R := R) (S := S) f.hom g.hom).symm

/-- Object map of `eComponentFunctor` is `eSubmoduleAsModuleCat`. -/
@[simp]
lemma eComponentFunctor_obj (M : ModuleCat.{v} (R × S)) :
    (eComponentFunctor (R := R) (S := S)).obj M =
      eSubmoduleAsModuleCat M :=
  rfl

/-- Object map of `fComponentFunctor` is `fSubmoduleAsModuleCat`. -/
@[simp]
lemma fComponentFunctor_obj (M : ModuleCat.{v} (R × S)) :
    (fComponentFunctor (R := R) (S := S)).obj M =
      fSubmoduleAsModuleCat M :=
  rfl

/-- Underlying type of `eComponentFunctor.obj M` is `eSubmodule`. -/
@[simp]
lemma eComponentFunctor_obj_coe (M : ModuleCat.{v} (R × S)) :
    ((eComponentFunctor (R := R) (S := S)).obj M : Type v) =
      ProdIdempotent.eSubmodule (R := R) (S := S) (M := M) :=
  rfl

/-- Underlying type of `fComponentFunctor.obj M` is `fSubmodule`. -/
@[simp]
lemma fComponentFunctor_obj_coe (M : ModuleCat.{v} (R × S)) :
    ((fComponentFunctor (R := R) (S := S)).obj M : Type v) =
      ProdIdempotent.fSubmodule (R := R) (S := S) (M := M) :=
  rfl

/-- Hom map of `eComponentFunctor` is `map_eSubmodule_R`. -/
@[simp]
lemma eComponentFunctor_map_hom {X Y : ModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((eComponentFunctor (R := R) (S := S)).map f).hom =
      ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom :=
  rfl

/-- Hom map of `fComponentFunctor` is `map_fSubmodule_S`. -/
@[simp]
lemma fComponentFunctor_map_hom {X Y : ModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((fComponentFunctor (R := R) (S := S)).map f).hom =
      ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom :=
  rfl

/-- The `e`-component functor is additive. -/
instance eComponentFunctor_additive :
    (eComponentFunctor (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_eSubmodule_R (R := R) (S := S)
        (ModuleCat.Hom.hom (f + g)) =
          ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom +
            ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g.hom
    have h : ModuleCat.Hom.hom (f + g) = f.hom + g.hom := rfl
    rw [h]
    simp

/-- The `f`-component functor is additive. -/
instance fComponentFunctor_additive :
    (fComponentFunctor (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    change ProdIdempotent.map_fSubmodule_S (R := R) (S := S)
        (ModuleCat.Hom.hom (f + g)) =
          ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom +
            ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g.hom
    have h : ModuleCat.Hom.hom (f + g) = f.hom + g.hom := rfl
    rw [h]
    simp

end ProdIdempotent
