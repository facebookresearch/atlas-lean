/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Tensor products of modules in independent universes

The linear tensor product defines a bifunctor whose coefficient universes are independent of each
other and of the ring universe. Curried and uncurried maps act on the two tensor factors, and each
partial functor is additive.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v w

variable (R : Type u) [CommRing R]

/-- For a commutative ring `R` in universe `u`, an `R`-module `M` with
carrier in `v` and an `R`-module `N` with carrier in `w`, their tensor
product over `R` is an object of `ModuleCat` in carrier universe `max(v,w)`. -/
abbrev tensorObjAt (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) : ModuleCat.{max v w} R :=
  ModuleCat.of R (M ⊗[R] N)

/-- For a commutative ring `R`, maps `f : M → M′` between modules in
carrier universe `v` and `g : N → N′` between modules in `w` induce the
linear tensor map `M ⊗_R N → M′ ⊗_R N′`, sending `m ⊗ n` to
`f(m) ⊗ g(n)`. The two carrier universes and ring universe are independent. -/
def tensorHomAt {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{w} R}
    (f : M ⟶ M') (g : N ⟶ N') : tensorObjAt R M N ⟶ tensorObjAt R M' N' :=
  ModuleCat.ofHom (TensorProduct.map f.hom g.hom)

/-- For linear maps `f : M → M′` and `g : N → N′` over a commutative ring
`R`, the independently sized tensor map sends the pure tensor `m ⊗ n`
to `f(m) ⊗ g(n)`. -/
@[simp]
theorem tensorHomAt_tmul {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{w} R}
    (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (tensorHomAt R f g).hom (m ⊗ₜ[R] n) = f.hom m ⊗ₜ[R] g.hom n :=
  TensorProduct.map_tmul _ _ _ _

/-- For modules `M`, `N` over a commutative ring `R` in independent
carrier universes `v`, `w`, the tensor map of their two identities is
the identity of `M ⊗_R N` in universe `max(v,w)`. -/
@[simp]
theorem tensorHomAt_id (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    tensorHomAt R (𝟙 M) (𝟙 N) = 𝟙 (tensorObjAt R M N) := by
  apply ModuleCat.hom_ext
  change TensorProduct.map (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) =
    LinearMap.id
  exact TensorProduct.map_id

/-- For a commutative ring `R` in universe `u`, tensor product defines a
curried bifunctor `ModuleCat_v(R) → ModuleCat_w(R) → ModuleCat_max(v,w)(R)`.
Its object value is `M ⊗_R N`; its maps apply the given linear map to
the relevant tensor factor. All three universes retain their given values. -/
def tensorBifunctorAt :
    ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj M :=
    { obj := tensorObjAt R M
      map g := tensorHomAt R (𝟙 M) g
      map_id N := by
        exact tensorHomAt_id R M N
      map_comp f g := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m n
        change TensorProduct.map LinearMap.id (g.hom.comp f.hom) (m ⊗ₜ[R] n) =
          TensorProduct.map LinearMap.id g.hom
            (TensorProduct.map LinearMap.id f.hom (m ⊗ₜ[R] n))
        simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply] }
  map f :=
    { app N := tensorHomAt R f (𝟙 N)
      naturality N N' g := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m n
        change TensorProduct.map f.hom LinearMap.id
            (TensorProduct.map LinearMap.id g.hom (m ⊗ₜ[R] n)) =
          TensorProduct.map LinearMap.id g.hom
            (TensorProduct.map f.hom LinearMap.id (m ⊗ₜ[R] n))
        simp only [TensorProduct.map_tmul, LinearMap.id_apply] }
  map_id M := by
    apply NatTrans.ext
    funext N
    change tensorHomAt R (𝟙 M) (𝟙 N) = 𝟙 (tensorObjAt R M N)
    exact tensorHomAt_id R M N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    change TensorProduct.map (g.hom.comp f.hom) LinearMap.id (m ⊗ₜ[R] n) =
      TensorProduct.map g.hom LinearMap.id
        (TensorProduct.map f.hom LinearMap.id (m ⊗ₜ[R] n))
    simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]

/-- For the independently sized tensor bifunctor over a commutative ring
`R`, a morphism `(f,g)` in the product of the two module categories is
sent by the uncurried bifunctor to the simultaneous tensor map
`f ⊗ g : M ⊗_R N → M′ ⊗_R N′`. -/
theorem tensorBifunctorAt_uncurry_map
    {X Y : ModuleCat.{v} R × ModuleCat.{w} R} (f : X ⟶ Y) :
    (CategoryTheory.Functor.uncurry.obj (tensorBifunctorAt R : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤
        ModuleCat.{max v w} R)).map f = tensorHomAt R f.1 f.2 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  change TensorProduct.map LinearMap.id f.2.hom
      (TensorProduct.map f.1.hom LinearMap.id (m ⊗ₜ[R] n)) =
    TensorProduct.map f.1.hom f.2.hom (m ⊗ₜ[R] n)
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

/-- For a commutative ring `R`, the curried tensor bifunctor with carrier
universes `v`, `w` preserves addition of first-variable linear maps:
`(f+g) ⊗ id = f ⊗ id + g ⊗ id`, as natural transformations in the
second variable. Its target carrier universe is `max(v,w)`. -/
instance tensorBifunctorAt_additive :
    (tensorBifunctorAt R : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R).Additive where
  map_add {M M' f g} := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    change TensorProduct.map (f.hom + g.hom) LinearMap.id (m ⊗ₜ[R] n) =
      TensorProduct.map f.hom LinearMap.id (m ⊗ₜ[R] n) +
        TensorProduct.map g.hom LinearMap.id (m ⊗ₜ[R] n)
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
      TensorProduct.add_tmul]

/-- For a commutative ring `R` and a fixed module `M` with carrier in `v`,
tensoring by `M` preserves addition of linear maps between modules in `w`:
`id ⊗ (f+g) = id ⊗ f + id ⊗ g`. The tensor-product carrier universe is `max(v,w)`. -/
instance tensorBifunctorAt_obj_additive (M : ModuleCat.{v} R) :
    ((tensorBifunctorAt R : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R).obj M).Additive where
  map_add {N N' f g} := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    change TensorProduct.map LinearMap.id (f.hom + g.hom) (m ⊗ₜ[R] n) =
      TensorProduct.map LinearMap.id f.hom (m ⊗ₜ[R] n) +
        TensorProduct.map LinearMap.id g.hom (m ⊗ₜ[R] n)
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
      TensorProduct.tmul_add]

section NativeMonoidal

open scoped MonoidalCategory

/-- For a commutative ring `R` in universe `u`, when both coefficient
carrier universes are `u`, the independently sized tensor bifunctor is
naturally isomorphic to the monoidal category's curried tensor functor.
The components are identities on the same tensor-product modules. -/
def tensorBifunctorAtNativeIso :
    (tensorBifunctorAt R : ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R) ≅
      CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (fun N => Iso.refl _)
    (by
      intro N N' g
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m n
      rfl)) (by
    intro M M' f
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    rfl)

end NativeMonoidal

end ModuleCat
