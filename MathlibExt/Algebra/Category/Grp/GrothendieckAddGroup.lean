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

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Grothendieck group completion

For `M : AddCommMonoid`, `GrothendieckAddGroup M` is its group completion. The
cross-universe universal property is `liftAddEquiv : (M →+ G) ≃+ (GrothendieckAddGroup M →+ G)`
with generator laws `lift_comp_of` / `lift_of`. It yields the biadditive lift `lift₂` with
`lift₂_of_of`, the induced maps `map` with `map_of`, `hom_ext`, `map_id`, `map_comp`, and the
bundled functor `AddCommMonCat.grothendieckAddGroup : AddCommMonCat ⥤ AddCommGrpCat` with its
object, hom, and generator simp lemmas.
-/

@[expose] public section

open CategoryTheory Algebra

universe u v w

namespace Algebra.GrothendieckAddGroup

/-- Composition/generator law for `GrothendieckAddGroup.lift`. -/
@[simp]
theorem lift_comp_of {M : Type u} {G : Type v} [AddCommMonoid M] [AddCommGroup G]
    (f : M →+ G) :
    (GrothendieckAddGroup.lift f).comp GrothendieckAddGroup.of = f :=
  Equiv.symm_apply_apply (GrothendieckAddGroup.lift (M := M) (G := G)) f

/-- Pointwise generator law for `GrothendieckAddGroup.lift`. -/
theorem lift_of {M : Type u} {G : Type v} [AddCommMonoid M] [AddCommGroup G]
    (f : M →+ G) (x : M) :
    GrothendieckAddGroup.lift f (GrothendieckAddGroup.of x) = f x :=
  DFunLike.congr_fun (lift_comp_of f) x

/-- Generator simplification in the normal form of the localization inclusion.
The named `lift_of` rule remains available for explicit generator rewrites. -/
@[simp]
theorem lift_addMonoidOf {M : Type u} {G : Type v}
    [AddCommMonoid M] [AddCommGroup G] (f : M →+ G) (x : M) :
    GrothendieckAddGroup.lift f ((AddLocalization.addMonoidOf ⊤) x) = f x :=
  lift_of f x

/-- Additive equivalence refining `GrothendieckAddGroup.lift`. -/
noncomputable def liftAddEquiv {M : Type u} {G : Type v}
    [AddCommMonoid M] [AddCommGroup G] :
    (M →+ G) ≃+ (GrothendieckAddGroup M →+ G) where
  toFun := GrothendieckAddGroup.lift
  invFun g := g.comp GrothendieckAddGroup.of
  left_inv f := lift_comp_of f
  right_inv g := GrothendieckAddGroup.lift.apply_symm_apply g
  map_add' f g := by
    have h : (GrothendieckAddGroup.lift f + GrothendieckAddGroup.lift g).comp
        GrothendieckAddGroup.of = f + g := by
      ext x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, lift_of]
    calc
      GrothendieckAddGroup.lift (f + g) =
          GrothendieckAddGroup.lift
            ((GrothendieckAddGroup.lift f + GrothendieckAddGroup.lift g).comp
              GrothendieckAddGroup.of) := by rw [h]
      _ = GrothendieckAddGroup.lift f + GrothendieckAddGroup.lift g :=
        GrothendieckAddGroup.lift.apply_symm_apply _

@[simp]
theorem liftAddEquiv_apply {M : Type u} {G : Type v}
    [AddCommMonoid M] [AddCommGroup G] (f : M →+ G) :
    liftAddEquiv f = GrothendieckAddGroup.lift f :=
  rfl

@[simp]
theorem liftAddEquiv_symm_apply {M : Type u} {G : Type v}
    [AddCommMonoid M] [AddCommGroup G] (g : GrothendieckAddGroup M →+ G) :
    liftAddEquiv.symm g = g.comp GrothendieckAddGroup.of :=
  rfl

/-- Reusable biadditive lift constructed from `liftAddEquiv` in each variable.
Preserves noncommutative argument order. -/
noncomputable def lift₂ {M : Type u} {N : Type v} {G : Type w}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommGroup G]
    (f : M →+ N →+ G) :
    GrothendieckAddGroup M →+ GrothendieckAddGroup N →+ G :=
  liftAddEquiv ((liftAddEquiv (M := N) (G := G)).toAddMonoidHom.comp f)

/-- Generator law for the biadditive lift. -/
@[simp]
theorem lift₂_of_of {M : Type u} {N : Type v} {G : Type w}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommGroup G]
    (f : M →+ N →+ G) (x : M) (y : N) :
    lift₂ f (GrothendieckAddGroup.of x) (GrothendieckAddGroup.of y) = f x y := by
  simp only [lift₂, liftAddEquiv_apply, lift_of, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]

/-- The general induced additive homomorphism on Grothendieck group completions,
defined from the universal property. Cross-universe in the source and target monoids. -/
noncomputable def map {M : Type u} {N : Type v} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) : GrothendieckAddGroup M →+ GrothendieckAddGroup N :=
  GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp f)

/-- Generator formula for the induced map, via `lift_of`. -/
theorem map_of {M : Type u} {N : Type v} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (x : M) :
    map f (GrothendieckAddGroup.of x) = GrothendieckAddGroup.of (f x) :=
  lift_of (GrothendieckAddGroup.of.comp f) x

/-- Induced-map simplification on the normal-form localization inclusion.
The named `map_of` rule keeps its original explicit-rewrite interface. -/
@[simp]
theorem map_addMonoidOf {M : Type u} {N : Type v}
    [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) (x : M) :
    map f ((AddLocalization.addMonoidOf ⊤) x) = (AddLocalization.addMonoidOf ⊤) (f x) :=
  map_of f x

/-- Extensionality for additive homomorphisms out of `GrothendieckAddGroup M`
via agreement after composition with `of`, derived from `liftAddEquiv`. -/
@[ext]
theorem hom_ext {M : Type u} {G : Type v} [AddCommMonoid M] [AddCommGroup G]
    (f g : GrothendieckAddGroup M →+ G)
    (h : f.comp GrothendieckAddGroup.of = g.comp GrothendieckAddGroup.of) : f = g :=
  liftAddEquiv.symm.injective h

/-- The induced map respects identity. -/
theorem map_id {M : Type u} [AddCommMonoid M] :
    map (AddMonoidHom.id M) = AddMonoidHom.id (GrothendieckAddGroup M) := by
  apply hom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, map_of, AddMonoidHom.id_apply]

/-- The induced map respects composition, cross-universe in all three monoids. -/
theorem map_comp {M : Type u} {N : Type v} {P : Type w}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    (f : M →+ N) (g : N →+ P) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, map_of]

end Algebra.GrothendieckAddGroup

namespace AddCommMonCat

/-- Group completion functor `AddCommMonCat ⥤ AddCommGrpCat` via the reusable
`Algebra.GrothendieckAddGroup.map` API. -/
noncomputable def grothendieckAddGroup : AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (GrothendieckAddGroup M)
  map f := AddCommGrpCat.ofHom (Algebra.GrothendieckAddGroup.map f.hom)
  map_id := by
    intro M
    ext : 1
    exact Algebra.GrothendieckAddGroup.map_id
  map_comp := by
    intro M N P f g
    ext : 1
    exact Algebra.GrothendieckAddGroup.map_comp f.hom g.hom

@[simp]
theorem grothendieckAddGroup_obj_coe (M : AddCommMonCat.{u}) :
    (grothendieckAddGroup.obj M : Type u) = GrothendieckAddGroup M :=
  rfl

@[simp]
theorem grothendieckAddGroup_map_hom {M N : AddCommMonCat.{u}} (f : M ⟶ N) :
    (grothendieckAddGroup.map f).hom =
      Algebra.GrothendieckAddGroup.map f.hom :=
  rfl

/-- The functor acts on the canonical generator `of x` by `of (f x)`. -/
@[simp]
theorem grothendieckAddGroup_map_of {M N : AddCommMonCat.{u}} (f : M ⟶ N) (x : M) :
    (grothendieckAddGroup.map f) (GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of (f.hom x) :=
  Algebra.GrothendieckAddGroup.map_of f.hom x

end AddCommMonCat
