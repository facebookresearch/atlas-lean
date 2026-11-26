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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorDifferential

/-!
# Naturality of the signed Hom–tensor comparison

For integer cochain complexes over a commutative ring, the Hom source `P` varies
contravariantly, while the Hom target `J` and tensor factor `U` vary covariantly. The Hom maps
act by source precomposition and target postcomposition; the tensor maps act on both factors.

For arbitrary maps `f : P' → P`, `g : J → J'`, and `h : U → U'`, these maps commute with the
signed comparison `Hom_R(P,J) ⊗_R U → Hom_R(P,J ⊗_R U)`. The square holds for full-product Hom
and direct-sum tensor totals.
-/

@[expose] public section
noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Uncurried cochain tensor bifunctor has the two-factor tensor map.

The map of the uncurried tensor bifunctor on a pair of cochain morphisms `(f, g)` equals
`mapAt R f g`. -/
theorem mapAt_uncurry
    {P P' Q Q' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (CategoryTheory.Functor.uncurry.obj
      (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ)).map
          (X := (P, Q)) (Y := (P', Q')) (f, g) = mapAt R f g := by
  dsimp only [CategoryTheory.Functor.uncurry, bifunctorAt,
    CategoryTheory.Functor.map₂HomologicalComplex]
  exact mapAt_precomp_postcomp R f g

/-- Uncurried linear Hom functor has precomposition and postcomposition maps.

The map of the uncurried linear Hom bifunctor on a morphism of `(Pᵒᵖ, J)` pairs is
`linearComplexMap R f.1.unop f.2`. -/
theorem linearFunctor_uncurry_map
    {X Y : (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ×
      CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y) :
    (CategoryTheory.Functor.uncurry.obj
      (linearFunctor R (ModuleCat.{v} R))).map f =
        linearComplexMap R f.1.unop f.2 := by
  change linearComplexMap R f.1.unop (𝟙 X.2) ≫
      linearComplexMap R (𝟙 Y.1.unop) f.2 = _
  rw [linearComplexMap_comp]
  simp only [Category.id_comp]

/-- Linear Hom map evaluates by precomposition and postcomposition.

For `f : P' ⟶ P`, `g : J ⟶ J'`, and `p + n = q`, the image of a degree-`n` cochain `z`
evaluates at `x : P'^p` as `(g.f q)(z_(p,q)((f.f p) x))`. -/
theorem linearComplexMap_v_apply
    {P P' J J' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : P' ⟶ P) (g : J ⟶ J') (n p q : ℤ) (hpq : p + n = q)
    (z : Cochain P J n) (x : P'.X p) :
    ((((linearComplexMap R f g).f n).hom z).v p q hpq).hom x =
      (g.f q).hom ((z.v p q hpq).hom ((f.f p).hom x)) := by
  change ((mapLinearOver R f g n z).v p q hpq).hom x = _
  simp only [mapLinearOver_v, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- Signed Hom–tensor comparison is natural in three cochain inputs.

The tensor map of `linearComplexMap R f g` and `h`, followed by the comparison at `(P', J',
U')`, equals the comparison at `(P, J, U)` followed by the linear Hom map of `f` and `mapAt R
g h`. -/
theorem homTensorComparison_naturality
    {P P' J J' U U' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : P' ⟶ P) (g : J ⟶ J') (h : U ⟶ U') :
    mapAt R (linearComplexMap R f g) h ≫ homTensorComparison R P' J' U' =
      homTensorComparison R P J U ≫ linearComplexMap R f (mapAt R g h) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z u
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((homTensorDegree R P' J' U' n).hom
      (((mapAt R (linearComplexMap R f g) h).f n).hom
        (mkAt R (linearComplex R P J) U a b n hab z u))).v p q hpq).hom x =
    ((((linearComplexMap R f (mapAt R g h)).f n).hom
      ((homTensorDegree R P J U n).hom
        (mkAt R (linearComplex R P J) U a b n hab z u))).v p q hpq).hom x
  rw [mapAt_mk,
    homTensorDegree_mk_v' R P' J' U' n a b hab
      (((linearComplexMap R f g).f a).hom z) ((h.f b).hom u)
        p (p + a) q rfl hpq x,
    linearComplexMap_v_apply, linearComplexMap_v_apply,
    homTensorDegree_mk_v' R P J U n a b hab z u
      p (p + a) q rfl hpq ((f.f p).hom x),
    map_zsmul_unit, mapAt_mk]

end CochainComplex.ModuleTensor
