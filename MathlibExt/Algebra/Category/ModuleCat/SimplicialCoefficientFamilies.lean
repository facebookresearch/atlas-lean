/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedPrismFamily
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Normalized tensor families of simplicial modules

For a commutative ring R, a simplicial R-module diagram X and a coefficient module M, form the
coefficient-first tensor diagram M ⊗_R X and its normalized Moore chain complex N(M ⊗_R X).
Varying X gives a functor to coefficient families, and varying M gives their coefficient maps.

A simplicial homotopy H between maps X → Y induces normalized chain homotopies for every M.
Their components are natural in coefficient maps: h_M(n,m) followed by the Y-coefficient map
equals the X-coefficient map followed by h_N(n,m). The ring, diagram-carrier and coefficient-
carrier universe levels are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace ModuleCat.SimplicialCoefficientFamilies

variable (R : Type u) [CommRing R]

/-- The family of normalized coefficient tensors.

Send a simplicial module X to the coefficient functor M ↦ N(M ⊗_R X), using the coefficient-
first tensor bifunctor and normalized Moore complex. -/
def normalized : SimplicialObject (ModuleCat.{v} R) ⥤
    (ModuleCat.{t} R ⥤ ChainComplex (ModuleCat.{max v t} R) ℕ) :=
  CategoryTheory.Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (ModuleCat.{v} R) (ModuleCat.{max v t} R) ⋙
    (CategoryTheory.Functor.whiskeringLeft (ModuleCat.{t} R)
      (ModuleCat.{v} R ⥤ ModuleCat.{max v t} R)
      (SimplicialObject (ModuleCat.{max v t} R))).obj
        (ModuleCat.tensorBifunctorAt.{u, t, v} R) ⋙
    (CategoryTheory.Functor.whiskeringRight (ModuleCat.{t} R)
      (SimplicialObject (ModuleCat.{max v t} R))
      (ChainComplex (ModuleCat.{max v t} R) ℕ)).obj
        (normalizedMooreComplex (ModuleCat.{max v t} R))

/-- The normalized family at a coefficient module.

The value at X and M is the normalized Moore complex of X followed by the functor M ⊗_R −. -/
theorem obj_obj (X : SimplicialObject (ModuleCat.{v} R)) (M : ModuleCat.{t} R) :
    ((normalized R).obj X).obj M =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).obj
        (X ⋙ (ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M) := rfl

/-- The normalized map of a simplicial diagram morphism.

For f : X → Y and fixed M, the family map is normalization of the simplicial map obtained by
tensoring f on the left with M. -/
theorem map_app {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y)
    (M : ModuleCat.{t} R) :
    ((normalized R).map f).app M =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).map
        (Functor.whiskerRight f ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M)) := rfl

/-- The normalized map of a coefficient morphism.

For a : M → N and fixed X, the coefficient-family map is normalization of the simplicial map a
⊗ id_X. -/
theorem obj_map (X : SimplicialObject (ModuleCat.{v} R))
    {M N : ModuleCat.{t} R} (a : M ⟶ N) :
    ((normalized R).obj X).map a =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).map
        (Functor.whiskerLeft X ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map a)) := rfl

/-- Coefficient naturality of normalized simplicial homotopies.

For a fixed simplicial homotopy H and a coefficient map a : M → N, its normalized components
satisfy h_M(n,m) ≫ N_Y(a)_m = N_X(a)_n ≫ h_N(n,m), for all n,m ∈ ℕ. -/
theorem homotopy_naturality {X Y : SimplicialObject (ModuleCat.{v} R)}
    {f g : X ⟶ Y} (H : SimplicialObject.Homotopy f g)
    {M N : ModuleCat.{t} R} (a : M ⟶ N) (n m : ℕ) :
    ((H.whiskerRight ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M)).toNormalizedChainHomotopy).hom n m ≫
        (((normalized R).obj Y).map a).f m =
      (((normalized R).obj X).map a).f n ≫
        ((H.whiskerRight ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj N)).toNormalizedChainHomotopy).hom n m :=
  SimplicialObject.Homotopy.normalizedFamilyHom_naturality
    (ModuleCat.tensorBifunctorAt.{u, t, v} R) H a n m

end ModuleCat.SimplicialCoefficientFamilies

end
