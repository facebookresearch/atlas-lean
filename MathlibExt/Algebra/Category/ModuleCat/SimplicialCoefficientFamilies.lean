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
# Native coefficient families on original simplicial module diagrams

The native tensor bifunctor, native whiskering functors and Moore
normalization form one functor from the original diagram to its coefficient
family. All actual diagram maps and coefficient maps remain the original
maps on these native models. A fixed original prism gives a
parameter-natural normalized chain homotopy.

Ring, diagram-carrier and coefficient universes are independent. There is
no flatness, projectivity or naturality certificate input, and no new
complex or tensor construction.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace ModuleCat.SimplicialCoefficientFamilies

variable (R : Type u) [CommRing R]

/-- Native tensor/whiskering/normalization, as a functor of original coefficient families. -/
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

/-- Every family object is the same original coefficient tensor before native normalization. -/
theorem obj_obj (X : SimplicialObject (ModuleCat.{v} R)) (M : ModuleCat.{t} R) :
    ((normalized R).obj X).obj M =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).obj
        (X ⋙ (ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M) := rfl

/-- Diagram arrows are exactly the original coefficient-first normalized arrows. -/
theorem map_app {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y)
    (M : ModuleCat.{t} R) :
    ((normalized R).map f).app M =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).map
        (Functor.whiskerRight f ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M)) := rfl

/-- Coefficient arrows are exactly the original tensor natural-transformation components. -/
theorem obj_map (X : SimplicialObject (ModuleCat.{v} R))
    {M N : ModuleCat.{t} R} (a : M ⟶ N) :
    ((normalized R).obj X).map a =
      (normalizedMooreComplex (ModuleCat.{max v t} R)).map
        (Functor.whiskerLeft X ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map a)) := rfl

/-- The fixed original prism produces a natural normalized homotopy of the actual coefficient maps. -/
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
