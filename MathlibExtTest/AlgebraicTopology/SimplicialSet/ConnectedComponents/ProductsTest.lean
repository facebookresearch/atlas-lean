/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents.Products

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

open CategoryTheory Limits Opposite SSet MonoidalCategory
open scoped Simplicial

namespace ConnectedComponentsProductsTest

-- Arbitrary ambient objects keep their original tensor vertices in both directions.
example {X Y : SSet.{u + 2}} (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    piZeroTensorEquiv X Y (π₀.mk (componentTensorSimplex (op ⦋0⦌) x y)) =
        (π₀.mk x, π₀.mk y) ∧
      (piZeroTensorEquiv X Y).symm (π₀.mk x, π₀.mk y) =
        π₀.mk (componentTensorSimplex (op ⦋0⦌) x y) := by
  constructor
  · rw [piZeroTensorEquiv_apply, mapπ₀_mk, mapπ₀_mk]
    rfl
  · exact piZeroTensorEquiv_symm_mk x y

-- The chosen product comparison keeps the same original pair of vertices.
example {X Y : SSet.{u + 2}} (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    piZeroProductEquiv X Y (π₀.mk (componentProductSimplex (op ⦋0⦌) x y)) =
        (π₀.mk x, π₀.mk y) ∧
      (piZeroProductEquiv X Y).symm (π₀.mk x, π₀.mk y) =
        π₀.mk (componentProductSimplex (op ⦋0⦌) x y) :=
  ⟨piZeroProductEquiv_mk x y, piZeroProductEquiv_symm_mk x y⟩

-- Every simplicial operator retains both original projected simplices.
example {X Y : SSet.{u + 2}} {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m)
    (x : X.obj n) (y : Y.obj n) :
    (prod.fst : X ⨯ Y ⟶ X).app m
        ((X ⨯ Y).map a (componentProductSimplex n x y)) = X.map a x ∧
      (prod.snd : X ⨯ Y ⟶ Y).app m
        ((X ⨯ Y).map a (componentProductSimplex n x y)) = Y.map a y := by
  constructor
  · rw [componentProductSimplex_map, componentProductSimplex_fst]
  · rw [componentProductSimplex_map, componentProductSimplex_snd]

example {X Y X' Y' : SSet.{u + 2}} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : π₀ (X ⨯ Y)) :
    piZeroProductEquiv X' Y' (mapπ₀ (prod.map f g) c) =
      (mapπ₀ f (piZeroProductEquiv X Y c).1, mapπ₀ g (piZeroProductEquiv X Y c).2) :=
  piZeroProductEquiv_natural f g c

-- Finite products and the actual comparison for every zero-factor family are available
-- from the neutral module, with no model-category scope.
example : PreservesFiniteProducts (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) := inferInstance

-- The neutral import exposes the monoidal instance and its invertible structure maps.
example : π₀Functor.{u + 2}.Monoidal := inferInstance

example (X Y : SSet.{u + 2}) :
    IsIso (Functor.OplaxMonoidal.δ π₀Functor.{u + 2} X Y) := inferInstance

example : IsIso (Functor.OplaxMonoidal.η π₀Functor.{u + 2}) := inferInstance

example : PreservesLimitsOfShape (Discrete (Fin 0))
    (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) := piZeroFunctor_preserves_zeroProduct

example (K : Fin 0 → SSet.{u + 2}) :
    IsIso (piComparison (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) K) := inferInstance

example (K : Fin 0 → SSet.{u + 2}) (c : π₀ (∏ᶜ K)) :
    inv (piComparison (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) K)
        (piComparison (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) K c) = c := by
  have h := IsIso.hom_inv_id (piComparison (π₀Functor : SSet.{u + 2} ⥤ Type (u + 2)) K)
  exact congrArg (fun f => f c) h

end ConnectedComponentsProductsTest
