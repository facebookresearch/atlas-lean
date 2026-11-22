/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.LeftDecalageExtraDegeneracy
import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual original left-decalage path diagram at one fixed object

Take the literal pullback of the whole original first-vertex augmentation
along the prescribed original zero-degree vertex. This retains the entire
shifted diagram, its original right-block projection and that same fixed
object in every degree. Evaluation identifies the chosen whole pullback
with the actual scalar row pullback, keeping both original legs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open CategoryTheory.SimplicialObject.LeftDecalage

/-- The same fixed original zero-degree vertex as a whole constant-diagram map. -/
def point (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u}) ⟶
      (SimplicialObject.const SSet.{u}).obj (W.diagram _⦋0⦌) :=
  (SimplicialObject.const SSet.{u}).map (SSet.yonedaEquiv.symm x)

/-- The whole original path diagram with its first object fixed to the same prescribed x. -/
def diagram (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) : SimplicialObject SSet.{u} :=
  pullback (augmentation W.diagram) (point W x)

/-- Its original whole shifted-simplex leg retains the same first-vertex pullback. -/
def toDecalage (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagram W x ⟶ CategoryTheory.SimplicialObject.LeftDecalage.diagram W.diagram :=
  pullback.fst _ _

/-- Its original whole point leg retains the same prescribed zero-degree vertex. -/
def toPoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagram W x ⟶ (SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u}) :=
  pullback.snd _ _

/-- The whole original fixed-object path projection is the same right-block restriction. -/
def projection (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) : diagram W x ⟶ W.diagram :=
  toDecalage W x ≫ CategoryTheory.SimplicialObject.LeftDecalage.projection W.diagram

/-- The full original path diagram retains its exact original fixed-object equation. -/
theorem fixedObject (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    toDecalage W x ≫ augmentation W.diagram = toPoint W x ≫ point W x :=
  pullback.condition

/-- The same whole fixed-object pullback evaluated at each original row is its actual scalar pullback. -/
def rowIso (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (diagram W x).obj (op (SimplexCategory.mk n)) ≅
      pullback ((augmentation W.diagram).app (op (SimplexCategory.mk n)))
        (SSet.yonedaEquiv.symm x) :=
  ((IsPullback.of_hasPullback (augmentation W.diagram) (point W x)).map
    ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op (SimplexCategory.mk n)))).isoPullback

/-- The forward original row comparison keeps the entire shifted-simplex leg. -/
theorem rowIso_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (rowIso W x n).hom ≫ pullback.fst _ _ = (toDecalage W x).app (op (SimplexCategory.mk n)) :=
  ((IsPullback.of_hasPullback (augmentation W.diagram) (point W x)).map
    ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op (SimplexCategory.mk n)))).isoPullback_hom_fst

/-- The forward original row comparison keeps the entire same fixed-point leg. -/
theorem rowIso_snd (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (rowIso W x n).hom ≫ pullback.snd _ _ = (toPoint W x).app (op (SimplexCategory.mk n)) :=
  ((IsPullback.of_hasPullback (augmentation W.diagram) (point W x)).map
    ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op (SimplexCategory.mk n)))).isoPullback_hom_snd

end SimplicialSpace.LeftDecalageObject
