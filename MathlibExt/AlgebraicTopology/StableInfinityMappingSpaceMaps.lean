/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps

/-!
# Native maps on full infinity-categorical mapping-space fibres

These are literal pullback maps of the full arrow-core endpoint fibre,
induced by native enriched postcomposition. They retain noninvertible
arrow objects and every parameter simplex. Full faithfulness is tested
on these same maps; it is not an independent object equivalence.

Reference: Lurie, Higher Topos Theory, Section 1.2.2;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Section 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinitySFunctorMaps
open scoped Simplicial

universe u

/-- The actual map of complete object-diagram cores. -/
def objectCoreMap {C D : SSet.{u}} (f : C ⟶ D) :
    ObjectCore C ⟶ ObjectCore D := coreMap (postcomposition Δ[0] f)

/-- The actual map of complete arrow-diagram cores. -/
def arrowCoreMap {C D : SSet.{u}} (f : C ⟶ D) :
    ArrowCore C ⟶ ArrowCore D := coreMap (postcomposition Δ[1] f)

/-- Both original endpoints commute with the native full arrow map. -/
theorem endpoint_naturality {C D : SSet.{u}} (f : C ⟶ D) (i : Fin 2) :
    arrowCoreMap f ≫ endpoint D i = endpoint C i ≫ objectCoreMap f := by
  dsimp only [arrowCoreMap, endpoint, objectCoreMap]
  rw [← coreMap_comp, ← coreMap_comp]
  congr 1

/-- The native chosen-object diagram commutes with actual postcomposition. -/
theorem objectPoint_naturality {C D : SSet.{u}} (f : C ⟶ D)
    (x : C _⦋0⦌) :
    objectPoint C x ≫ objectCoreMap f =
      objectPoint D (f.app (op ⦋0⦌) x) := by
  dsimp only [objectPoint, objectCoreMap]
  rw [← coreMap_comp]
  congr 1
  rw [SSet.const_comp, mappingZero_postcomposition, SSet.const_comp]

/-- Both original endpoints commute with the native full arrow map. -/
theorem endpointPair_naturality {C D : SSet.{u}} (f : C ⟶ D) :
    arrowCoreMap f ≫ endpointPair D =
      endpointPair C ≫ prod.map (objectCoreMap f) (objectCoreMap f) := by
  apply prod.hom_ext
  · simpa only [endpointPair, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using endpoint_naturality f 1
  · simpa only [endpointPair, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using endpoint_naturality f 0

/-- The specified endpoint pair is the image of those same source vertices. -/
theorem fixedEndpoints_naturality {C D : SSet.{u}} (f : C ⟶ D)
    (x y : C _⦋0⦌) :
    fixedEndpoints C x y ≫ prod.map (objectCoreMap f) (objectCoreMap f) =
      fixedEndpoints D (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  apply prod.hom_ext
  · simpa only [fixedEndpoints, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using objectPoint_naturality f x
  · simpa only [fixedEndpoints, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using objectPoint_naturality f y

/-- The actual map on the full endpoint-fixed mapping-space fibre. -/
def mappingSpaceMap {C D : SSet.{u}} (f : C ⟶ D)
    (x y : C _⦋0⦌) : mappingSpace C x y ⟶
      mappingSpace D (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  pullback.map (endpointPair C) (fixedEndpoints C x y)
    (endpointPair D)
    (fixedEndpoints D (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
    (arrowCoreMap f) (𝟙 Point)
    (prod.map (objectCoreMap f) (objectCoreMap f))
    (endpointPair_naturality f).symm
    (by simpa using fixedEndpoints_naturality f x y)

/-- Full faithfulness tests every actual mapping-space comparison. -/
def IsFullyFaithful {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  ∀ x y : C _⦋0⦌, WeakEquivalence (mappingSpaceMap f x y)

/-- A whole natural equivalence is an equivalence edge in the full functor category. -/
def NaturallyEquivalentMaps {X Y : SSet.{u}} (f g : X ⟶ Y) : Prop :=
  ∃ e : (mapping X Y) _⦋1⦌, IsEquivalenceEdge (mapping X Y) e ∧
    (mapping X Y).δ 1 e = mappingZero X Y f ∧
    (mapping X Y).δ 0 e = mappingZero X Y g

end MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps
