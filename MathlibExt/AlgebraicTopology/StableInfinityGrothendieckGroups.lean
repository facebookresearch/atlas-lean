/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The actual degree-zero Grothendieck group of a stable infinity category

Generators are the actual objects of the quasicategory. Relations identify
objects joined by an equivalence edge and impose [middle]=[source]+[cofiber]
on every actual cocartesian square with its zero corner. This group is
only degree zero. It does not define the higher or nonconnective K carrier.

Exact functors act by the actual object map and preserve these same
source-normalized relations. The comparison to the K spectrum and to
native ordinary ring/triangulated K0 is requested separately.

Reference: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4,
Introduction and Sections 7--9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open StableInfinityCategoryModels StableInfinityMappingSpaces StableInfinityFiniteDiagrams
open QuasicategoricalModels
open scoped Simplicial

universe u

/-- Integral generators are the actual object vertices. -/
abbrev ObjectCycles (C : StableInfinityCategory.{u}) := FreeAbelianGroup (C.toSSet _⦋0⦌)

/-- The source equivalence/cofiber relations, with every actual diagram retained. -/
def GrothendieckRelation (C : StableInfinityCategory.{u}) (r : ObjectCycles C) : Prop :=
  (∃ e : C.toSSet _⦋1⦌, IsEquivalenceEdge C.toSSet e ∧
    r = FreeAbelianGroup.of (C.toSSet.δ 1 e) - FreeAbelianGroup.of (C.toSSet.δ 0 e)) ∨
  ∃ d : indexNerve SquareCorner ⟶ C.toSSet, IsPushoutSquare d ∧
    IsZeroObject C.toSSet (cornerValue d .vertical) ∧
    r = FreeAbelianGroup.of (cornerValue d .horizontal) -
      FreeAbelianGroup.of (cornerValue d .origin) - FreeAbelianGroup.of (cornerValue d .final)

/-- The actual relation subgroup, not an abstract degree-zero invariant. -/
def relations (C : StableInfinityCategory.{u}) : AddSubgroup (ObjectCycles C) :=
  AddSubgroup.closure {r | GrothendieckRelation C r}

/-- The native quotient Grothendieck group. -/
abbrev GrothendieckGroup (C : StableInfinityCategory.{u}) := ObjectCycles C ⧸ relations C

/-- Its actual object class in the native quotient. -/
def objectClass (C : StableInfinityCategory.{u}) (x : C.toSSet _⦋0⦌) : GrothendieckGroup C :=
  QuotientAddGroup.mk (FreeAbelianGroup.of x)

/-- Exact functors map the original integral object generators. -/
def objectCycleMap {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) :
    ObjectCycles C →+ ObjectCycles D := FreeAbelianGroup.map (f.map.app (op ⦋0⦌))

/-- The original equivalence/cofiber relations are preserved by that same exact functor. -/
theorem objectCycleMap_relation {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D)
    (r : ObjectCycles C) (h : GrothendieckRelation C r) :
    GrothendieckRelation D (objectCycleMap f r) := by
  rcases h with ⟨e, he, rfl⟩ | ⟨d, hd, hz, rfl⟩
  · left
    refine ⟨f.map.app (op ⦋1⦌) e, IsEquivalenceEdge.map f.map he, ?_⟩
    simp [objectCycleMap, SSet.δ_naturality_apply]
  · right
    refine ⟨d ≫ f.map, f.exact.2 d hd, f.exact.1 (cornerValue d .vertical) hz, ?_⟩
    simp [objectCycleMap, cornerValue]

/-- Quotient descent is a property of the explicitly defined relation map. -/
theorem objectCycleMap_relations {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) :
    relations C ≤ (relations D).comap (objectCycleMap f) := by
  rw [relations, AddSubgroup.closure_le]
  intro r hr
  exact AddSubgroup.subset_closure (objectCycleMap_relation f r hr)

/-- The actual canonical group map induced by an exact functor. -/
def grothendieckMap {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) :
    GrothendieckGroup C →+ GrothendieckGroup D :=
  QuotientAddGroup.map (relations C) (relations D) (objectCycleMap f) (objectCycleMap_relations f)

end MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups
