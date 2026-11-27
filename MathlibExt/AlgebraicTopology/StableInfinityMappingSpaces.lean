/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.QuasicategoricalModels
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Native mapping spaces of an infinity category

The mapping space is the actual fibre of the core of the arrow functor
category over the two fixed endpoints. The core is taken on natural
transformations of arrows, retaining every arrow object and all its
higher homotopies. It does not restrict the arrows to equivalences.

The endpoint maps are native standard-simplex restrictions. Object
points are native constant zero-simplex maps. For a quasicategory the
endpoint map on these cores is a Kan fibration, so this fibre computes
the mapping space. The general construction theorem is a separate
source-support request.

References: Lurie, Higher Topos Theory, Sections 1.2.2 and 1.2.5;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2 and 7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels
open scoped Simplicial

universe u

/-- The native zero-simplex core, the fixed contractible comparison target. -/
abbrev Point : SSet.{u} := core Δ[0]

/-- The full core of the native arrow functor infinity category. -/
abbrev ArrowCore (C : SSet.{u}) : SSet.{u} := core (mapping Δ[1] C)

/-- The full core of object-valued zero-simplex diagrams. -/
abbrev ObjectCore (C : SSet.{u}) : SSet.{u} := core (mapping Δ[0] C)

/-- Restriction to endpoint one or zero is the native precomposition map. -/
def endpoint (C : SSet.{u}) (i : Fin 2) : ArrowCore C ⟶ ObjectCore C :=
  coreMap (precomposition (SSet.stdSimplex.δ i) C)

/-- The arrow core projects to its literal source and target diagrams. -/
def endpointPair (C : SSet.{u}) : ArrowCore C ⟶ prod (ObjectCore C) (ObjectCore C) :=
  prod.lift (endpoint C 1) (endpoint C 0)

/-- An object point uses the actual constant zero-simplex and native Hom comparison. -/
def objectPoint (C : SSet.{u}) (x : C _⦋0⦌) : Point ⟶ ObjectCore C :=
  coreMap (SSet.const (mappingZero Δ[0] C (SSet.const x)))

/-- The endpoint pair is fixed by the two actual objects. -/
def fixedEndpoints (C : SSet.{u}) (x y : C _⦋0⦌) :
    Point ⟶ prod (ObjectCore C) (ObjectCore C) :=
  prod.lift (objectPoint C x) (objectPoint C y)

/-- The actual mapping-space fibre, including noninvertible arrow objects. -/
def mappingSpace (C : SSet.{u}) (x y : C _⦋0⦌) : SSet.{u} :=
  pullback (endpointPair C) (fixedEndpoints C x y)

/-- The actual comparison of that mapping space with the fixed point core. -/
def mappingToPoint (C : SSet.{u}) (x y : C _⦋0⦌) : mappingSpace C x y ⟶ Point :=
  pullback.snd (endpointPair C) (fixedEndpoints C x y)

/-- Initiality is contractibility of all actual outgoing mapping spaces. -/
def IsInitialObject (C : SSet.{u}) (x : C _⦋0⦌) : Prop :=
  ∀ y : C _⦋0⦌, WeakEquivalence (mappingToPoint C x y)

/-- Terminality is contractibility of all actual incoming mapping spaces. -/
def IsTerminalObject (C : SSet.{u}) (x : C _⦋0⦌) : Prop :=
  ∀ y : C _⦋0⦌, WeakEquivalence (mappingToPoint C y x)

/-- A zero object has both native mapping-space universal properties. -/
def IsZeroObject (C : SSet.{u}) (x : C _⦋0⦌) : Prop :=
  IsInitialObject C x ∧ IsTerminalObject C x

end MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces
