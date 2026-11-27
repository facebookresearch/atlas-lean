/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# Simplicial connected components and realization path components

The canonical map `π₀(X) → π₀(|X|)` sends the class of a simplicial vertex to the
path component of its realized vertex. A simplicial edge gives a path with source
at interval parameter zero and target at parameter one; its simplicial faces are
`d₁` at the source and `d₀` at the target.

This vertex map descends to connected components and is natural in every
simplicial map. The target is the topological path-component type `ZerothHomotopy`.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/--
The map from simplicial connected components `π₀(X)` to the path components of
`|X|`, taking a vertex class to the path component of the realized vertex.
-/
noncomputable def piZeroToZerothHomotopy (X : SSet.{u}) :
    SSet.π₀ X → ZerothHomotopy ↑(SSet.toTop.obj X) :=
  SSet.π₀.lift (ZerothHomotopy.mk ∘ SSet.realizedVertex)
    (fun _ _ e => ZerothHomotopy.sound (TopCat.pathEquiv (SSet.realizedEdgePath e)))

/--
The canonical component map sends `π₀.mk x` to the path-component class of the
realized vertex `x`.
-/
@[simp]
theorem piZeroToZerothHomotopy_mk (X : SSet.{u}) (x : X _⦋0⦌) :
    piZeroToZerothHomotopy X (SSet.π₀.mk x) =
      ZerothHomotopy.mk (SSet.realizedVertex x) :=
  rfl

/--
For a simplicial map `f : X → Y`, the canonical component maps commute with
`π₀(f)` and the path-component map induced by `|f|`.
-/
theorem piZeroToZerothHomotopy_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    TopCat.zerothHomotopyMap (SSet.toTop.map f) ∘ piZeroToZerothHomotopy X =
      piZeroToZerothHomotopy Y ∘ SSet.mapπ₀ f := by
  funext x
  induction x
  simp [Function.comp_apply, piZeroToZerothHomotopy_mk, SSet.mapπ₀_mk,
    TopCat.zerothHomotopyMap_mk, SSet.realizedVertex_naturality]

end SSet

end
