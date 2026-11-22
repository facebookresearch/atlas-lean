/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# Simplicial components and realized path components

`piZeroToZerothHomotopy` sends the simplicial connected component of a
vertex to the path component of its realized vertex.
A realized edge supplies the path needed to descend to `SSet.π₀`, with
`δ 1` as its source and `δ 0` as its target.
`piZeroToZerothHomotopy_naturality` shows that this map commutes with every
simplicial map and its topological realization.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Canonical map from simplicial `π₀` to realized path components. -/
noncomputable def piZeroToZerothHomotopy (X : SSet.{u}) :
    SSet.π₀ X → ZerothHomotopy ↑(SSet.toTop.obj X) :=
  SSet.π₀.lift (ZerothHomotopy.mk ∘ SSet.realizedVertex)
    (fun _ _ e => ZerothHomotopy.sound (TopCat.pathEquiv (SSet.realizedEdgePath e)))

/-- Representative law: the canonical map sends the class of a vertex `x` to the path
    component of its realized vertex, with the fixed `δ 1`-source/`δ 0`-target orientation. -/
@[simp]
theorem piZeroToZerothHomotopy_mk (X : SSet.{u}) (x : X _⦋0⦌) :
    piZeroToZerothHomotopy X (SSet.π₀.mk x) =
      ZerothHomotopy.mk (SSet.realizedVertex x) :=
  rfl

/-- Naturality: the canonical map commutes with a simplicial map `f`, sending
    representatives via `SSet.realizedVertex_naturality` with the same orientation. -/
theorem piZeroToZerothHomotopy_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    TopCat.zerothHomotopyMap (SSet.toTop.map f) ∘ piZeroToZerothHomotopy X =
      piZeroToZerothHomotopy Y ∘ SSet.mapπ₀ f := by
  funext x
  induction x
  simp [Function.comp_apply, piZeroToZerothHomotopy_mk, SSet.mapπ₀_mk,
    TopCat.zerothHomotopyMap_mk, SSet.realizedVertex_naturality]

end SSet

end
