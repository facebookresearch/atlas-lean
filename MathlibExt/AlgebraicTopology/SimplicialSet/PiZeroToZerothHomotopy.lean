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
# Simplicial `π₀` to realized path components

For `X : SSet`, the canonical map from simplicial connected components `SSet.π₀ X`
to topological path components `ZerothHomotopy ↑(SSet.toTop.obj X)`, sending a vertex
to its realized vertex. Edge coherence uses `SSet.realizedEdgePath` with `δ 1` source
(`0 : TopCat.I`) / `δ 0` target (`1 : TopCat.I`) orientation, transported across
`TopCat.pathEquiv` and quotiented by `ZerothHomotopy.sound`.

Nonclaims: no surjectivity, no injectivity, no `π₀ K ≃ K₀`, no additivity, no spectrum claim.
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
