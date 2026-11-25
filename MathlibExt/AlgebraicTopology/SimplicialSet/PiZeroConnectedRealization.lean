/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjective
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.Topology.Connected.PathConnected

/-!
# Path-connected realization of a connected simplicial set

For `X : SSet`, simplicial connectedness (`X.IsConnected`) implies the geometric
realization `|X|` is path-connected (`PathConnectedSpace`). The simplicial
hypothesis supplies the `Subsingleton` half via `SSet.π₀`, transported along the
surjective canonical map `SSet.piZeroToZerothHomotopy` by the exact library lemma
`Function.Surjective.subsingleton`; realization nonemptiness from a realized vertex
supplies the `Nonempty` half; `pathConnectedSpace_iff_zerothHomotopy` closes the goal.

This is path connectedness only, not contractibility. It does not establish
injectivity or an equivalence of the canonical map, additivity, any K-space
construction, or `pi-zero K = K0`.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Realization of a simplicially connected simplicial set is path-connected. -/
theorem pathConnectedSpace_realization_of_isConnected (X : SSet.{u}) [X.IsConnected] :
    PathConnectedSpace ↑(SSet.toTop.obj X) := by
  have hConn : X.IsConnected := inferInstance
  have hNeVertex : Nonempty (X _⦋0⦌) := SSet.IsConnected.nonempty
  have hSubPiZero : Subsingleton (SSet.π₀ X) := inferInstance
  have hSurj : Function.Surjective (SSet.piZeroToZerothHomotopy X) :=
    SSet.piZeroToZerothHomotopy_surjective X
  have hSubZeroH : Subsingleton (ZerothHomotopy ↑(SSet.toTop.obj X)) := by
    have := hSubPiZero
    exact Function.Surjective.subsingleton hSurj
  have hNeReal : Nonempty ↑(SSet.toTop.obj X) :=
    ⟨SSet.realizedVertex (Classical.choice hNeVertex)⟩
  have hZNe : Nonempty (ZerothHomotopy ↑(SSet.toTop.obj X)) :=
    Nonempty.map ZerothHomotopy.mk hNeReal
  have hZSub : Subsingleton (ZerothHomotopy ↑(SSet.toTop.obj X)) := hSubZeroH
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨hZNe, hZSub⟩

end SSet

end
