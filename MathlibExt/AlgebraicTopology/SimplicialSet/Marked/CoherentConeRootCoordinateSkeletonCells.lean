/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateRelativeWeakCells
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# The actual original skeletal root-boundary cells are the same weak scalar cells

The native relative skeletal boundary attachment retains the original
nondegenerate scalar and its actual omission from the coordinate-boundary
range. Its unchanged relative root-cube index therefore gives the SAME
original coordinate/scalar trivial cofibration, without endpoint,
dimension or weak-class certificates supplied as inputs.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The actual original skeletal boundary cell keeps exactly its same native relative nondegenerate root-cube scalar
index. -/
def coneRootCoordinateSkeletonCellNative {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N :=
  Subcomplex.N.mk c.simplex c.nonDegenerate (by
    intro hc
    exact c.notMem ⟨⟨c.simplex, hc⟩, rfl⟩)

/-- The original relative skeletal attachment retains precisely its unchanged whole original scalar simplex. -/
theorem coneRootCoordinateSkeletonCellNative_simplex {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (coneRootCoordinateSkeletonCellNative c).simplex = c.simplex := rfl

/-- The native relative skeletal index retains exactly its actual original scalar dimension. -/
theorem coneRootCoordinateSkeletonCellNative_dim {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (coneRootCoordinateSkeletonCellNative c).dim = d := rfl

/-- Every actual original skeletal root-boundary scalar cell yields the SAME genuine marked coordinate/scalar
coefficient trivial cofibration. -/
theorem coneRootCoordinateSkeletonCell_trivialCofibration {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    trivialCofibrations Marked.{u} (coneRootCoordinateScalarCell j hj c.simplex) :=
  nativeRootCoordinateRelativeCell_coefficientTrivialCofibration j hj hj'
    (coneRootCoordinateSkeletonCellNative c)

end SSet.Marked.CoherentWeight
