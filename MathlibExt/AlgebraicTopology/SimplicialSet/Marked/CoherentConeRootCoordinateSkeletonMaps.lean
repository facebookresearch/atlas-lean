/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonCells

/-!
# Actual original scalar skeletal attaching maps

The unchanged native scalar cell has its literal coproduct boundary and
whole-simplex inclusions into the original skeletal pushout. Reading
those same native maps retains its original full scalar map and both
original attaching equalities. No model or filler outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original scalar cell boundary enters the OLD native relative skeletal stage through its original
coproduct inclusion. -/
def coneRootCoordinateSkeletonBoundaryMap {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (boundary.{u} d : SSet.{u}) ⟶
      (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d : SSet.{u}) :=
  c.ιSigmaBoundary ≫ SSet.relativeCellComplexOfMono.t (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d

/-- The SAME entire original scalar simplex enters the native successor skeletal stage through its literal original
coproduct inclusion. -/
def coneRootCoordinateSkeletonSuccessorMap {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (Δ[d] : SSet.{u}) ⟶
      (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (d + 1) : SSet.{u}) :=
  c.ιSigmaStdSimplex ≫ SSet.relativeCellComplexOfMono.b (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d

/-- The actual original skeletal successor scalar map retains exactly its SAME entire original scalar simplex map
into the unchanged smaller-root coefficient. -/
theorem coneRootCoordinateSkeletonSuccessorMap_inclusion {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonSuccessorMap c ≫
        (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (d + 1)).ι = c.map :=
  c.ι_b_ι

/-- The SAME original scalar boundary map retains its unchanged whole original boundary inclusion followed by its
complete original scalar map. -/
theorem coneRootCoordinateSkeletonBoundaryMap_inclusion {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonBoundaryMap c ≫
        (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d).ι =
      (boundary.{u} d).ι ≫ c.map :=
  (c.ι_t_ι_eq_ι_l_b_ι).trans
    (congrArg (fun f => (boundary.{u} d).ι ≫ f) c.ι_b_ι)

/-- The actual original scalar boundary and whole successor maps commute through the unchanged original native
scalar skeletal attaching square. -/
theorem coneRootCoordinateSkeletonBoundaryMap_successor {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonBoundaryMap c ≫
        SSet.relativeCellComplexOfMono.r (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d =
      (boundary.{u} d).ι ≫ coneRootCoordinateSkeletonSuccessorMap c := by
  apply (cancel_mono (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (d + 1)).ι).mp
  calc
    (coneRootCoordinateSkeletonBoundaryMap c ≫
        SSet.relativeCellComplexOfMono.r (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫
          (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (d + 1)).ι =
        coneRootCoordinateSkeletonBoundaryMap c ≫
          (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d).ι := by
      rw [Category.assoc]
      exact congrArg (fun f => coneRootCoordinateSkeletonBoundaryMap c ≫ f)
        (Subcomplex.homOfLE_ι ((SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι).monotone (by omega)))
    _ = (boundary.{u} d).ι ≫ c.map := coneRootCoordinateSkeletonBoundaryMap_inclusion c
    _ = ((boundary.{u} d).ι ≫ coneRootCoordinateSkeletonSuccessorMap c) ≫
        (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (d + 1)).ι :=
      (congrArg (fun f => (boundary.{u} d).ι ≫ f) (coneRootCoordinateSkeletonSuccessorMap_inclusion c)).symm.trans
        (Category.assoc _ _ _).symm

end SSet.Marked.CoherentWeight
