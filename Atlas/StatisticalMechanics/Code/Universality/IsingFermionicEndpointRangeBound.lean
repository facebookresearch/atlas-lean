/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFaceCornerCardinality









namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteGraphLaplacian_abs_le_four_of_unitRange
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V -> Real) (x : V)
    (hcard : Nat.card ↑(G.neighborSet x) <= 4)
    (hrange : forall y, 0 <= f y /\ f y <= 1) :
    |isingFiniteGraphLaplacian G f x| <= 4 := by
  have hneighbor : forall y, G.Adj x y -> |f y - f x| <= 1 := by
    intro y _
    rw [abs_le]
    have hx := hrange x
    have hy := hrange y
    constructor <;> linarith
  simpa using
    (FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteGraphLaplacian_abs_le_four_mul
      G f x 1 (by norm_num) hcard hneighbor)

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullSquareVertex_sampledLaplacian_le_four_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall x,
      0 <= (Phi (embedding x)).im /\ (Phi (embedding x)).im <= 1) :
    forall x,
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= 4 := by
  intro x
  exact isingFiniteGraphLaplacian_abs_le_four_of_unitRange
    (fkIsingSquareFullVertexGraph n) _ x
    (fullVertex_neighbor_card_le_four n x) hrange

theorem fullSquareFace_sampledLaplacian_le_four_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall c,
      0 <= (Phi (embedding c)).im /\ (Phi (embedding c)).im <= 1) :
    forall c,
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= 4 := by
  intro c
  exact isingFiniteGraphLaplacian_abs_le_four_of_unitRange
    (fkIsingSquareFullFaceGraph n) _ c
    (fullFace_neighbor_card_le_four n c) hrange

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
