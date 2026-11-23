/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridZeroComparisonEdge

/-!
# Original target-grid Q projection values for root edges

The actual Q-side projection evaluates every diagonal chain at its retained
Quillen simplex. Degree-zero morphism edges project to the degenerate retained
simplex, and identity edges of degree-one lifts project to the actual retained
one-simplex. These are original target-only values, independent of source roles.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial Topology

universe u v

namespace AlgebraicKTheory

variable (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- The Waldhausen structure derived from D's exact structure, used to read
the original Stage grid Q projection and its root edges. -/
local instance originalQEdgeValueWaldhausen : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

private theorem originalGridQDiagonalValueComputed (n : SimplexCategoryᵒᵖ)
    (q : (quillenStageGridDiagonal D).obj n) :
    (quillenStageGridToNQ (C := D)).app n q = (q.obj 0).q := by
  change (quillenQSimplexDiscreteDiagonalIso (C := D)).hom.app n
    ((quillenStageGridQProjectionDiagonal (C := D)).app n q) = _
  rw [quillenStageGridQProjectionDiagonal_app]
  rfl

/-- Every original diagonal chain Q projection is its actual retained simplex. -/
theorem quillenStageGridToNQ_diagonal_value (n : SimplexCategoryᵒᵖ)
    (q : (quillenStageGridDiagonal D).obj n) :
    (quillenStageGridToNQ (C := D)).app n q = (q.obj 0).q :=
  originalGridQDiagonalValueComputed D n q

private theorem originalGridQDegreeZeroEdgeComputed
    {X Y : QuillenStageGridLift D ⦋0⦌} (f : X ⟶ Y) :
    ((quillenStageGridDiagonalDegreeZeroMapEdge f).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id X.q).edge := by
  let a : (quillenStageGridDiagonal D).obj (op ⦋0⦌) := ComposableArrows.mk₀ X
  let b : (quillenStageGridDiagonal D).obj (op ⦋0⦌) := ComposableArrows.mk₀ Y
  let e : (quillenStageGridDiagonal D).Edge a b := quillenStageGridDiagonalDegreeZeroMapEdge f
  let q : (quillenStageGridDiagonal D).obj (op ⦋1⦌) :=
    quillenStageGridDiagonalDegreeZeroMapSimplex f
  have hEdge : e.edge = q := quillenStageGridDiagonalDegreeZeroMapEdge_edge f
  have hRetained : (q.obj 0).q = (SSet.Edge.id (X := NQ D) X.q).edge := by
    change ((reindexQuillenStageGridLift (C := D)
      (SimplexCategory.σ (0 : Fin 1))).obj X).q = (SSet.Edge.id (X := NQ D) X.q).edge
    exact (reindexQuillenStageGridLift_obj_q (SimplexCategory.σ (0 : Fin 1)) X).trans
      (by rfl)
  have hProjected : (quillenStageGridToNQ (C := D)).app (op ⦋1⦌) q =
      (SSet.Edge.id (X := NQ D) X.q).edge :=
    (quillenStageGridToNQ_diagonal_value D (op ⦋1⦌) q).trans hRetained
  change (e.map (quillenStageGridToNQ (C := D))).edge =
    (SSet.Edge.id (X := NQ D) X.q).edge
  exact (SSet.Edge.map_edge e (quillenStageGridToNQ (C := D))).trans
    ((congrArg (fun r : (quillenStageGridDiagonal D).obj (op ⦋1⦌) =>
      (quillenStageGridToNQ (C := D)).app (op ⦋1⦌) r) hEdge).trans hProjected)

/-- Every original degree-zero grid morphism edge has its actual degenerate
Q projection. No fiber-arrow or root compatibility witness is an input. -/
theorem quillenStageGridDegreeZeroEdge_toNQ_value
    {X Y : QuillenStageGridLift D ⦋0⦌} (f : X ⟶ Y) :
    ((quillenStageGridDiagonalDegreeZeroMapEdge f).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id X.q).edge :=
  originalGridQDegreeZeroEdgeComputed D f

/-- The original identity chain on a degree-one grid lift projects to the
EXACT original retained Quillen one-simplex. -/
theorem quillenStageGridIdentityOneSimplex_toNQ_value (X : QuillenStageGridLift D ⦋1⦌) :
    (quillenStageGridToNQ (C := D)).app (op ⦋1⦌) (ComposableArrows.mk₁ (𝟙 X)) = X.q :=
  quillenStageGridToNQ_diagonal_value D (op ⦋1⦌) (ComposableArrows.mk₁ (𝟙 X))

end AlgebraicKTheory

end
