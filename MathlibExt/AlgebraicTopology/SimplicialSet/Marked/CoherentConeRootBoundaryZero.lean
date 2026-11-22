/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The original zero-dimensional root boundary is genuinely initial

The original zero-dimensional vertex has no positive tail coordinate.
Thus every scalar simplex of its original coordinate boundary is absent,
with precisely its inherited original marking. Its genuine marked
initial universal property at every original coefficient gives the
whole enriched initial universal property of the same root diagram.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire zero-dimensional original supported coefficient has no scalar simplex, since there is no original
positive coordinate. -/
theorem coneRootBoundaryZero_noSimplex (i : Vertex.{u} 0) (q : SimplexCategoryᵒᵖ)
    (a : (coneRootBoundaryMarked i).toSSet.obj q) : False := by
  have hi : i = (⊥ : Vertex.{u} 0) := ULift.ext (Fin.eq_zero i.down)
  have hs : coneRootBoundarySupport i = coneCoordinateBoundary i := by
    simp [coneRootBoundarySupport, hi]
  have ha : a.val ∈ (coneCoordinateBoundary i).obj q := hs ▸ a.property
  obtain ⟨j, _, _⟩ := (mem_coneCoordinateBoundary_iff i a.val).mp ha
  have hj : j.val = i := (ULift.ext (Fin.eq_zero j.val.down)).trans hi.symm
  exact (ne_of_lt j.property) hj.symm

/-- The unchanged original zero-dimensional marked root-boundary coefficient is genuinely initial with its full
inherited marking. -/
def coneRootBoundaryZeroCoefficientIsInitial (i : Vertex.{u} 0) : IsInitial (coneRootBoundaryMarked i) :=
  IsInitial.ofUniqueHom
    (fun X =>
      { hom :=
          { app q := ↾fun a => False.elim (coneRootBoundaryZero_noSimplex i q a)
            naturality q r f := by
              ext a
              exact False.elim (coneRootBoundaryZero_noSimplex i q a) }
        preserve {e} _ := False.elim (coneRootBoundaryZero_noSimplex i (op ⦋1⦌) e) })
    (fun X f => by
      apply Hom.ext
      ext q a
      exact False.elim (coneRootBoundaryZero_noSimplex i q a))

/-- The same original whole zero-dimensional marked enriched root boundary is genuinely initial, detected at every
actual marked evaluation coefficient. -/
def coneRootBoundaryZeroIsInitial : IsInitial (coneRootBoundaryDiagram.{u} 0) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  exact isColimitChangeEmptyCocone Marked.{u} (coneRootBoundaryZeroCoefficientIsInitial i.unop.as) _ (Iso.refl _)

end SSet.Marked.CoherentWeight
