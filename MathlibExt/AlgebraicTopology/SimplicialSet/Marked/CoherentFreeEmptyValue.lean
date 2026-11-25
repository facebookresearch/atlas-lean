/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# Whole original free coefficient values beyond their source

There is no original coherent path from a larger ordinal vertex to a
smaller source. Thus the whole marked free value is genuinely initial,
for every original coefficient and every scalar degree. Its unique
maps keep the complete original empty path carrier; no new lifting or
model outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original free value strictly beyond its actual source is initial for every whole marked coefficient. -/
def coherentFreeBeyondIsInitial {n : ℕ} {k i : Vertex.{u} n} (hi : k < i) (A : Marked.{u}) :
    IsInitial ((enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k)) A).obj
      (op (SimplicialThickening.mk i))) := by
  let noPath : ∀ p : SimplicialThickening.Path i k, False := fun p => (not_le_of_gt hi) p.le
  exact IsInitial.ofUniqueHom
    (fun X =>
      { hom :=
          { app q := ↾fun a => False.elim (noPath (a.1.obj 0))
            naturality q r f := by ext a; exact False.elim (noPath (a.1.obj 0)) }
        preserve {e} _ := False.elim (noPath (e.1.obj 0)) })
    (fun X f => by
      apply Hom.ext
      ext q a
      exact False.elim (noPath (a.1.obj 0)))

end SSet.Marked.CoherentWeight
