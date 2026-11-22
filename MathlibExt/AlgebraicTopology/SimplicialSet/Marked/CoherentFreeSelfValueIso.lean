/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products

/-!
# Actual original free coefficient evaluation on a coherent self path

Every original coherent self path is its literal singleton identity.
Thus the full self-Hom nerve is terminal, with its original singleton
map and every scalar operator preserved. Its maximally marked product
with an arbitrary original coefficient is isomorphic to that unchanged
coefficient through the native free-unit and projection.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original free diagram value at its same coherent vertex is its unchanged marked coefficient
  through the original projection and native enriched identity unit. -/
def coherentFreeSelfValueIso {n : ℕ} (k : Vertex.{u} n) (A : Marked.{u}) :
    (enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k)) A).obj
      (op (SimplicialThickening.mk k)) ≅ A where
  hom := prodSnd _ A
  inv := enrichedFreeUnit _ _ A
  hom_inv_id := by
    apply Hom.ext
    ext q x
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => (coneSelfPath_eq_id (x.1.obj t)).symm) (fun _ _ _ => ?_)
      apply InducedCategory.Hom.ext
      exact Subsingleton.elim _ _
    · rfl
  inv_hom_id := Hom.ext rfl

/-- Original coefficient maps commute with the complete self-value projection, retaining both original Hom
  and coefficient coordinates. -/
theorem coherentFreeSelfValueIso_natural {n : ℕ} (k : Vertex.{u} n)
    {A D : Marked.{u}} (f : A ⟶ D) :
    ((enrichedFreeDiagramFunctor (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k))).map f).app
        (op (SimplicialThickening.mk k)) ≫ (coherentFreeSelfValueIso k D).hom =
      (coherentFreeSelfValueIso k A).hom ≫ f := Hom.ext rfl

end SSet.Marked.CoherentWeight
