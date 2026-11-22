/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceImages

/-!
# The actual whole original root-coface maximum map

The original maximum functor reads every vertex of every whole cone
simplex. Its same native nerve map is natural for the original root
transport. Thus the unchanged root coface image preserves precisely
the original ordinal image of every original maximum.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The unchanged original maximum functor reads every full original cone word into its original ordinal nerve. -/
def coneMaximumMap {n : ℕ} (i : Vertex.{u} n) : coneWeight i ⟶ max (nerve (Vertex.{u} n)) :=
  toMax (nerveMap (maximumFunctor i))

/-- The whole original root coface image retains its same full maximum map after the genuine original root transport. -/
theorem coneRootCofaceImage_maximumMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCofaceImage.{u} j hj ≫ coneMaximumMap (⊥ : Vertex.{u} (n + 1)) =
      coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫
        coneMaximumMap (coneCofaceEmbedding j (⊥ : Vertex.{u} n)) := by
  let h := coneCofaceEmbedding_root.{u} j hj
  let z := fun i : Vertex.{u} (n + 1) => coneMaximumMap i
  have ht : eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) h) ≫ z (⊥ : Vertex.{u} (n + 1)) =
      z (coneCofaceEmbedding j (⊥ : Vertex.{u} n)) :=
    (eqToHom_naturality z h).symm.trans (Category.comp_id _)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫ f) ht)

/-- Every scalar vertex of every whole original root cone simplex retains exactly the original coface image of its
same original maximum. -/
theorem coneRootCofaceImage_maximum {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ) (a : (nerve (ConeSubset (⊥ : Vertex.{u} n))).obj q) (t : Fin (q.unop.len + 1)) :
    (((coneRootCofaceImage j hj).hom.app q a).obj t).maximum = coneCofaceEmbedding j (a.obj t).maximum := by
  have h := congrArg (fun f : coneWeight (⊥ : Vertex.{u} n) ⟶ max (nerve (Vertex.{u} (n + 1))) =>
    (f.hom.app q a).obj t) (coneRootCofaceImage_maximumMap j hj)
  exact h.trans (ConeSubset.image_maximum (coneCofaceEmbedding j).toOrderHom (a.obj t))

end SSet.Marked.CoherentWeight
