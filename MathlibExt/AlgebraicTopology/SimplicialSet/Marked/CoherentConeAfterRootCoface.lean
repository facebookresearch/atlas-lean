/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterCofaceOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceImages

/-!
# The original full positive-root coface image

The complete original positive root cone enters the same original
positive target root through its unchanged coface coefficient and
genuine original root equality. Its full inclusion is exactly the
original positive inclusion followed by the original root cone image.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire original marked positive root cone keeps its same actual coface image at the unchanged original
target root. -/
def coneAfterRootCofaceImage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n) ⟶
      coneAfterWeight (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) :=
  coneAfterCofaceCoefficient j hj (⊥ : Vertex.{u} n) ≫
    eqToHom (congrArg (fun v : Vertex.{u} (n + 1) => coneAfterWeight v (⊥ : Vertex.{u} (n + 1)))
      (coneCofaceEmbedding_root j hj))

/-- The complete original positive root coface image retains exactly its unchanged original whole root cone-image
inclusion square. -/
theorem coneAfterRootCofaceImage_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneAfterRootCofaceImage.{u} j hj ≫ coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) =
      coneAfterInclusion (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n) ≫ coneRootCofaceImage j hj := by
  let h := coneCofaceEmbedding_root.{u} j hj
  let a := coneAfterCofaceCoefficient j hj (⊥ : Vertex.{u} n)
  let z := fun v : Vertex.{u} (n + 1) => coneAfterInclusion v (⊥ : Vertex.{u} (n + 1))
  let t := eqToHom (congrArg (fun v : Vertex.{u} (n + 1) => coneAfterWeight v (⊥ : Vertex.{u} (n + 1))) h)
  let s := eqToHom (congrArg (fun v : Vertex.{u} (n + 1) => coneWeight v) h)
  have ht : t ≫ z (⊥ : Vertex.{u} (n + 1)) = z (coneCofaceEmbedding j (⊥ : Vertex.{u} n)) ≫ s :=
    (eqToHom_naturality z h).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => a ≫ v) ht).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun v => v ≫ s) (coneAfterCofaceCoefficient_inclusion j hj (⊥ : Vertex.{u} n))).trans
          (Category.assoc _ _ _))))

end SSet.Marked.CoherentWeight
