/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeProperBoundaryOperator

/-!
# The exact original lower root-face map into the supported coefficient

The same original marked lower-face isomorphism and supported proper
image agree as entire marked maps into the actual root boundary.
The original monic coefficient inclusion detects the equality, with
only the genuine original root equality used in the transport.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The whole original lower-face chart followed by its actual supported entry is exactly the same original proper
image and root transport. -/
theorem coneLowerRootFaceIso_boundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneLowerRootFaceIso.{u} j hj).hom ≫ coneLowerRootFaceToBoundary j hj =
      coneProperBoundaryImage (coneCofaceEmbedding j).toOrderHom (coneCofaceEmbedding_not_surjective j)
          (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneRootBoundaryMarked i)
          (coneCofaceEmbedding_root j hj)) := by
  let h := coneCofaceEmbedding_root.{u} j hj
  let e := coneLowerRootFaceIso.{u} j hj
  let g := coneLowerRootFaceToBoundary.{u} j hj
  let f := coneProperBoundaryImage (coneCofaceEmbedding j).toOrderHom
    (coneCofaceEmbedding_not_surjective j) (⊥ : Vertex.{u} n)
  let p := coneRootBoundaryInclusion (⊥ : Vertex.{u} (n + 1))
  let t := eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneRootBoundaryMarked i) h)
  let w := eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) h)
  have ht : t ≫ p = coneRootBoundaryInclusion (coneCofaceEmbedding j (⊥ : Vertex.{u} n)) ≫ w :=
    (eqToHom_naturality (fun i : Vertex.{u} (n + 1) => coneRootBoundaryInclusion i) h).symm
  have h₁ : (e.hom ≫ g) ≫ p =
      coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫ w :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun v => e.hom ≫ v) (coneLowerRootFaceToBoundary_inclusion j hj)).trans
        (coneLowerRootFaceIso_inclusion j hj))
  have h₂ : (f ≫ t) ≫ p =
      coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫ w :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun v => f ≫ v) ht).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun v => v ≫ w)
            (coneProperBoundaryImage_inclusion (coneCofaceEmbedding j).toOrderHom
              (coneCofaceEmbedding_not_surjective j) (⊥ : Vertex.{u} n)))))
  exact (cancel_mono p).mp (h₁.trans h₂.symm)

end SSet.Marked.CoherentWeight
