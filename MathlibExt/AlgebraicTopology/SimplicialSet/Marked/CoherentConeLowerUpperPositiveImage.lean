/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerUpperRootFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterRootCoface
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterMonomorphism

/-!
# The exact original lower/upper positive image and coordinate legs

The full marked lower/upper preimage retains its unchanged original
lower-coordinate inclusion. Its whole positive coface image is the
same original upper-coordinate entry into the positive root cone.
The original marked positive inclusion detects this equality on the
entire original simplex carrier and all inherited maximum marks.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The genuine complete positive lower/upper preimage retains exactly its original full lower-coordinate leg
through the unchanged positive inclusion and actual marked coface isomorphism. -/
theorem coneLowerUpperRootPositivePreimage_face {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneLowerUpperRootPositivePreimage.{u} j hj k hk ≫
      (coneAfterInclusion (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n) ≫ (coneLowerRootFaceIso j hj).hom) =
        coneLowerUpperRootFaceLeft j k := by
  let e := coneLowerRootFaceIso.{u} j hj
  let p := coneLowerUpperRootFaceLeft.{u} j k
  have hf := coneLowerUpperRootPositivePreimage_inclusion.{u} j hj k hk
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom) hf).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun f => p ≫ f) e.inv_hom_id).trans (Category.comp_id _))))

/-- The entire genuine positive image of the same original marked lower/upper intersection is precisely its
unchanged original upper-coordinate map into the whole original positive root cone. -/
theorem coneLowerUpperRootPositivePreimage_image {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneLowerUpperRootPositivePreimage.{u} j hj k hk ≫ coneAfterRootCofaceImage j hj =
      coneLowerUpperRootFaceRight j k ≫
        coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up k, hk⟩ := by
  let p := coneLowerUpperRootPositivePreimage.{u} j hj k hk
  let q := coneLowerUpperRootFaceRight.{u} j k
  let u := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up k, hk⟩
  let ι := coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  apply (cancel_mono ι).mp
  have hl : (p ≫ coneAfterRootCofaceImage j hj) ≫ ι = coneLowerUpperRootFaceInclusion j k :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => p ≫ f) (coneAfterRootCofaceImage_inclusion j hj)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ coneRootCofaceImage j hj) (coneLowerUpperRootPositivePreimage_inclusion j hj k
            hk)).trans
            (coneLowerUpperRootPreimage_inclusion j hj k))))
  have hr : (q ≫ u) ≫ ι = coneLowerUpperRootFaceInclusion j k :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => q ≫ f) (coneUpperFaceToAfter_inclusion (⊥ : Vertex.{u} (n + 1))
        (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up k, hk⟩)).trans (coneLowerUpperRootFaceRight_inclusion j k))
  exact hl.trans hr.symm

end SSet.Marked.CoherentWeight
