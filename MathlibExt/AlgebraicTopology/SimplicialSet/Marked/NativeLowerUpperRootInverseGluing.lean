/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerUpperPositiveImage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerPositiveRootCompatibility

/-!
# Genuine native gluing on every full original lower/upper root intersection

The original complete marked lower/upper intersection has its actual
positive smaller-root preimage. The whole original positive-coface
source equation and unchanged upper-coordinate positive entry make
the two genuine inverse maps agree there. In dimension one the same
actual preimage lands in the original empty positive zero cone.
No native boundary source map is cancelled to prove this equality.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Both genuine original native lower and upper inverse maps agree on every entire original marked lower/upper root
intersection, all dimensions/universes/arbitrary original bases, with original coordinate projections and full
original coface/positive unit maps retained. -/
theorem nativeLowerUpperRootInverse_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (j k : Fin (n + 2)) (hj : 0 < j) (hk : 0 < k) :
    coneLowerUpperRootFaceLeft j k ≫ nativeLowerRootBoundaryInverse B σ j hj =
      coneLowerUpperRootFaceRight j k ≫ nativeUpperRootBoundaryInverse B σ k hk := by
  cases n with
  | zero =>
    apply Hom.ext
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    let a := (coneLowerUpperRootPositivePreimage.{u} j hj k hk).hom.app q x
    have hz : (a.obj 0).val.maximum = (⊥ : Vertex.{u} 0) := ULift.ext (Fin.eq_zero _)
    exact False.elim ((lt_irrefl _) (hz ▸ (a.obj 0).property))
  | succ n =>
    let p := coneLowerUpperRootPositivePreimage.{u} j hj k hk
    let a := coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ≫
      (coneLowerRootFaceIso j hj).hom
    let c := coneAfterRootCofaceImage.{u} j hj
    let u := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 2)) (⊥ : Vertex.{u} (n + 2)) ⟨ULift.up k, hk⟩
    let P := (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
    have hl : p ≫ a = coneLowerUpperRootFaceLeft j k := coneLowerUpperRootPositivePreimage_face j hj k hk
    have hr : p ≫ c = coneLowerUpperRootFaceRight j k ≫ u := coneLowerUpperRootPositivePreimage_image j hj k hk
    have hc : a ≫ nativeLowerRootBoundaryInverse B σ j hj = c ≫ P :=
      nativeLowerPositiveRootInverse_condition B n σ j hj
    exact (congrArg (fun f => f ≫ nativeLowerRootBoundaryInverse B σ j hj) hl.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => p ≫ f) hc).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ P) hr).trans (Category.assoc _ _ _)))))

end SSet.Marked
