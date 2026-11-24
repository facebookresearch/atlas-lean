/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentWholeFaceComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomFaces

/-!
# The genuine whole Hom interval in two original outside ordinal faces

Two omitted original vertices outside the same endpoint interval give a
whole coherent Hom isomorphism through their common original ordinal
face. The interval coverage is proved from those original vertex
inequalities and the actual face embeddings. All endpoints, scalar
degrees and the original composite coherent operator are retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.TwoOutsideFaces
open SimplicialEnrichment
variable {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k)

/-- The same original common-face vertex, read through its first actual pair of ordinal embeddings. -/
def point (a : ULift.{u} (Fin (n + 1))) : ULift.{u} (Fin (n + 3)) :=
  (OrdinalFace.embedding j) ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)

/-- Both original common-face operator orders retain the same individual vertex. -/
theorem point_right (a : ULift.{u} (Fin (n + 1))) :
    point j k hjk a =
      (OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a) :=
  ULift.ext (HornHomFaces.common_vertex j k hjk a.down)

/-- The second omitted original vertex is the exact image of its actual first-face preimage. -/
theorem omitted_image :
    (OrdinalFace.embedding j) (ULift.up (k.pred (Fin.ne_zero_of_lt hjk))) = (ULift.up k : ULift.{u} (Fin (n + 3))) :=
  ULift.ext (Fin.succAbove_pred_of_lt j k hjk)

/-- Outside the whole original interval implies outside its actual first-face preimage interval. -/
theorem inner_outside (a b : ULift.{u} (Fin (n + 1)))
    (hk : (ULift.up k : ULift.{u} (Fin (n + 3))) < point j k hjk a ∨ point j k hjk b < ULift.up k) :
    (ULift.up (k.pred (Fin.ne_zero_of_lt hjk)) : ULift.{u} (Fin (n + 2))) <
        (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a ∨
      (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b < ULift.up (k.pred (Fin.ne_zero_of_lt hjk)) := by
  rcases hk with hk | hk
  · left
    apply (OrdinalFace.embedding j).lt_iff_lt.mp
    exact (congrArg (fun x => x < point j k hjk a) (omitted_image j k hjk)).mpr hk
  · right
    apply (OrdinalFace.embedding j).lt_iff_lt.mp
    exact (congrArg (fun x => point j k hjk b < x) (omitted_image j k hjk)).mpr hk

/-- The genuine whole original common-face Hom isomorphism from two actual outside vertices. -/
def homIso (a b : ULift.{u} (Fin (n + 1)))
    (hj : (ULift.up j : ULift.{u} (Fin (n + 3))) < point j k hjk a ∨ point j k hjk b < ULift.up j)
    (hk : (ULift.up k : ULift.{u} (Fin (n + 3))) < point j k hjk a ∨ point j k hjk b < ULift.up k) :
    nerve (SimplicialThickening.Path a b) ≅
      nerve (SimplicialThickening.Path (point j k hjk a) (point j k hjk b)) :=
  IntervalFaceCover.outsideIso (k.pred (Fin.ne_zero_of_lt hjk)) a b (inner_outside j k hjk a b hk) ≪≫
    IntervalFaceCover.outsideIso j
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) hj

/-- The whole common-face forward Hom map is exactly the original composite coherent simplex operator. -/
theorem homIso_operator (a b : ULift.{u} (Fin (n + 1)))
    (hj : (ULift.up j : ULift.{u} (Fin (n + 3))) < point j k hjk a ∨ point j k hjk b < ULift.up j)
    (hk : (ULift.up k : ULift.{u} (Fin (n + 3))) < point j k hjk a ∨ point j k hjk b < ULift.up k) :
    (homIso j k hjk a b hj hk).hom =
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
        coherentSimplexMap (SimplexCategory.δ j)).map (.mk a) (.mk b) := by
  change (IntervalFaceCover.outsideIso (k.pred (Fin.ne_zero_of_lt hjk)) a b _).hom ≫
    (IntervalFaceCover.outsideIso j
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) hj).hom = _
  exact congrArg₂ (fun f g => f ≫ g)
    (IntervalFaceCover.outsideIso_operator (k.pred (Fin.ne_zero_of_lt hjk)) a b
      (inner_outside j k hjk a b hk))
    (IntervalFaceCover.outsideIso_operator j
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) hj)

end CategoryTheory.CoherentRealization.TwoOutsideFaces
