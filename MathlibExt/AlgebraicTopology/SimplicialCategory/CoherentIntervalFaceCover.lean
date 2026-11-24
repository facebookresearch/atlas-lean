/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrdinalFace

/-!
# Actual entire coherent Hom intervals carried by an ordinal face

A supplied order embedding covering the original endpoint interval gives
a genuine whole Hom isomorphism. For the actual ordinal face, the coverage
is proved when its omitted vertex lies outside those endpoints. No Hom
comparison is assumed as data; both whole inverses are the original path
image/preimage maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.IntervalFaceCover
variable {J K : Type u} [LinearOrder J] [LinearOrder K]
  (e : J ↪o K) (a b : J)

/-- Actual interval coverage identifies the original embedding face with the entire target Hom. -/
theorem imageFace_eq_top (h : ∀ x : K, e a ≤ x → x ≤ e b → x ∈ Set.range e) :
    OrderEmbeddingFace.imageFace e a b = ⊤ := by
  apply Subfunctor.ext
  funext q
  ext p
  constructor
  · intro _
    trivial
  · intro _ t x hx
    exact h x ((p.obj t).left_le x hx) ((p.obj t).le_right x hx)

/-- The genuine entire original Hom isomorphism from actual interval coverage. -/
def wholeHomIso (h : ∀ x : K, e a ≤ x → x ≤ e b → x ∈ Set.range e) :
    nerve (SimplicialThickening.Path a b) ≅ nerve (SimplicialThickening.Path (e a) (e b)) :=
  OrderEmbeddingFace.faceIso e a b ≪≫
    SSet.Subcomplex.eqToIso (imageFace_eq_top e a b h) ≪≫
      SSet.Subcomplex.topIso _

/-- The entire interval forward map is the original whole direct-image enriched Hom map. -/
theorem wholeHomIso_hom (h : ∀ x : K, e a ≤ x → x ≤ e b → x ∈ Set.range e) :
    (wholeHomIso e a b h).hom = OrderEmbeddingFace.imageMap e a b := by
  change (OrderEmbeddingFace.faceIso e a b).hom ≫ (OrderEmbeddingFace.imageFace e a b).ι = _
  exact OrderEmbeddingFace.faceIso_imageMap e a b

variable {n : ℕ} (t : Fin (n + 2)) (i j : ULift.{u} (Fin (n + 1)))

/-- The original ordinal face covers its entire endpoint interval when the omitted vertex is
outside it. -/
theorem ordinal_coverage
    (h : (ULift.up t : ULift.{u} (Fin (n + 2))) < (OrdinalFace.embedding t) i ∨
      (OrdinalFace.embedding t) j < ULift.up t)
    (x : ULift.{u} (Fin (n + 2)))
    (hi : (OrdinalFace.embedding t) i ≤ x) (hj : x ≤ (OrdinalFace.embedding t) j) :
    x ∈ Set.range (OrdinalFace.embedding t) := by
  apply (OrdinalFace.mem_range_embedding t x).mpr
  intro hx
  subst x
  rcases h with h | h
  · exact (not_lt_of_ge hi) h
  · exact (not_lt_of_ge hj) h

/-- The actual whole coherent Hom isomorphism of an outside ordinal face. -/
def outsideIso
    (h : (ULift.up t : ULift.{u} (Fin (n + 2))) < (OrdinalFace.embedding t) i ∨
      (OrdinalFace.embedding t) j < ULift.up t) :
    nerve (SimplicialThickening.Path i j) ≅
      nerve (SimplicialThickening.Path ((OrdinalFace.embedding t) i) ((OrdinalFace.embedding
        t) j)) :=
  wholeHomIso (OrdinalFace.embedding t) i j (ordinal_coverage t i j h)

/-- The outside-face Hom isomorphism retains exactly the actual original coherent simplex
operator. -/
theorem outsideIso_operator
    (h : (ULift.up t : ULift.{u} (Fin (n + 2))) < (OrdinalFace.embedding t) i ∨
      (OrdinalFace.embedding t) j < ULift.up t) :
    (outsideIso t i j h).hom =
      (SimplicialEnrichment.coherentSimplexMap (SimplexCategory.δ t)).map (.mk i) (.mk j) :=
  wholeHomIso_hom (OrdinalFace.embedding t) i j (ordinal_coverage t i j h)

end CategoryTheory.CoherentRealization.IntervalFaceCover
