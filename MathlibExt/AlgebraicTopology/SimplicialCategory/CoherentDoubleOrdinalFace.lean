/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCommonIntervalMaps

/-!
# Actual intersections of two original negative coherent faces

The common ordinal embedding has range exactly the complement of the two
specified original vertex labels. Its coherent Hom is isomorphic to the
actual intersection of their two negative path subcomplexes, even when
those labels lie inside the endpoint interval. No whole-interval coverage
or Kan condition is assumed for this supported-face comparison.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.DoubleOrdinalFace
open SimplicialEnrichment
variable {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k)

/-- The actual common ordinal embedding, retaining both original omitted labels. -/
def embedding : ULift.{u} (Fin (n + 1)) ↪o ULift.{u} (Fin (n + 3)) :=
  (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))).comp (OrdinalFace.embedding j)

/-- The whole common ordinal range omits exactly the two supplied individual original vertices. -/
theorem mem_range (x : ULift.{u} (Fin (n + 3))) :
    x ∈ Set.range (embedding j k hjk) ↔ x ≠ ULift.up j ∧ x ≠ ULift.up k := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(OrdinalFace.mem_range_embedding j _).mp ⟨_, rfl⟩, ?_⟩
    intro hk
    have hpre : (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a =
        ULift.up (k.pred (Fin.ne_zero_of_lt hjk)) :=
      (OrdinalFace.embedding j).injective (hk.trans (TwoOutsideFaces.omitted_image j k hjk).symm)
    exact (OrdinalFace.mem_range_embedding (k.pred (Fin.ne_zero_of_lt hjk)) _).mp ⟨a, rfl⟩ hpre
  · rintro ⟨hj, hk⟩
    obtain ⟨a, ha⟩ := (OrdinalFace.mem_range_embedding j x).mpr hj
    have hpre : a ≠ ULift.up (k.pred (Fin.ne_zero_of_lt hjk)) := by
      intro h
      subst a
      exact hk (ha.symm.trans (TwoOutsideFaces.omitted_image j k hjk))
    obtain ⟨b, hb⟩ := (OrdinalFace.mem_range_embedding (k.pred (Fin.ne_zero_of_lt hjk)) a).mpr hpre
    exact ⟨b, (congrArg (OrdinalFace.embedding j) hb).trans ha⟩

/-- The whole common coherent Hom face is the actual intersection of its two original negative subcomplexes. -/
theorem imageFace_eq (a b : ULift.{u} (Fin (n + 1))) :
    OrderEmbeddingFace.imageFace (embedding j k hjk) a b =
      HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up j)
        (TwoOutsideFaces.point j k hjk b) ⊓
      HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up k)
        (TwoOutsideFaces.point j k hjk b) := by
  apply Subfunctor.ext
  funext q
  ext p
  change (∀ t, (p.obj t).I ⊆ Set.range (embedding j k hjk)) ↔
    (∀ t, ULift.up j ∉ (p.obj t).I) ∧ (∀ t, ULift.up k ∉ (p.obj t).I)
  constructor
  · intro h
    exact ⟨fun t ht => ((mem_range j k hjk _).mp (h t ht)).1 rfl,
      fun t ht => ((mem_range j k hjk _).mp (h t ht)).2 rfl⟩
  · rintro ⟨hj, hk⟩ t x hx
    apply (mem_range j k hjk x).mpr
    constructor
    · intro h
      subst x
      exact hj t hx
    · intro h
      subst x
      exact hk t hx

/-- The actual intersection of the two original negative faces at the supplied common original endpoints. -/
def face (a b : ULift.{u} (Fin (n + 1))) :
    (nerve (SimplicialThickening.Path (TwoOutsideFaces.point j k hjk a) (TwoOutsideFaces.point j k hjk
      b))).Subcomplex :=
  HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up j) (TwoOutsideFaces.point j k hjk b) ⊓
    HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up k) (TwoOutsideFaces.point j k hjk b)

/-- The genuine original supported-Hom isomorphism onto the intersection of the two negative faces. -/
def homIso (a b : ULift.{u} (Fin (n + 1))) :
    nerve (SimplicialThickening.Path a b) ≅ face j k hjk a b :=
  OrderEmbeddingFace.faceIso (embedding j k hjk) a b ≪≫ SSet.Subcomplex.eqToIso (imageFace_eq j k hjk a b)

/-- The supported common-face isomorphism reads back the actual original composite coherent simplex operator. -/
theorem homIso_operator (a b : ULift.{u} (Fin (n + 1))) :
    (homIso j k hjk a b).hom ≫
      (face j k hjk a b).ι =
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
        coherentSimplexMap (SimplexCategory.δ j)).map (.mk a) (.mk b) := by
  change (OrderEmbeddingFace.faceIso (embedding j k hjk) a b).hom ≫
    (OrderEmbeddingFace.imageFace (embedding j k hjk) a b).ι = _
  exact (OrderEmbeddingFace.faceIso_imageMap (embedding j k hjk) a b).trans
    (WholeFaceComposition.imageMap_comp
      (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) (OrdinalFace.embedding j) a b).symm

end CategoryTheory.CoherentRealization.DoubleOrdinalFace
