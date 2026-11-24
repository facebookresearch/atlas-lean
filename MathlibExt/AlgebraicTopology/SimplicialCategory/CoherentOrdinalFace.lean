/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrderEmbeddingFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomBoxDecomposition

/-!
# Original ordinal zero faces of coherent Hom objects

The actual ordinal face embedding identifies its whole coherent Hom with
the original path subcomplex omitting precisely that face's vertex. Its
forward map is the original coherent simplex operator; the inverse takes
actual path preimages. The original endpoints and scalar degrees remain
unchanged.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OrdinalFace
open SimplicialEnrichment
variable {n : ℕ}

/-- The original lifted ordinal face embedding on the same coherent-simplex vertex labels. -/
def embedding (t : Fin (n + 2)) : ULift.{u} (Fin (n + 1)) ↪o ULift.{u} (Fin (n + 2)) where
  toFun x := ULift.up (t.succAbove x.down)
  inj' x y h := by
    apply ULift.ext
    exact (Fin.succAboveOrderEmb t).injective (congrArg ULift.down h)
  map_rel_iff' := (Fin.succAboveOrderEmb t).map_rel_iff'

/-- The actual face range omits exactly the supplied original lifted vertex. -/
theorem mem_range_embedding (t : Fin (n + 2)) (x : ULift.{u} (Fin (n + 2))) :
    x ∈ Set.range (embedding t) ↔ x ≠ ULift.up t := by
  constructor
  · rintro ⟨y, rfl⟩ h
    exact Fin.succAbove_ne t y.down (congrArg ULift.down h)
  · intro h
    have hx : x.down ∈ Set.range (Fin.succAboveOrderEmb t) := by
      rw [Fin.range_succAboveOrderEmb]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq, ULift.ext_iff] using h
    obtain ⟨y, hy⟩ := hx
    exact ⟨ULift.up y, ULift.ext hy⟩

/-- The actual whole embedding face is precisely the original negative coherent Hom face. -/
theorem imageFace_eq_negative (t : Fin (n + 2)) (a b : ULift.{u} (Fin (n + 1))) :
    OrderEmbeddingFace.imageFace (embedding t) a b =
      HomBoxDecomposition.negative ((embedding t) a) (ULift.up t) ((embedding t) b) := by
  apply Subfunctor.ext
  funext q
  ext p
  change (∀ s, (p.obj s).I ⊆ Set.range (embedding t)) ↔ ∀ s, ULift.up t ∉ (p.obj s).I
  constructor
  · intro h s hs
    exact (mem_range_embedding t _).mp (h s hs) rfl
  · intro h s x hx
    apply (mem_range_embedding t x).mpr
    intro he
    subst x
    exact h s hx

/-- The genuine coherent Hom isomorphism onto the same original negative face. -/
def negativeIso (t : Fin (n + 2)) (a b : ULift.{u} (Fin (n + 1))) :
    nerve (SimplicialThickening.Path a b) ≅
      HomBoxDecomposition.negative ((embedding t) a) (ULift.up t) ((embedding t) b) :=
  OrderEmbeddingFace.faceIso (embedding t) a b ≪≫
    SSet.Subcomplex.eqToIso (imageFace_eq_negative t a b)

/-- The negative-face comparison reads back the entire original coherent simplex face map. -/
theorem negativeIso_operator (t : Fin (n + 2)) (a b : ULift.{u} (Fin (n + 1))) :
    (negativeIso t a b).hom ≫
      (HomBoxDecomposition.negative ((embedding t) a) (ULift.up t) ((embedding t) b)).ι =
        (coherentSimplexMap (SimplexCategory.δ t)).map (.mk a) (.mk b) := by
  change (OrderEmbeddingFace.faceIso (embedding t) a b).hom ≫
    (OrderEmbeddingFace.imageFace (embedding t) a b).ι = _
  exact OrderEmbeddingFace.faceIso_imageMap (embedding t) a b

end CategoryTheory.CoherentRealization.OrdinalFace
