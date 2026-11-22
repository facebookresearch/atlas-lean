/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofaceSupport

/-!
# All original proper operators enter the complete root boundary

Every original nonsurjective ordinal operator omits an actual target
vertex. If a source coefficient maps to the target root, that omitted
vertex is positive and is absent throughout the whole image word.
Every positive target coefficient is retained in full. Thus the same
original image operator lifts to the actual marked root-boundary
diagram, including all original scalar degrees and coherent paths.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every actual omitted target coordinate is absent throughout the whole original image simplex. -/
theorem coneImage_omittedCoordinate {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (i : Vertex.{u} n) (j : Vertex.{u} m) (hj : ∀ k, f k ≠ j)
    {q : SimplexCategoryᵒᵖ} (a : (nerve (ConeSubset i)).obj q) :
    (coneImage f i).hom.app q a ∈ (coneCoordinateFace (f i) j false).obj q := by
  apply (mem_coneCoordinateFace_false (f i) j _).mpr
  intro t h
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact hj k hk

/-- The same whole original image of every proper ordinal operator lies in the actual complete target root boundary. -/
theorem coneProperImage_mem {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) (i : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (a : (nerve (ConeSubset i)).obj q) :
    (coneImage f i).hom.app q a ∈ (coneRootBoundarySupport (f i)).obj q := by
  classical
  by_cases hi : f i = ⊥
  · have hx : ∃ j, ∀ k, f k ≠ j := by
      simpa only [Function.Surjective, not_forall, not_exists] using hf
    obtain ⟨j, hj⟩ := hx
    have hj0 : j ≠ (⊥ : Vertex.{u} m) := fun h => hj i (hi.trans h.symm)
    have hpos : (⊥ : Vertex.{u} m) < j := lt_of_le_of_ne bot_le (Ne.symm hj0)
    rw [coneRootBoundarySupport, ite_eq_left hi]
    apply (mem_coneCoordinateBoundary_iff (f i) _).mpr
    exact ⟨⟨j, hi.symm ▸ hpos⟩, false, coneImage_omittedCoordinate f i j hj a⟩
  · rw [coneRootBoundarySupport, ite_eq_right hi]
    exact Set.mem_univ _

/-- Every proper original image map retains the same whole simplex and its original maximum marking in the actual
supported coefficient. -/
def coneProperBoundaryImage {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) (i : Vertex.{u} n) :
    coneWeight i ⟶ coneRootBoundaryMarked (f i) where
  hom :=
    { app q := ↾fun a => ⟨(coneImage f i).hom.app q a, coneProperImage_mem f hf i a⟩
      naturality q r g := by
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        exact congr($((coneImage f i).hom.naturality g) a) }
  preserve {e} he := (coneImage f i).preserve he

/-- The actual supported proper-image map keeps precisely the original whole cone-image inclusion. -/
theorem coneProperBoundaryImage_inclusion {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) (i : Vertex.{u} n) :
    coneProperBoundaryImage f hf i ≫ coneRootBoundaryInclusion (f i) = coneImage f i := by
  apply Hom.ext
  rfl

/-- Restrict the complete target root-boundary diagram along the same actual original ordinal operator. -/
def coneRootBoundaryRestricted {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) :
    EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  (EnrichedFunctor.opposite (indexMap f)).comp SSet.{u} (coneRootBoundaryDiagram m)

/-- The full proper original cone operator lifts to the actual root-boundary enriched diagram with all its original
path actions. -/
def coneProperBoundaryOperator {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) : coneDiagram n ⟶ coneRootBoundaryRestricted f where
  app i := coneProperBoundaryImage f hf i.unop.as
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ConeSubset.image_prepend f _ _)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The full supported operator followed by the unchanged restricted inclusion is exactly the original whole cone
operator. -/
theorem coneProperBoundaryOperator_inclusion {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) :
    coneProperBoundaryOperator f hf ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f))).map
          (coneRootBoundaryDiagramInclusion m) = coneOperator f := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneProperBoundaryImage_inclusion f hf i.unop.as

/-- Precomposing a proper original operator keeps its same actual omitted target vertices. -/
theorem coneProper_comp {n m k : ℕ} (f : Vertex.{u} m →o Vertex.{u} k)
    (hf : ¬ Function.Surjective f) (g : Vertex.{u} n →o Vertex.{u} m) :
    ¬ Function.Surjective (f.comp g) := by
  intro h
  apply hf
  intro j
  obtain ⟨i, hi⟩ := h j
  exact ⟨g i, hi⟩

/-- All whole original scalar words compose through their same supported proper-image map. -/
theorem coneProperBoundaryImage_comp {n m k : ℕ} (f : Vertex.{u} m →o Vertex.{u} k)
    (hf : ¬ Function.Surjective f) (g : Vertex.{u} n →o Vertex.{u} m) (i : Vertex.{u} n) :
    coneImage g i ≫ coneProperBoundaryImage f hf (g i) =
      coneProperBoundaryImage (f.comp g) (coneProper_comp f hf g) i := by
  apply Hom.ext
  ext q a
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t => ConeSubset.image_comp g f _)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Every actual original coface is proper at the same omitted original vertex. -/
theorem coneCofaceEmbedding_not_surjective {n : ℕ} (j : Fin (n + 2)) :
    ¬ Function.Surjective (coneCofaceEmbedding.{u} j) := by
  intro h
  obtain ⟨i, hi⟩ := h (ULift.up j)
  exact Fin.succAbove_ne j i.down (congrArg ULift.down hi)

/-- All actual original cofaces, including the zeroth one, enter the same complete original marked root-boundary
diagram. -/
def coneRootBoundaryCoface {n : ℕ} (j : Fin (n + 2)) :
    coneDiagram n ⟶ coneRootBoundaryRestricted (coneCofaceEmbedding.{u} j).toOrderHom :=
  coneProperBoundaryOperator (coneCofaceEmbedding j).toOrderHom
    (coneCofaceEmbedding_not_surjective j)

/-- Every whole original coface lift retains its exact original cone operator and original attaching inclusion. -/
theorem coneRootBoundaryCoface_inclusion {n : ℕ} (j : Fin (n + 2)) :
    coneRootBoundaryCoface.{u} j ≫
        (enrichedDiagramRestrict
          (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom))).map
          (coneRootBoundaryDiagramInclusion (n + 1)) =
      coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap :=
  coneProperBoundaryOperator_inclusion (coneCofaceEmbedding j).toOrderHom
    (coneCofaceEmbedding_not_surjective j)

end SSet.Marked.CoherentWeight
