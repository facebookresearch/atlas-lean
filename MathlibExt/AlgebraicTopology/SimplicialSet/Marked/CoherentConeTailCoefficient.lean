/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeImageMarkedIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterInclusion

/-!
# The whole original tail cone coefficients

Every subset with a positive least vertex already lies in the actual
zeroth-coface range. The existing native embedding-image isomorphism
therefore identifies its whole cone coefficient with the original
smaller coefficient. The positive-maximum version keeps the same
image map and marking through the actual bound insertion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Every whole original positive tail subset lies in the actual original coface image. -/
def coneTailImageLiftFunctor (n : ℕ) (i : Vertex.{u} n) :
    ConeSubset (coneTailEmbedding n i) ⥤ ConeEmbeddingImage (coneTailEmbedding n) i where
  obj a := ⟨a, by
    intro j hj
    exact (mem_coneCofaceEmbedding_range (0 : Fin (n + 2)) j).mpr
      (ne_of_gt ((coneTailEmbedding_positive i).trans_le (a.lower j hj)))⟩
  map f := homOfLE (leOfHom f)

/-- The whole actual supported tail image and the original target coefficient have the same subset words. -/
def coneTailImageNerveIso (n : ℕ) (i : Vertex.{u} n) :
    (coneEmbeddingMarkedImage (coneTailEmbedding n) i).toSSet ≅
      (coneWeight (coneTailEmbedding n i)).toSSet where
  hom := nerveMap (coneEmbeddingInclusion (coneTailEmbedding n) i)
  inv := nerveMap (coneTailImageLiftFunctor n i)
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext rfl) (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole actual tail image is its original marked coefficient with unchanged maximum marks. -/
def coneTailImageIso (n : ℕ) (i : Vertex.{u} n) :
    coneEmbeddingMarkedImage (coneTailEmbedding n) i ≅ coneWeight (coneTailEmbedding n i) :=
  isoMk (coneTailImageNerveIso n i) (fun _ => Iff.rfl)

/-- The actual smaller cone coefficient is strictly isomorphic to the original tail coefficient through its
  native coface image. -/
def coneTailCoefficientIso (n : ℕ) (i : Vertex.{u} n) :
    coneWeight i ≅ coneWeight (coneTailEmbedding n i) :=
  coneEmbeddingMarkedIso (coneTailEmbedding n) i ≪≫ coneTailImageIso n i

/-- The entire forward tail coefficient isomorphism is exactly the original cone coface image map. -/
theorem coneTailCoefficientIso_hom (n : ℕ) (i : Vertex.{u} n) :
    (coneTailCoefficientIso n i).hom = coneImage (coneTailEmbedding n).toOrderHom i :=
  coneEmbeddingMarkedIso_inclusion (coneTailEmbedding n) i

/-- The same original smaller coefficient identifies the whole positive-maximum tail coefficient. -/
def coneTailAfterCoefficientIso (n : ℕ) (i : Vertex.{u} n) :
    coneWeight i ≅ coneAfterWeight (coneTailEmbedding n i) (⊥ : Vertex.{u} (n + 1)) :=
  coneTailCoefficientIso n i ≪≫ (coneAfterAboveIso (coneTailEmbedding_positive i)).symm

/-- The actual positive-tail coefficient map followed by its original inclusion is the same whole original
  coface image. -/
theorem coneTailAfterCoefficientIso_inclusion (n : ℕ) (i : Vertex.{u} n) :
    (coneTailAfterCoefficientIso n i).hom ≫
      coneAfterInclusion (coneTailEmbedding n i) (⊥ : Vertex.{u} (n + 1)) =
        coneImage (coneTailEmbedding n).toOrderHom i := by
  change ((coneTailCoefficientIso n i).hom ≫ (coneAfterAboveIso (coneTailEmbedding_positive i)).inv) ≫
    (coneAfterAboveIso (coneTailEmbedding_positive i)).hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (coneTailCoefficientIso n i).hom ≫ f)
      (coneAfterAboveIso (coneTailEmbedding_positive i)).inv_hom_id).trans
      ((Category.comp_id _).trans (coneTailCoefficientIso_hom n i)))

end SSet.Marked.CoherentWeight
