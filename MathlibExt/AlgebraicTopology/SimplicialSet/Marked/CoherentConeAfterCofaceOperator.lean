/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofacePositiveCoefficient
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators

/-!
# Whole original positive-cone coface operators

A positive omitted vertex leaves the original root fixed. The original
whole ordinal image therefore preserves the positive-maximum subsets
and their exact maximum marking. The same original path-union law
gives the complete enriched positive-cone coface map and its unchanged
full-cone inclusion square.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The full original positive subset is carried by its same original coface image to a genuinely positive original
target subset. -/
def coneAfterCofaceSubsetImage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    {i : Vertex.{u} n} (a : ConeAfter i (⊥ : Vertex.{u} n)) :
    ConeAfter (coneCofaceEmbedding j i) (⊥ : Vertex.{u} (n + 1)) :=
  ⟨a.val.image (coneCofaceEmbedding j).toOrderHom, by
    let p := coneCofaceEmbedding.{u} j
    have hr : p (⊥ : Vertex.{u} n) = (⊥ : Vertex.{u} (n + 1)) := coneCofaceEmbedding_root j hj
    have hp : (⊥ : Vertex.{u} (n + 1)) < p a.val.maximum := hr ▸ p.strictMono a.property
    have hm := ConeSubset.image_maximum p.toOrderHom a.val
    exact hm.symm ▸ hp⟩

/-- The entire original positive cone subset category keeps its unchanged coface image on every object and monotone
scalar relation. -/
def coneAfterCofaceFunctor {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) (i : Vertex.{u} n) :
    ConeAfter i (⊥ : Vertex.{u} n) ⥤ ConeAfter (coneCofaceEmbedding j i) (⊥ : Vertex.{u} (n + 1)) where
  obj a := coneAfterCofaceSubsetImage j hj a
  map {a b} h := homOfLE (by
    change a.val.vertices.image (coneCofaceEmbedding j) ⊆ b.val.vertices.image (coneCofaceEmbedding j)
    exact Finset.image_subset_image (leOfHom h))

/-- The whole original marked positive coefficient coface map retains every original scalar simplex and the same
maximum-preserving edge marking. -/
def coneAfterCofaceCoefficient {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) (i : Vertex.{u} n) :
    coneAfterWeight i (⊥ : Vertex.{u} n) ⟶ coneAfterWeight (coneCofaceEmbedding j i) (⊥ : Vertex.{u} (n + 1)) where
  hom := nerveMap (coneAfterCofaceFunctor j hj i)
  preserve {e} he := by
    change ((e.obj 0).val.image (coneCofaceEmbedding j).toOrderHom).maximum =
      ((e.obj 1).val.image (coneCofaceEmbedding j).toOrderHom).maximum
    let f := (coneCofaceEmbedding.{u} j).toOrderHom
    have hh := congrArg f he
    exact (ConeSubset.image_maximum f (e.obj 0).val).trans
      (hh.trans (ConeSubset.image_maximum f (e.obj 1).val).symm)

/-- Every whole original positive coface coefficient retains exactly its original whole cone-image inclusion square. -/
theorem coneAfterCofaceCoefficient_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) (i : Vertex.{u} n) :
    coneAfterCofaceCoefficient j hj i ≫ coneAfterInclusion (coneCofaceEmbedding j i) (⊥ : Vertex.{u} (n + 1)) =
      coneAfterInclusion i (⊥ : Vertex.{u} n) ≫ coneImage (coneCofaceEmbedding j).toOrderHom i := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Every original positive coface gives the full marked enriched operator on the actual whole positive-cone
diagrams, preserving all original path actions. -/
def coneAfterCofaceOperator {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneAfterDiagram (⊥ : Vertex.{u} n) ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom))).obj
        (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) where
  app i := coneAfterCofaceCoefficient j hj i.unop.as
  naturality i l := by
    ext q p
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend (coneCofaceEmbedding j).toOrderHom _ _

/-- The actual full positive-cone coface operator retains exactly its unchanged original entire full-cone inclusion
square. -/
theorem coneAfterCofaceOperator_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneAfterCofaceOperator.{u} j hj ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom))).map
        (coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1))) =
      coneAfterDiagramInclusion (⊥ : Vertex.{u} n) ≫ coneOperator (coneCofaceEmbedding j).toOrderHom := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneAfterCofaceCoefficient_inclusion j hj i.unop.as

/-- On every original positive tail coefficient, the full positive-cone coface map retains precisely the same actual
original positive coefficient map after its genuine original double-coface vertex transport. -/
theorem coneAfterCofaceCoefficient_tail {n : ℕ} (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    coneAfterCofaceCoefficient k hk (coneTailEmbedding n i) ≫
      eqToHom (congrArg (fun v : Vertex.{u} (n + 2) => coneAfterWeight v (⊥ : Vertex.{u} (n + 2)))
        (coneTailCofaceVertex k hk i).symm) =
      coneAfterInclusion (coneTailEmbedding n i) (⊥ : Vertex.{u} (n + 1)) ≫ coneCofacePositiveCoefficient k hk i := by
  let v := coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)
  let w := coneCofaceEmbedding k (coneTailEmbedding n i)
  let hr := (coneTailCofaceVertex.{u} k hk i).symm
  let ι := coneAfterInclusion v (⊥ : Vertex.{u} (n + 2))
  let hpos := coneTailEmbedding_positive (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)
  have hι : (coneAfterAboveIso hpos).hom = ι := coneAfterAboveIso_hom hpos
  have : IsIso ι := hι ▸ (coneAfterAboveIso hpos).isIso_hom
  let a := coneAfterCofaceCoefficient.{u} k hk (coneTailEmbedding n i)
  let b := coneAfterInclusion (coneTailEmbedding n i) (⊥ : Vertex.{u} (n + 1))
  let t := eqToHom (congrArg (fun x : Vertex.{u} (n + 2) => coneAfterWeight x (⊥ : Vertex.{u} (n + 2))) hr)
  let s := eqToHom (congrArg (fun x : Vertex.{u} (n + 2) => coneWeight x) hr)
  have ht : t ≫ ι = coneAfterInclusion w (⊥ : Vertex.{u} (n + 2)) ≫ s :=
    (eqToHom_naturality (fun x : Vertex.{u} (n + 2) => coneAfterInclusion x (⊥ : Vertex.{u} (n + 2))) hr).symm
  apply (cancel_mono ι).mp
  have hl : (a ≫ t) ≫ ι = b ≫ (coneImage (coneCofaceEmbedding k).toOrderHom (coneTailEmbedding n i) ≫ s) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) ht).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ s) (coneAfterCofaceCoefficient_inclusion k hk (coneTailEmbedding n i))).trans
            (Category.assoc _ _ _))))
  have hh : (b ≫ coneCofacePositiveCoefficient k hk i) ≫ ι =
      b ≫ (coneImage (coneCofaceEmbedding k).toOrderHom (coneTailEmbedding n i) ≫ s) :=
    (Category.assoc _ _ _).trans (congrArg (fun z => b ≫ z) (coneCofacePositiveCoefficient_inclusion k hk i))
  exact hl.trans hh.symm

end SSet.Marked.CoherentWeight
