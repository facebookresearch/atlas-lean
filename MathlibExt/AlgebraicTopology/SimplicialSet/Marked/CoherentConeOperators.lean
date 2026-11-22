/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram
import MathlibExt.CategoryTheory.Enriched.FunctorOpposite

/-!
# Whole ordinal operators on the native marked coherent cone diagram

Every monotone original ordinal map acts by the whole direct image of
the original path and cone subsets. Image commutes with union and keeps
the exact image maximum. Consequently it supplies a genuine full
enriched natural transformation between the cone weight and its
restricted target weight. Faces and degeneracies use the same maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual coherent index map keeps every original interval-subset direct image. -/
def indexMap {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) :
    EnrichedFunctor SSet.{u} (Index.{u} n) (Index.{u} m) := SimplicialThickening.functor f

/-- Whole direct image commutes with prepending the entire original coherent path. -/
theorem ConeSubset.image_prepend {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    {i j : Vertex.{u} n} (p : SimplicialThickening.Path i j) (a : ConeSubset j) :
    (a.prepend p).image f = (a.image f).prepend
      ((SimplicialThickening.functorMap f (SimplicialThickening.mk i) (SimplicialThickening.mk j)).obj p) := by
  apply ConeSubset.ext
  change (p.I.toFinite.toFinset ∪ a.vertices).image f =
    (f '' p.I).toFinite.toFinset ∪ a.vertices.image f
  rw [Finset.image_union, Set.Finite.toFinset_image]

/-- Restrict the target cone diagram along the actual enriched original ordinal map. -/
def coneRestricted {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) :
    EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  (EnrichedFunctor.opposite (indexMap f)).comp SSet.{u} (coneDiagram m)

/-- Each original ordinal operator is a whole marked enriched natural map of the cone weights. -/
def coneOperator {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) :
    EnrichedDiagramMap (coneDiagram n) (coneRestricted f) where
  app i := coneImage f i.unop.as
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend f _ _

/-- Identity direct image preserves the same whole original subset. -/
theorem ConeSubset.image_id {n : ℕ} {i : Vertex.{u} n} (a : ConeSubset i) :
    a.image (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) = a := by
  apply ConeSubset.ext
  exact Finset.image_id

/-- Consecutive original ordinal images retain precisely the original whole composed vertex image. -/
theorem ConeSubset.image_comp {n m k : ℕ}
    (f : Vertex.{u} n →o Vertex.{u} m) (g : Vertex.{u} m →o Vertex.{u} k)
    {i : Vertex.{u} n} (a : ConeSubset i) : (a.image f).image g = a.image (g.comp f) := by
  apply ConeSubset.ext
  exact Finset.image_image

/-- The whole identity ordinal operator preserves the actual marked cone weight map. -/
theorem coneImage_id {n : ℕ} (i : Vertex.{u} n) :
    coneImage (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i = 𝟙 (coneWeight i) := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact ConeSubset.image_id _

/-- Whole cone-weight maps compose by the exact original composed ordinal operator. -/
theorem coneImage_comp {n m k : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (g : Vertex.{u} m →o Vertex.{u} k) (i : Vertex.{u} n) :
    coneImage f i ≫ coneImage g (f i) = coneImage (g.comp f) i := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact ConeSubset.image_comp f g _

/-- The original source maximum is carried to its same original ordinal image in every weight degree. -/
theorem coneOperator_maximum {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (i : Index.{u} n) (q : ℕ) (a : (nerve (ConeSubset i.as)) _⦋q⦌) (k : Fin (q + 1)) :
    ((((coneOperator f).app (op i)).hom.app (op ⦋q⦌) a).obj k).maximum =
      f (a.obj k).maximum := ConeSubset.image_maximum f _

end SSet.Marked.CoherentWeight
