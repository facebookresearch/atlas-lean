/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateInsertion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeInjectiveImage

/-!
# Whole original coface vertices and exact finite root preimages

The original root equality transport changes no finite subset vertex.
Every whole coface simplex therefore retains exactly its original
coordinate image. The same native finite preimage reads every original
coordinate of an arbitrary larger-root subset, with coface image equal
to erasing precisely the omitted original coordinate.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual equality transport between original cone roots retains the entire finite vertex subset at every
scalar vertex. -/
theorem coneWeight_eqToHom_vertices {n : ℕ} (i k : Vertex.{u} n) (h : i = k)
    (q : SimplexCategoryᵒᵖ) (a : (coneWeight i).toSSet.obj q) (t : Fin (q.unop.len + 1)) :
    (((eqToHom (congrArg (fun v : Vertex.{u} n => coneWeight v) h)).hom.app q a).obj t).vertices =
      (a.obj t).vertices := by
  cases h
  rfl

/-- The full original coface subset image retains its genuine root and every original finite coordinate. -/
def coneRootCofaceSubset {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} n)) : ConeSubset (⊥ : Vertex.{u} (n + 1)) where
  vertices := a.vertices.image (coneCofaceEmbedding j)
  mem := coneCofaceEmbedding_root j hj ▸ Finset.mem_image_of_mem (coneCofaceEmbedding j) a.mem
  lower _ _ := bot_le

/-- The original whole coface subset retains exactly its original finite ordinal image. -/
theorem coneRootCofaceSubset_vertices {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} n)) :
    (coneRootCofaceSubset j hj a).vertices = a.vertices.image (coneCofaceEmbedding j) := rfl

/-- Every scalar vertex of the same original full root-coface map is precisely its unchanged original finite coface
image. -/
theorem coneRootCofaceImage_vertices {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ) (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet.obj q)
    (t : Fin (q.unop.len + 1)) :
    (((coneRootCofaceImage j hj).hom.app q a).obj t).vertices =
      (a.obj t).vertices.image (coneCofaceEmbedding j) :=
  coneWeight_eqToHom_vertices (coneCofaceEmbedding j (⊥ : Vertex.{u} n)) ⊥
    (coneCofaceEmbedding_root j hj) q
    ((coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n)).hom.app q a) t

/-- The same whole original coface map retains the complete original root subset record at each scalar vertex. -/
theorem coneRootCofaceImage_obj {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ) (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet.obj q)
    (t : Fin (q.unop.len + 1)) :
    ((coneRootCofaceImage j hj).hom.app q a).obj t = coneRootCofaceSubset j hj (a.obj t) :=
  ConeSubset.ext (coneRootCofaceImage_vertices j hj q a t)

/-- Inclusion of whole original root subsets remains inclusion of their same original coface images. -/
theorem coneRootCofaceSubset_mono {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Monotone (coneRootCofaceSubset.{u} j hj) := fun _ _ h => Finset.image_subset_image h

/-- The full original root preimage records exactly those original smaller ordinal vertices whose coface image
belongs to the unchanged larger subset. -/
def coneRootCofacePreimage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) : ConeSubset (⊥ : Vertex.{u} n) where
  vertices := Finset.univ.filter (fun k => coneCofaceEmbedding j k ∈ a.vertices)
  mem := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (coneCofaceEmbedding_root j hj).symm ▸ a.mem⟩
  lower _ _ := bot_le

/-- The exact original root coface preimage is monotone on the entire unchanged larger-root inclusion order. -/
theorem coneRootCofacePreimage_mono {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Monotone (coneRootCofacePreimage.{u} j hj) := by
  intro a b h k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hk).2⟩

/-- Every entire original smaller-root subset is recovered by its exact native coface preimage. -/
theorem coneRootCofacePreimage_image {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} n)) :
    coneRootCofacePreimage j hj (coneRootCofaceSubset j hj a) = a := by
  apply ConeSubset.ext
  ext k
  simp only [coneRootCofacePreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  change coneCofaceEmbedding j k ∈ a.vertices.image (coneCofaceEmbedding j) ↔ k ∈ a.vertices
  constructor
  · intro hk
    obtain ⟨l, hl, h⟩ := Finset.mem_image.mp hk
    exact (coneCofaceEmbedding j).injective h ▸ hl
  · exact Finset.mem_image_of_mem (coneCofaceEmbedding j)

/-- The actual full original coface image of a larger subset's exact preimage erases precisely its one omitted
original coordinate. -/
theorem coneRootCofaceImage_preimage_vertices {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    (coneRootCofaceSubset j hj (coneRootCofacePreimage j hj a)).vertices =
      a.vertices.erase (ULift.up j) := by
  ext k
  constructor
  · intro hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hne : coneCofaceEmbedding j l ≠ ULift.up j :=
      (mem_coneCofaceEmbedding_range j _).mp ⟨l, rfl⟩
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hl).2⟩
  · intro hk
    obtain ⟨l, rfl⟩ := (mem_coneCofaceEmbedding_range j k).mpr (Finset.mem_erase.mp hk).1
    exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp hk).2⟩, rfl⟩

end SSet.Marked.CoherentWeight
