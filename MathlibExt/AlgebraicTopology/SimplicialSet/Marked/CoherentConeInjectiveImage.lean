/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators

/-!
# Original injective cone images retain their complete subset carrier

An actual ordinal order embedding identifies the original cone subsets
with precisely those whole target subsets contained in its image. The
inverse reads the original finite preimage, retaining every coordinate
and the designated least vertex. This is the native face-carrier
comparison needed by relative cone latching; no model-class equality
or filling outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual cone subsets supported on the entire image of an original ordinal embedding. -/
abbrev ConeEmbeddingImage {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :=
  {a : ConeSubset (f i) // ∀ j ∈ a.vertices, j ∈ Set.range f}

/-- The native original cone image, retaining its complete finite support inside the actual embedding range. -/
def coneEmbeddingImage {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n)
    (a : ConeSubset i) : ConeEmbeddingImage f i :=
  ⟨a.image f.toOrderHom, by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨k, rfl⟩⟩

/-- The exact original finite preimage of a supported target cone subset. -/
def coneEmbeddingPreimage {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n)
    (a : ConeEmbeddingImage f i) : ConeSubset i where
  vertices := Finset.univ.filter (fun j => f j ∈ a.val.vertices)
  mem := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.val.mem⟩
  lower j hj := f.le_iff_le.mp (a.val.lower (f j) (Finset.mem_filter.mp hj).2)

/-- Every original whole cone subset is recovered from its actual embedding image. -/
theorem coneEmbeddingPreimage_image {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m)
    (i : Vertex.{u} n) (a : ConeSubset i) :
    coneEmbeddingPreimage f i (coneEmbeddingImage f i a) = a := by
  apply ConeSubset.ext
  ext j
  simp only [coneEmbeddingPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  change f j ∈ a.vertices.image f ↔ j ∈ a.vertices
  constructor
  · intro hj
    obtain ⟨k, hk, h⟩ := Finset.mem_image.mp hj
    exact f.injective h ▸ hk
  · exact Finset.mem_image_of_mem f

/-- Every entire supported target cone subset is recovered from its native original finite preimage. -/
theorem coneEmbeddingImage_preimage {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m)
    (i : Vertex.{u} n) (a : ConeEmbeddingImage f i) :
    coneEmbeddingImage f i (coneEmbeddingPreimage f i a) = a := by
  apply Subtype.ext
  apply ConeSubset.ext
  ext j
  constructor
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hk).2
  · intro hj
    obtain ⟨k, rfl⟩ := a.property j hj
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

/-- The actual whole original cone is order-isomorphic to exactly its supported target image, including the
  zero-tail and all raised universe cases. -/
def coneEmbeddingOrderIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    ConeSubset i ≃o ConeEmbeddingImage f i where
  toFun := coneEmbeddingImage f i
  invFun := coneEmbeddingPreimage f i
  left_inv := coneEmbeddingPreimage_image f i
  right_inv := coneEmbeddingImage_preimage f i
  map_rel_iff' := by
    intro a b
    change a.vertices.image f ⊆ b.vertices.image f ↔ a.vertices ⊆ b.vertices
    exact Finset.image_subset_image_iff f.injective

end SSet.Marked.CoherentWeight
