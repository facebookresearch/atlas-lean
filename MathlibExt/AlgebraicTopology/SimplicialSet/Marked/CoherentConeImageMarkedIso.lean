/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeInjectiveImage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Whole marked original cone image isomorphism

The genuine ordinal embedding image comparison identifies the entire
original nerve and exactly the maximum-preserving marked edges. The
inclusion composite is precisely the original cone image map. All
original scalar operators, vertices and marks are retained, before
any native boundary-latching class conclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original supported cone image includes into the entire target cone by its literal full subset. -/
def coneEmbeddingInclusion {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    ConeEmbeddingImage f i ⥤ ConeSubset (f i) where
  obj := Subtype.val
  map h := homOfLE (leOfHom h)

/-- The genuine full cone subset order isomorphism induces the same entire original nerve isomorphism. -/
def coneEmbeddingNerveIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    nerve (ConeSubset i) ≅ nerve (ConeEmbeddingImage f i) where
  hom := nerveMap (coneEmbeddingOrderIso f i).monotone.functor
  inv := nerveMap (coneEmbeddingOrderIso f i).symm.monotone.functor
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ (coneEmbeddingOrderIso f i).monotone.functor) ⋙
      (coneEmbeddingOrderIso f i).symm.monotone.functor = x
    refine CategoryTheory.Functor.ext
      (fun t => (coneEmbeddingOrderIso f i).symm_apply_apply (x.obj t)) ?_
    intro a b h
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ (coneEmbeddingOrderIso f i).symm.monotone.functor) ⋙
      (coneEmbeddingOrderIso f i).monotone.functor = x
    refine CategoryTheory.Functor.ext
      (fun t => (coneEmbeddingOrderIso f i).apply_symm_apply (x.obj t)) ?_
    intro a b h
    exact Subsingleton.elim _ _

/-- The supported original image carries literally the target cone's pulled-back maximum-preserving marking. -/
def coneEmbeddingMarkedImage {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight (f i)) (nerveMap (coneEmbeddingInclusion f i))

/-- The entire native embedding image preserves and reflects precisely the original constant-maximum edge marking. -/
theorem coneEmbeddingNerve_marking_iff {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m)
    (i : Vertex.{u} n) (e : (coneWeight i).toSSet _⦋1⦌) :
    (coneEmbeddingNerveIso f i).hom.app (op ⦋1⦌) e ∈ (coneEmbeddingMarkedImage f i).marking ↔
      e ∈ (coneWeight i).marking := by
  change ((e.obj 0).image f.toOrderHom).maximum = ((e.obj 1).image f.toOrderHom).maximum ↔
    (e.obj 0).maximum = (e.obj 1).maximum
  rw [ConeSubset.image_maximum, ConeSubset.image_maximum]
  exact f.injective.eq_iff

/-- The actual whole cone embedding comparison is an isomorphism of the original marked carriers, not just
  of scalar cores. -/
def coneEmbeddingMarkedIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    coneWeight i ≅ coneEmbeddingMarkedImage f i :=
  isoMk (coneEmbeddingNerveIso f i) (fun e => (coneEmbeddingNerve_marking_iff f i e).symm)

/-- The original supported image inclusion retains every whole original target cone simplex and its original marking. -/
def coneEmbeddingMarkedInclusion {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    coneEmbeddingMarkedImage f i ⟶ coneWeight (f i) :=
  comapHom (coneWeight (f i)) (nerveMap (coneEmbeddingInclusion f i))

/-- The genuine marked image comparison followed by its literal inclusion is precisely the original full
  cone ordinal-image map. -/
theorem coneEmbeddingMarkedIso_inclusion {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m)
    (i : Vertex.{u} n) :
    (coneEmbeddingMarkedIso f i).hom ≫ coneEmbeddingMarkedInclusion f i = coneImage f.toOrderHom i := by
  apply Hom.ext
  ext q x
  refine CategoryTheory.Functor.ext (fun t => rfl) ?_
  intro a b h
  exact Subsingleton.elim _ _

end SSet.Marked.CoherentWeight
