/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingCube

/-!
# Actual order-embedding faces of coherent Hom objects

The original direct-image coherent Hom map of an order embedding is
identified with the actual subcomplex whose whole path chain lies in that
embedding's range. The inverse takes genuine preimages of the same path
subsets. Both whole scalar inverse equations are proved, with the original
endpoints retained. No face or mapping-space outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OrderEmbeddingFace
variable {J K : Type u} [LinearOrder J] [LinearOrder K] (e : J ↪o K) (i j : J)

private instance (a b : SimplicialThickening.Path i j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual original coherent Hom map induced by the supplied order embedding. -/
def imageMap : nerve (SimplicialThickening.Path i j) ⟶
    nerve (SimplicialThickening.Path (e i) (e j)) :=
  nerveMap (SimplicialThickening.functorMap e.toOrderHom (.mk i) (.mk j))

/-- The whole scalar path chain lies in the same supplied embedding range. -/
def imageFace : (nerve (SimplicialThickening.Path (e i) (e j))).Subcomplex where
  obj q := {p | ∀ t, (p.obj t).I ⊆ Set.range e}
  map f p hp := by
    intro t
    exact hp (f.unop.toOrderHom t)

variable {e i j}

/-- Preimage of the same original endpoint-containing path under the actual order embedding. -/
def preimagePath (p : SimplicialThickening.Path (e i) (e j)) : SimplicialThickening.Path i j where
  I := e ⁻¹' p.I
  left := p.left
  right := p.right
  left_le t ht := e.le_iff_le.mp (p.left_le (e t) ht)
  le_right t ht := e.le_iff_le.mp (p.le_right (e t) ht)

/-- Taking preimage of the original direct-image path returns its actual whole original subset. -/
theorem preimage_image (p : SimplicialThickening.Path i j) :
    preimagePath ((SimplicialThickening.functorMap e.toOrderHom (.mk i) (.mk j)).obj p) = p := by
  apply SimplicialThickening.Path.ext
  ext t
  constructor
  · rintro ⟨s, hs, he⟩
    have h : s = t := e.injective he
    simpa only [h] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- A whole original supported path is exactly recovered from its actual embedding preimage. -/
theorem image_preimage (p : SimplicialThickening.Path (e i) (e j)) (hp : p.I ⊆ Set.range e) :
    (SimplicialThickening.functorMap e.toOrderHom (.mk i) (.mk j)).obj (preimagePath p) = p := by
  apply SimplicialThickening.Path.ext
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro ht
    obtain ⟨s, rfl⟩ := hp ht
    exact ⟨s, ht, rfl⟩

variable (e i j)

/-- The actual preimage chain at every scalar vertex and arrow of the original supported face. -/
def preimageChain {q : SimplexCategoryᵒᵖ} (p : (imageFace e i j : SSet.{u}).obj q) :
    (nerve (SimplicialThickening.Path i j)).obj q where
  obj t := preimagePath (p.val.obj t)
  map f := ⟨homOfLE (fun t ht => (p.val.map f).hom.down.down ht)⟩

/-- The actual direct-image coherent map with values in its original supported face. -/
def toFace : nerve (SimplicialThickening.Path i j) ⟶ imageFace e i j where
  app q := ↾fun p => ⟨(imageMap e i j).app q p, fun t x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, rfl⟩⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((imageMap e i j).naturality f) p)

/-- The actual supported-face inverse on whole original scalar path chains. -/
def fromFace : (imageFace e i j : SSet.{u}) ⟶ nerve (SimplicialThickening.Path i j) where
  app q := ↾fun p => preimageChain e i j p
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y g
    exact Subsingleton.elim _ _

/-- The genuine original order-embedding Hom-face isomorphism, with both entire scalar
inverses proved. -/
def faceIso : nerve (SimplicialThickening.Path i j) ≅ imageFace e i j where
  hom := toFace e i j
  inv := fromFace e i j
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    refine CategoryTheory.Functor.ext (fun t => preimage_image (e := e) (p.obj t)) ?_
    intro x y f
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => image_preimage (p.val.obj t) (p.property t)) ?_
    intro x y f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual face comparison followed by its subcomplex inclusion is the original whole
coherent direct-image map. -/
theorem faceIso_imageMap : (faceIso e i j).hom ≫ (imageFace e i j).ι = imageMap e i j := rfl

end CategoryTheory.CoherentRealization.OrderEmbeddingFace
