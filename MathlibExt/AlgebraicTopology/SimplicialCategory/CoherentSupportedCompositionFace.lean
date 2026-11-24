/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFacesNaturality

/-!
# Original composition faces inside an actual embedding-supported Hom

The positive face in the source coherent simplex is isomorphic to the
intersection of the actual image-supported target Hom face and its
original positive middle-vertex face. The inverse takes the same path
preimages and retains the same original middle vertex at every scalar
vertex. No whole-interval coverage or Kan assumption is needed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.SupportedCompositionFace
open CompositionFace OrderEmbeddingFace
variable {J K : Type u} [LinearOrder J] [LinearOrder K] (e : J ↪o K) (i j k : J)

private instance (a b : SimplicialThickening.Path i k) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual image-supported Hom with the same original middle vertex in every scalar vertex. -/
def face : (nerve (SimplicialThickening.Path (e i) (e k))).Subcomplex :=
  imageFace e i k ⊓ positive (e i) (e j) (e k)

/-- The actual original positive face maps by direct image into the supported positive intersection. -/
def toFace : (positive i j k : SSet.{u}) ⟶ face e i j k where
  app q := ↾fun p => ⟨(imageMap e i k).app q p.val,
    ⟨fun t x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, rfl⟩,
      fun t => ⟨j, p.property t, rfl⟩⟩⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((imageMap e i k).naturality f) p.val)

/-- The same whole supported path chain pulls back to the source positive face, retaining the exact original
  middle vertex. -/
def fromFace : (face e i j k : SSet.{u}) ⟶ positive i j k where
  app q := ↾fun p => ⟨preimageChain e i k ⟨p.val, p.property.1⟩, p.property.2⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y g
    exact Subsingleton.elim _ _

/-- The genuine source-positive-face isomorphism onto the supported target-positive intersection. -/
def faceIso : (positive i j k : SSet.{u}) ≅ face e i j k where
  hom := toFace e i j k
  inv := fromFace e i j k
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => preimage_image (e := e) (p.val.obj t)) ?_
    intro x y f
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => image_preimage (p.val.obj t) (p.property.1 t)) ?_
    intro x y f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The supported positive-face comparison reads back the whole original direct-image coherent Hom map. -/
theorem faceIso_ι : (faceIso e i j k).hom ≫ (face e i j k).ι =
    (positive i j k).ι ≫ imageMap e i k := rfl

/-- The supported composition face retains the actual original three endpoint Hom maps and whole union composition. -/
theorem composition_readback :
    (positiveIso i j k).hom ≫ (faceIso e i j k).hom ≫ (face e i j k).ι =
      (imageMap e i j ⊗ₘ imageMap e j k) ≫ CompositionFace.composition (e i) (e j) (e k) := by
  exact (congrArg (fun f => (positiveIso i j k).hom ≫ f) (faceIso_ι e i j k)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ imageMap e i k) (positiveIso_composition i j k)).trans
        (FacesNaturality.imageMap_composition e i j k)))

end CategoryTheory.CoherentRealization.SupportedCompositionFace
