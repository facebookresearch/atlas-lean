/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Quotients of nested images

For composable maps `A → B → T`, the image of the composite is a subobject
of the image of `B → T`.  If `X → B → T` is exact, quotienting `B` by the
sum of `A → B` and `X → B` is canonically isomorphic to the quotient of the
two nested images.  The comparison and its inverse are constructed from the
universal properties of images and cokernels.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A X B T : C} (a : A ⟶ B) (x : X ⟶ B) (b : B ⟶ T)

/-- Commutative square from a composite arrow to its second factor. -/
noncomputable def imageCompSquare : Arrow.mk (a ≫ b) ⟶ Arrow.mk b :=
  Arrow.homMk' a (𝟙 T) (by simp)

/-- Canonical inclusion of the image of a composite into the image of its
second factor. -/
noncomputable def imageCompMap : image (a ≫ b) ⟶ image b :=
  image.map (imageCompSquare a b)

/-- The image-of-composite inclusion followed by the target image inclusion
is the source image inclusion. -/
theorem imageCompMap_ι :
    imageCompMap a b ≫ image.ι b = image.ι (a ≫ b) := by
  simpa [imageCompMap, imageCompSquare] using
    image.map_ι (imageCompSquare a b)

/-- The composite-image epimorphism factors through the nested-image
inclusion. -/
@[reassoc]
theorem factorThruImage_imageCompMap :
    factorThruImage (a ≫ b) ≫ imageCompMap a b =
      a ≫ factorThruImage b := by
  simpa [imageCompMap, imageCompSquare] using
    image.factor_map (imageCompSquare a b)

/-- The image-of-composite comparison is monic. -/
noncomputable instance imageCompMap_mono : Mono (imageCompMap a b) :=
  mono_of_mono_fac (imageCompMap_ι a b)

/-- A morphism killed by `b` is also killed by the epimorphism onto
`image b`. -/
theorem comp_factorThruImage_eq_zero (hxb : x ≫ b = 0) :
    x ≫ factorThruImage b = 0 := by
  apply (cancel_mono (image.ι b)).1
  rw [Category.assoc, image.fac, hxb, zero_comp]

/-- Forward comparison from the quotient by `a` and an exact-kernel map to
the quotient of the two nested images. -/
noncomputable def imageQuotientForward (hxb : x ≫ b = 0) :
    cokernel (biprod.desc a x) ⟶ cokernel (imageCompMap a b) :=
  cokernel.desc (biprod.desc a x)
    (factorThruImage b ≫ cokernel.π (imageCompMap a b)) (by
      ext
      · rw [biprod.inl_desc_assoc,
          ← Category.assoc, ← factorThruImage_imageCompMap,
          Category.assoc, cokernel.condition, comp_zero, comp_zero]
      · rw [biprod.inr_desc_assoc,
          ← Category.assoc, comp_factorThruImage_eq_zero x b hxb,
          zero_comp, comp_zero])

/-- The forward comparison computes on the canonical cokernel projection. -/
@[reassoc]
theorem cokernel_π_imageQuotientForward (hxb : x ≫ b = 0) :
    cokernel.π (biprod.desc a x) ≫ imageQuotientForward a x b hxb =
      factorThruImage b ≫ cokernel.π (imageCompMap a b) := by
  simp [imageQuotientForward]

/-- Replace the final map in `X → B → T` by the epimorphism onto its image. -/
noncomputable def exactToImageShortComplex (hxb : x ≫ b = 0) :
    ShortComplex C :=
  ShortComplex.mk x (factorThruImage b)
    (comp_factorThruImage_eq_zero x b hxb)

/-- Exactness is preserved when the final map is replaced by its image
epimorphism. -/
theorem exactToImageShortComplex_exact (hxb : x ≫ b = 0)
    (hS : (ShortComplex.mk x b hxb).Exact) :
    (exactToImageShortComplex x b hxb).Exact := by
  let φ : exactToImageShortComplex x b hxb ⟶ ShortComplex.mk x b hxb :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι b
      comm₁₂ := by simp [exactToImageShortComplex]
      comm₂₃ := by
        simp [exactToImageShortComplex] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

/-- Map from `image b` to the quotient of `B` by the sum of `a` and `x`. -/
noncomputable def imageToBiprodQuotient (hxb : x ≫ b = 0)
    (hS : (ShortComplex.mk x b hxb).Exact) :
    image b ⟶ cokernel (biprod.desc a x) := by
  have hg : Epi (exactToImageShortComplex x b hxb).g := by
    dsimp [exactToImageShortComplex]
    infer_instance
  let _ := hg
  have hxzero : x ≫ cokernel.π (biprod.desc a x) = 0 := by
    simpa only [biprod.inr_desc_assoc, comp_zero] using
      (biprod.inr ≫= cokernel.condition (biprod.desc a x))
  have hzero : (exactToImageShortComplex x b hxb).f ≫
      cokernel.π (biprod.desc a x) = 0 := by
    simpa [exactToImageShortComplex] using hxzero
  exact (exactToImageShortComplex_exact x b hxb hS).desc
    (cokernel.π (biprod.desc a x)) hzero

/-- The map from `image b` computes after the epimorphism onto that image. -/
@[reassoc]
theorem factorThruImage_imageToBiprodQuotient
    (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    factorThruImage b ≫ imageToBiprodQuotient a x b hxb hS =
      cokernel.π (biprod.desc a x) := by
  have hg : Epi (exactToImageShortComplex x b hxb).g := by
    dsimp [exactToImageShortComplex]
    infer_instance
  let _ := hg
  exact (exactToImageShortComplex_exact x b hxb hS).g_desc _ _

/-- The nested-image inclusion is killed by the map to the biproduct
quotient. -/
theorem imageCompMap_imageToBiprodQuotient
    (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    imageCompMap a b ≫ imageToBiprodQuotient a x b hxb hS = 0 := by
  have hazero : a ≫ cokernel.π (biprod.desc a x) = 0 := by
    simpa only [biprod.inl_desc_assoc, comp_zero] using
      (biprod.inl ≫= cokernel.condition (biprod.desc a x))
  apply (cancel_epi (factorThruImage (a ≫ b))).1
  rw [factorThruImage_imageCompMap_assoc,
    factorThruImage_imageToBiprodQuotient, comp_zero]
  exact hazero

/-- Inverse comparison from the quotient of nested images to the quotient by
the two source maps. -/
noncomputable def imageQuotientInverse
    (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    cokernel (imageCompMap a b) ⟶ cokernel (biprod.desc a x) :=
  cokernel.desc (imageCompMap a b)
    (imageToBiprodQuotient a x b hxb hS)
    (imageCompMap_imageToBiprodQuotient a x b hxb hS)

/-- The inverse comparison computes on the canonical cokernel projection. -/
@[reassoc]
theorem cokernel_π_imageQuotientInverse
    (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    cokernel.π (imageCompMap a b) ≫
        imageQuotientInverse a x b hxb hS =
      imageToBiprodQuotient a x b hxb hS := by
  simp [imageQuotientInverse]

/-- If `X → B → T` is exact, then quotienting `B` by the images of `A` and
`X` is canonically the quotient `image(B→T) / image(A→T)`. -/
noncomputable def imageQuotientBiprodIso
    (hxb : x ≫ b = 0) (hS : (ShortComplex.mk x b hxb).Exact) :
    cokernel (biprod.desc a x) ≅ cokernel (imageCompMap a b) where
  hom := imageQuotientForward a x b hxb
  inv := imageQuotientInverse a x b hxb hS
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (biprod.desc a x))).1
    simp only [Category.comp_id]
    rw [← Category.assoc, cokernel_π_imageQuotientForward,
      Category.assoc, cokernel_π_imageQuotientInverse,
      factorThruImage_imageToBiprodQuotient]
  inv_hom_id := by
    apply (cancel_epi (cokernel.π (imageCompMap a b))).1
    simp only [Category.comp_id]
    rw [← Category.assoc, cokernel_π_imageQuotientInverse]
    apply (cancel_epi (factorThruImage b)).1
    rw [← Category.assoc, factorThruImage_imageToBiprodQuotient,
      cokernel_π_imageQuotientForward]

end CategoryTheory
