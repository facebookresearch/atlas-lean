/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotient

/-!
# Naturality of the nested-image biproduct quotient comparison

Commuting maps between two diagrams `A ⟶ B ⟶ T` and `X ⟶ B` induce
canonical maps on the quotient of `B` by the two incoming maps and on the
quotient of the nested images in `T`.  The canonical
`imageQuotientBiprodIso` intertwines those two maps.

The map constructions and the nested-image square do not use exactness.
Exactness is required only to form the source and target comparison
isomorphisms in the final theorem.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Naturality of the inclusion from the image of a composite into the
image of its second factor. -/
theorem imageCompMap_naturality
    {A B T A' B' T' : C}
    (a : A ⟶ B) (b : B ⟶ T) (a' : A' ⟶ B') (b' : B' ⟶ T')
    (sqAB : Arrow.mk (a ≫ b) ⟶ Arrow.mk (a' ≫ b'))
    (sqB : Arrow.mk b ⟶ Arrow.mk b')
    (hτ : sqAB.right = sqB.right) :
    imageCompMap a b ≫ image.map sqB =
      image.map sqAB ≫ imageCompMap a' b' := by
  apply (cancel_mono (image.ι b')).1
  calc
    (imageCompMap a b ≫ image.map sqB) ≫ image.ι b' =
        imageCompMap a b ≫ (image.map sqB ≫ image.ι b') :=
      Category.assoc _ _ _
    _ = imageCompMap a b ≫ (image.ι b ≫ sqB.right) := by
      exact congrArg (fun k => imageCompMap a b ≫ k)
        (image.map_ι sqB)
    _ = (imageCompMap a b ≫ image.ι b) ≫ sqB.right :=
      (Category.assoc _ _ _).symm
    _ = image.ι (a ≫ b) ≫ sqB.right := by
      rw [imageCompMap_ι]
    _ = image.ι (a ≫ b) ≫ sqAB.right := by
      rw [hτ]
    _ = image.map sqAB ≫ image.ι (a' ≫ b') :=
      (image.map_ι sqAB).symm
    _ = image.map sqAB ≫
        (imageCompMap a' b' ≫ image.ι b') := by
      rw [imageCompMap_ι]
    _ = (image.map sqAB ≫ imageCompMap a' b') ≫ image.ι b' :=
      (Category.assoc _ _ _).symm

/-- The map on quotients by two incoming maps induced by commuting vertical
maps. -/
noncomputable def biprodQuotientMap
    {A X B A' X' B' : C}
    (a : A ⟶ B) (x : X ⟶ B) (a' : A' ⟶ B') (x' : X' ⟶ B')
    (α : A ⟶ A') (χ : X ⟶ X') (β : B ⟶ B')
    (ha : a ≫ β = α ≫ a') (hx : x ≫ β = χ ≫ x') :
    cokernel (biprod.desc a x) ⟶ cokernel (biprod.desc a' x') :=
  cokernel.map (biprod.desc a x) (biprod.desc a' x')
    (biprod.map α χ) β (by
      apply biprod.hom_ext'
      · simp only [biprod.inl_desc_assoc,
          biprod.inl_map_assoc, biprod.inl_desc]
        exact ha
      · simp only [biprod.inr_desc_assoc,
          biprod.inr_map_assoc, biprod.inr_desc]
        exact hx)

/-- The induced biproduct-quotient map computes on the canonical cokernel
projection. -/
@[reassoc]
theorem cokernel_π_biprodQuotientMap
    {A X B A' X' B' : C}
    (a : A ⟶ B) (x : X ⟶ B) (a' : A' ⟶ B') (x' : X' ⟶ B')
    (α : A ⟶ A') (χ : X ⟶ X') (β : B ⟶ B')
    (ha : a ≫ β = α ≫ a') (hx : x ≫ β = χ ≫ x') :
    cokernel.π (biprod.desc a x) ≫
        biprodQuotientMap a x a' x' α χ β ha hx =
      β ≫ cokernel.π (biprod.desc a' x') := by
  simp [biprodQuotientMap]

/-- The map on quotients of nested images induced by commuting vertical
maps. -/
noncomputable def imageQuotientMap
    {A B T A' B' T' : C}
    (a : A ⟶ B) (b : B ⟶ T) (a' : A' ⟶ B') (b' : B' ⟶ T')
    (α : A ⟶ A') (β : B ⟶ B') (τ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ τ = β ≫ b') :
    cokernel (imageCompMap a b) ⟶ cokernel (imageCompMap a' b') := by
  have hab : α ≫ (a' ≫ b') = (a ≫ b) ≫ τ := by
    rw [← Category.assoc, ← ha, Category.assoc, ← hb,
      ← Category.assoc]
  let sqAB : Arrow.mk (a ≫ b) ⟶ Arrow.mk (a' ≫ b') :=
    Arrow.homMk' α τ hab
  let sqB : Arrow.mk b ⟶ Arrow.mk b' :=
    Arrow.homMk' β τ hb.symm
  exact cokernel.map (imageCompMap a b) (imageCompMap a' b')
    (image.map sqAB) (image.map sqB)
    (imageCompMap_naturality a b a' b' sqAB sqB rfl)

/-- The induced nested-image-quotient map computes on the canonical cokernel
projection. -/
@[reassoc]
theorem cokernel_π_imageQuotientMap
    {A B T A' B' T' : C}
    (a : A ⟶ B) (b : B ⟶ T) (a' : A' ⟶ B') (b' : B' ⟶ T')
    (α : A ⟶ A') (β : B ⟶ B') (τ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ τ = β ≫ b') :
    cokernel.π (imageCompMap a b) ≫
        imageQuotientMap a b a' b' α β τ ha hb =
      image.map (Arrow.homMk' β τ hb.symm) ≫
        cokernel.π (imageCompMap a' b') := by
  simp [imageQuotientMap]

/-- The canonical comparison from a biproduct quotient to a quotient of
nested images is natural under commuting maps of exact diagrams. -/
theorem imageQuotientBiprodIso_naturality
    {A X B T A' X' B' T' : C}
    (a : A ⟶ B) (x : X ⟶ B) (b : B ⟶ T)
    (a' : A' ⟶ B') (x' : X' ⟶ B') (b' : B' ⟶ T')
    (α : A ⟶ A') (χ : X ⟶ X') (β : B ⟶ B') (τ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hx : x ≫ β = χ ≫ x')
    (hb : b ≫ τ = β ≫ b')
    (hxb : x ≫ b = 0) (hxb' : x' ≫ b' = 0)
    (hS : (ShortComplex.mk x b hxb).Exact)
    (hS' : (ShortComplex.mk x' b' hxb').Exact) :
    biprodQuotientMap a x a' x' α χ β ha hx ≫
        (imageQuotientBiprodIso a' x' b' hxb' hS').hom =
      (imageQuotientBiprodIso a x b hxb hS).hom ≫
        imageQuotientMap a b a' b' α β τ ha hb := by
  let sqB : Arrow.mk b ⟶ Arrow.mk b' :=
    Arrow.homMk' β τ hb.symm
  apply (cancel_epi (cokernel.π (biprod.desc a x))).1
  calc
    cokernel.π (biprod.desc a x) ≫
          (biprodQuotientMap a x a' x' α χ β ha hx ≫
            (imageQuotientBiprodIso a' x' b' hxb' hS').hom) =
        (β ≫ cokernel.π (biprod.desc a' x')) ≫
          (imageQuotientBiprodIso a' x' b' hxb' hS').hom := by
      rw [← Category.assoc, cokernel_π_biprodQuotientMap]
    _ = β ≫
        (factorThruImage b' ≫
          cokernel.π (imageCompMap a' b')) := by
      simpa only [imageQuotientBiprodIso, Category.assoc] using
        β ≫= cokernel_π_imageQuotientForward a' x' b' hxb'
    _ = (factorThruImage b ≫ image.map sqB) ≫
        cokernel.π (imageCompMap a' b') := by
      simpa only [Category.assoc, sqB, Arrow.homMk'_left,
        Arrow.mk_left, Arrow.mk_hom] using
        (image.factor_map sqB).symm =≫
          cokernel.π (imageCompMap a' b')
    _ = factorThruImage b ≫
        (image.map sqB ≫
          cokernel.π (imageCompMap a' b')) :=
      Category.assoc _ _ _
    _ = factorThruImage b ≫
        (cokernel.π (imageCompMap a b) ≫
          imageQuotientMap a b a' b' α β τ ha hb) := by
      rw [cokernel_π_imageQuotientMap]
    _ = (factorThruImage b ≫
          cokernel.π (imageCompMap a b)) ≫
        imageQuotientMap a b a' b' α β τ ha hb :=
      (Category.assoc _ _ _).symm
    _ = (cokernel.π (biprod.desc a x) ≫
          (imageQuotientBiprodIso a x b hxb hS).hom) ≫
        imageQuotientMap a b a' b' α β τ ha hb := by
      simpa only [imageQuotientBiprodIso, Category.assoc] using
        (cokernel_π_imageQuotientForward a x b hxb).symm =≫
          imageQuotientMap a b a' b' α β τ ha hb
    _ = cokernel.π (biprod.desc a x) ≫
        ((imageQuotientBiprodIso a x b hxb hS).hom ≫
          imageQuotientMap a b a' b' α β τ ha hb) :=
      Category.assoc _ _ _

end CategoryTheory

end
