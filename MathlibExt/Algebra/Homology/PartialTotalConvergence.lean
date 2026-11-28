/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalHomologyCoordinates
public import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalGraded
public import MathlibExt.Algebra.Homology.PartialTotalNegativeVanishing

/-!
# Stable intervals and image-filtration quotients of partial totals

Let `B` be a first-quadrant bicomplex in an abelian category. In total homology degree `n`,
the image filtration is `I_p = im(H_n(T_p) → H_n(Tot B))`, with preceding index `p-1` in the
integers and `I_(-1)=0`.

Stable-interval step images identify with these filtration subobjects, compatibly with their
inclusions. The stable object for the interval from `p-1` to `p` is the cokernel of `I_(p-1) →
I_p`. Its projection and graded-quotient comparison retain the partial-total homology maps and
their image factors.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Abelian.SpectralObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The total-homology coordinate of a stable-interval abutment.

The stable-interval abutment at cochain degree `-n` is isomorphic to degree-`n` homology of
the full bicomplex total. -/
noncomputable def partialTotalStableAbutmentHomologyIso (n : ℕ) :
    B.partialTotalSpectralObject.stableIntervalAbutment (-(n : ℤ)) ≅
      (B.total (ComplexShape.down ℕ)).homology n := by
  dsimp only [stableIntervalAbutment, stableIntervalFull]
  exact
    B.partialTotalSpectralObjectHObjIso (-(n : ℤ))
        (show (⊥ : EInt) ≤ ⊤ from bot_le) ≪≫
      CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltration.map
          (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le)))
        B.isZero_partialTotalCochainFiltration_obj_bot (-(n : ℤ)) ≪≫
      (B.total (ComplexShape.down ℕ)).extendHomologyIso
        ComplexShape.embeddingDownNat rfl

/-- The image-filtration coordinate of a nonnegative stable step.

The stable-step image at stage `s` identifies with the partial-total homology filtration
subobject in degree `n`. -/
noncomputable def partialTotalStableStepImageFiltrationIso
    (n s : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStepImage
        (-(n : ℤ)) ((s : ℤ) : EInt) ≅
      (B.partialTotalHomologyFiltration n).obj ((s : ℤ) : EInt) := by
  let Y := B.partialTotalSpectralObject
  let d : ℤ := -(n : ℤ)
  let i : EInt := ((s : ℤ) : EInt)
  let a := Y.stableIntervalStepToAbutment d i
  let u := HomologicalComplex.homologyMap (B.partialTotalι s) n
  let eS := B.partialTotalSpectralStepHomologyIso n s
  let eA := B.partialTotalSpectralAbutmentHomologyIso n
  let eI := B.partialTotalHomologyFiltrationObjIsoImage n s
  have ha : a =
      (Y.H d).map (B.partialTotalSpectralStepToAbutmentArrow s) := by
    apply (Y.H d).congr_map
    subsingleton
  have hnat : a ≫ eA.hom = eS.hom ≫ u := by
    rw [ha]
    exact B.partialTotalSpectralStepToAbutment_comp_iso_hom n s
  exact Limits.image.compIso a eA.hom ≪≫
    Limits.image.eqToIso hnat ≪≫
    asIso (Limits.image.preComp eS.hom u) ≪≫ eI.symm

/-- The inclusion equation of a stable-step image comparison.

The image comparison followed by filtration inclusion equals stable-step image inclusion
followed by the total-homology abutment comparison. -/
@[reassoc]
theorem partialTotalStableStepImageFiltrationIso_hom_comp_ι
    (n s : ℕ) :
    (B.partialTotalStableStepImageFiltrationIso n s).hom ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
      Limits.image.ι
          (B.partialTotalSpectralObject.stableIntervalStepToAbutment
            (-(n : ℤ)) ((s : ℤ) : EInt)) ≫
        (B.partialTotalSpectralAbutmentHomologyIso n).hom := by
  let Y := B.partialTotalSpectralObject
  let d : ℤ := -(n : ℤ)
  let i : EInt := ((s : ℤ) : EInt)
  let a := Y.stableIntervalStepToAbutment d i
  let u := HomologicalComplex.homologyMap (B.partialTotalι s) n
  let eS := B.partialTotalSpectralStepHomologyIso n s
  let eA := B.partialTotalSpectralAbutmentHomologyIso n
  let eI := B.partialTotalHomologyFiltrationObjIsoImage n s
  have ha : a =
      (Y.H d).map (B.partialTotalSpectralStepToAbutmentArrow s) := by
    apply (Y.H d).congr_map
    subsingleton
  have hnat : a ≫ eA.hom = eS.hom ≫ u := by
    rw [ha]
    exact B.partialTotalSpectralStepToAbutment_comp_iso_hom n s
  have heI : eI.inv ≫
      (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
        Limits.image.ι u := by
    change (B.partialTotalHomologyFiltrationObjIsoImage n s).inv ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
      Limits.image.ι u
    rw [← B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι n s,
      Iso.inv_hom_id_assoc]
  change ((Limits.image.compIso a eA.hom ≪≫
      Limits.image.eqToIso hnat ≪≫
      asIso (Limits.image.preComp eS.hom u) ≪≫ eI.symm).hom) ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) = _
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [heI, asIso_hom, Limits.image.preComp_ι,
    ← Limits.image.eq_fac hnat, Limits.image.compIso_hom_comp_image_ι]

/-- Vanishing of the preceding stable step at filtration degree zero.

The stable step at integer filtration index `-1` is zero. -/
theorem isZero_partialTotalStablePreviousStep_zero (n : ℕ) :
    IsZero (B.partialTotalSpectralObject.stableIntervalStep
      (-(n : ℤ)) (((-1 : ℤ) : EInt))) := by
  let hE : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt) := by simp
  let f := B.partialTotalCochainFiltration.map (homOfLE hE)
  have hSource := B.isZero_partialTotalCochainFiltration_obj_bot
  have hTarget :=
    B.isZero_partialTotalCochainFiltration_obj_of_neg (-1) (by omega)
  have hConeX : IsZero ((CochainComplex.mappingCone f).X (-(n : ℤ))) :=
    (CochainComplex.mappingCone.isZero_X_iff f (-(n : ℤ))).2
      ⟨(HomologicalComplex.eval C (ComplexShape.up ℤ)
          (-(n : ℤ) + 1)).map_isZero hSource,
        (HomologicalComplex.eval C (ComplexShape.up ℤ)
          (-(n : ℤ))).map_isZero hTarget⟩
  have hConeH : IsZero
      ((CochainComplex.mappingCone f).homology (-(n : ℤ))) :=
    ((CochainComplex.mappingCone f).sc (-(n : ℤ)))
      |>.isZero_homology_of_isZero_X₂ hConeX
  exact IsZero.of_iso hConeH
    (B.partialTotalSpectralObjectHObjIso (-(n : ℤ)) hE)

/-- Vanishing of the preceding stable image at filtration degree zero.

The image of the stable step at integer index `-1` in the abutment is zero. -/
theorem isZero_partialTotalStablePreviousImage_zero (n : ℕ) :
    IsZero (B.partialTotalSpectralObject.stableIntervalStepImage
      (-(n : ℤ)) (((-1 : ℤ) : EInt))) :=
  IsZero.of_epi
    (Limits.factorThruImage
      (B.partialTotalSpectralObject.stableIntervalStepToAbutment
        (-(n : ℤ)) (((-1 : ℤ) : EInt))))
    (B.isZero_partialTotalStablePreviousStep_zero n)

/-- The preceding-image coordinate of the partial-total filtration.

The preceding stable-step image identifies with the preceding filtration object, including the
zero object at index `-1`. -/
noncomputable def partialTotalStablePreviousImageFiltrationIso
    (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStepImage
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex p) ≅
      (B.partialTotalHomologyFiltration n).obj
        (partialTotalHomologyPreviousIndex p) := by
  rcases p with _ | m
  · have hImage := B.isZero_partialTotalStablePreviousImage_zero n
    have hFiltration :=
      B.isZero_partialTotalHomologyFiltration_obj_of_neg n (-1) (by omega)
    exact IsZero.iso hImage hFiltration
  · simpa only [partialTotalHomologyPreviousIndex_succ] using
      B.partialTotalStableStepImageFiltrationIso n m

/-- The inclusion equation of a preceding stable-image comparison.

The preceding-image comparison commutes with its image inclusion into the abutment and
filtration inclusion into total homology. -/
@[reassoc]
theorem partialTotalStablePreviousImageFiltrationIso_hom_comp_ι
    (n p : ℕ) :
    (B.partialTotalStablePreviousImageFiltrationIso n p).hom ≫
        (B.partialTotalHomologyFiltration n).ι.app
          (partialTotalHomologyPreviousIndex p) =
      Limits.image.ι
          (B.partialTotalSpectralObject.stableIntervalStepToAbutment
            (-(n : ℤ)) (partialTotalHomologyPreviousIndex p)) ≫
        (B.partialTotalSpectralAbutmentHomologyIso n).hom := by
  rcases p with _ | m
  · exact (B.isZero_partialTotalStablePreviousImage_zero n).eq_of_src _ _
  · change (B.partialTotalStableStepImageFiltrationIso n m).hom ≫
        (B.partialTotalHomologyFiltration n).ι.app ((m : ℤ) : EInt) = _
    simpa only [partialTotalHomologyPreviousIndex_succ] using
      B.partialTotalStableStepImageFiltrationIso_hom_comp_ι n m

/-- The adjacent image map in partial-total filtration coordinates.

The stable-image map from the preceding stage to the current stage becomes the adjacent
filtration inclusion through the image isomorphisms. -/
@[reassoc]
theorem partialTotalStableImageMap_comp_currentIso_hom
    (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalImageMap
          (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) ≫
        (B.partialTotalStableStepImageFiltrationIso n p).hom =
      (B.partialTotalStablePreviousImageFiltrationIso n p).hom ≫
        B.partialTotalHomologyFiltrationAdjacentHom n p := by
  rcases p with _ | m
  · exact (B.isZero_partialTotalStablePreviousImage_zero n).eq_of_src _ _
  · apply (cancel_mono
      ((B.partialTotalHomologyFiltration n).ι.app
        (((m + 1 : ℕ) : ℤ) : EInt))).1
    simp only [Category.assoc,
      B.partialTotalStableStepImageFiltrationIso_hom_comp_ι n (m + 1),
      stableIntervalImageMap_comp_ι_assoc,
      B.partialTotalHomologyFiltrationAdjacentHom_comp_ι n (m + 1),
      B.partialTotalStablePreviousImageFiltrationIso_hom_comp_ι n (m + 1)]

/-- The stable interval object of an adjacent partial-total filtration pair.

In degree `n` and stage `p`, take the stable interval object at cochain degree `-n` for the
preceding-to-current filtration indices. -/
noncomputable abbrev partialTotalStableObj (n p : ℕ) : C :=
  B.partialTotalSpectralObject.stableIntervalObj
    (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)

/-- The stable-step map to its partial-total image subobject.

Factor the stable step through its image in the abutment and then use the image-filtration
comparison. -/
noncomputable def partialTotalSpectralStepToFiltration (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStep
        (-(n : ℤ)) ((p : ℤ) : EInt) ⟶
      (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) :=
  B.partialTotalSpectralObject.stableIntervalStepToImage
      (-(n : ℤ)) ((p : ℤ) : EInt) ≫
    (B.partialTotalStableStepImageFiltrationIso n p).hom

/-- The inclusion formula for a stable-step image factor.

The image factor followed by filtration inclusion is the partial-total step homology
coordinate followed by homology of the finite-stage inclusion. -/
theorem partialTotalSpectralStepToFiltration_comp_ι (n s : ℕ) :
    B.partialTotalSpectralStepToFiltration n s ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
      (B.partialTotalSpectralStepHomologyIso n s).hom ≫
        HomologicalComplex.homologyMap (B.partialTotalι s) n := by
  let Y := B.partialTotalSpectralObject
  let d : ℤ := -(n : ℤ)
  let i : EInt := ((s : ℤ) : EInt)
  let a := Y.stableIntervalStepToAbutment d i
  let eA := B.partialTotalStableAbutmentHomologyIso n
  let eS := B.partialTotalSpectralStepHomologyIso n s
  let u := HomologicalComplex.homologyMap (B.partialTotalι s) n
  have hCanonical : a ≫ eA.hom = eS.hom ≫ u := by
    change
      (B.partialTotalSpectralObject.H (-(n : ℤ))).map
            (B.partialTotalSpectralStepToAbutmentArrow s) ≫
          (B.partialTotalSpectralAbutmentHomologyIso n).hom = _
    exact B.partialTotalSpectralStepToAbutment_comp_iso_hom n s
  have hCanonicalImage :
      (B.partialTotalStableStepImageFiltrationIso n s).hom ≫
          (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
        Limits.image.ι a ≫ eA.hom := by
    change
      (B.partialTotalStableStepImageFiltrationIso n s).hom ≫
          (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
        Limits.image.ι
            (B.partialTotalSpectralObject.stableIntervalStepToAbutment
              (-(n : ℤ)) ((s : ℤ) : EInt)) ≫
          (B.partialTotalSpectralAbutmentHomologyIso n).hom
    exact B.partialTotalStableStepImageFiltrationIso_hom_comp_ι n s
  dsimp only [partialTotalSpectralStepToFiltration]
  rw [Category.assoc, hCanonicalImage]
  change
    Limits.factorThruImage
          (Y.stableIntervalStepToAbutment d i) ≫
        Limits.image.ι (Y.stableIntervalStepToAbutment d i) ≫ eA.hom = _
  rw [Limits.image.fac_assoc]
  exact hCanonical

/-- The filtration projection to an adjacent stable interval object.

Use the inverse current-image comparison and the stable interval quotient of that image. -/
noncomputable def partialTotalHomologyFiltrationToStable (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ⟶
      B.partialTotalStableObj n p :=
  (B.partialTotalStableStepImageFiltrationIso n p).inv ≫
    B.partialTotalSpectralObject.stableIntervalImageToStable
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)

/-- The stable-step factorization through its filtration image.

The stable-step-to-filtration map followed by the stable quotient equals the stable-step-to-
stable-object map. -/
@[reassoc (attr := simp)]
theorem partialTotalSpectralStepToFiltration_comp_toStable
    (n p : ℕ) :
    B.partialTotalSpectralStepToFiltration n p ≫
        B.partialTotalHomologyFiltrationToStable n p =
      B.partialTotalSpectralObject.stableIntervalStepToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) := by
  simp only [partialTotalSpectralStepToFiltration,
    partialTotalHomologyFiltrationToStable, Category.assoc,
    Iso.hom_inv_id_assoc,
    stableIntervalStepToImage_comp_imageToStable]

/-- The stable quotient in current-image coordinates.

The current image comparison followed by the filtration quotient is the stable image-to-
interval map. -/
@[reassoc (attr := simp)]
theorem partialTotalStableStepImageFiltrationIso_hom_comp_toStable
    (n p : ℕ) :
    (B.partialTotalStableStepImageFiltrationIso n p).hom ≫
        B.partialTotalHomologyFiltrationToStable n p =
      B.partialTotalSpectralObject.stableIntervalImageToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) := by
  simp only [partialTotalHomologyFiltrationToStable,
    Iso.hom_inv_id_assoc]

/-- Vanishing of the preceding filtration image in the stable quotient.

The adjacent filtration inclusion followed by the projection to the stable interval object is
zero. -/
@[reassoc (attr := simp)]
theorem partialTotalHomologyFiltrationAdjacentHom_comp_toStable_zero
    (n p : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n p ≫
        B.partialTotalHomologyFiltrationToStable n p = 0 := by
  apply (cancel_epi
    (B.partialTotalStablePreviousImageFiltrationIso n p).hom).1
  rw [← Category.assoc,
    ← B.partialTotalStableImageMap_comp_currentIso_hom n p,
    Category.assoc,
    B.partialTotalStableStepImageFiltrationIso_hom_comp_toStable n p,
    stableIntervalImageMap_comp_imageToStable_zero, comp_zero]

/-- The cokernel property of an adjacent stable filtration quotient.

The filtration projection to the stable interval object is a colimit cofork of the preceding-
to-current filtration inclusion. -/
noncomputable def partialTotalHomologyFiltrationToStableIsCokernel
    (n p : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (B.partialTotalHomologyFiltrationToStable n p)
      (B.partialTotalHomologyFiltrationAdjacentHom_comp_toStable_zero n p)) :=
  IsCokernel.ofIso
    (f := B.partialTotalSpectralObject.stableIntervalImageMap
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p))
    (f' := B.partialTotalHomologyFiltrationAdjacentHom n p)
    (s := CokernelCofork.ofπ
      (B.partialTotalSpectralObject.stableIntervalImageToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p))
      (B.partialTotalSpectralObject.stableIntervalImageMap_comp_imageToStable_zero
          (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)))
    (B.partialTotalSpectralObject.stableIntervalImageToStableIsCokernel
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p))
    (CokernelCofork.ofπ
      (B.partialTotalHomologyFiltrationToStable n p)
      (B.partialTotalHomologyFiltrationAdjacentHom_comp_toStable_zero n p))
    (B.partialTotalStablePreviousImageFiltrationIso n p)
    (B.partialTotalStableStepImageFiltrationIso n p)
    (Iso.refl (B.partialTotalStableObj n p))
    (B.partialTotalStableImageMap_comp_currentIso_hom n p).symm
    (by
      change (B.partialTotalStableStepImageFiltrationIso n p).hom ≫
          B.partialTotalHomologyFiltrationToStable n p =
        B.partialTotalSpectralObject.stableIntervalImageToStable
            (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) ≫ 𝟙 _
      rw [Category.comp_id]
      exact B.partialTotalStableStepImageFiltrationIso_hom_comp_toStable n p)

/-- The stable-image cokernel as a partial-total graded quotient.

The current and preceding image comparisons identify the stable-image map's cokernel with the
adjacent partial-total homology graded piece. -/
noncomputable def partialTotalStableImageCokernelIsoGraded
    (n p : ℕ) :
    cokernel
        (B.partialTotalSpectralObject.stableIntervalImageMap
          (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)) ≅
      B.partialTotalHomologyGradedPiece n p :=
  cokernel.mapIso
    (f := B.partialTotalSpectralObject.stableIntervalImageMap
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p))
    (B.partialTotalHomologyFiltrationAdjacentHom n p)
    (B.partialTotalStablePreviousImageFiltrationIso n p)
    (B.partialTotalStableStepImageFiltrationIso n p)
    (B.partialTotalStableImageMap_comp_currentIso_hom n p)

/-- The projection formula for a stable-image graded comparison.

The stable-image cokernel projection followed by the graded isomorphism equals the current-
image comparison followed by the partial-total graded projection. -/
@[reassoc]
theorem stableIntervalCokernelπ_comp_partialTotalIso_hom
    (n p : ℕ) :
    cokernel.π
        (B.partialTotalSpectralObject.stableIntervalImageMap
          (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)) ≫
      (B.partialTotalStableImageCokernelIsoGraded n p).hom =
    (B.partialTotalStableStepImageFiltrationIso n p).hom ≫
      B.partialTotalHomologyGradedπ n p := by
  dsimp only [partialTotalStableImageCokernelIsoGraded]
  apply cokernel.π_desc

/-- The adjacent stable interval as a homology-filtration graded piece.

The stable interval object is canonically isomorphic to the cokernel of the preceding-to-
current partial-total homology filtration map. -/
noncomputable def partialTotalStableGradedIso (n p : ℕ) :
    B.partialTotalStableObj n p ≅
      B.partialTotalHomologyGradedPiece n p :=
  B.partialTotalSpectralObject.stableIntervalImageCokernelIso
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) ≪≫
    B.partialTotalStableImageCokernelIsoGraded n p

/-- The filtration projection under stable-to-graded comparison.

The filtration-to-stable map followed by the graded isomorphism equals the homology-filtration
graded projection. -/
@[reassoc]
theorem partialTotalHomologyFiltrationToStable_comp_stableGradedIso_hom
    (n p : ℕ) :
    B.partialTotalHomologyFiltrationToStable n p ≫
        (B.partialTotalStableGradedIso n p).hom =
      B.partialTotalHomologyGradedπ n p := by
  dsimp only [partialTotalHomologyFiltrationToStable,
    partialTotalStableGradedIso, Iso.trans_hom]
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [stableIntervalImageToStable_comp_iso_hom]
  slice_lhs 2 3 =>
    rw [B.stableIntervalCokernelπ_comp_partialTotalIso_hom n p]
  rw [Iso.inv_hom_id_assoc]

end HomologicalComplex₂

end
