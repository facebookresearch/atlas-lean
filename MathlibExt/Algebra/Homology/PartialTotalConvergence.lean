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
# Stable intervals and graded pieces for the partial-total filtration

This file transports the generic stable-interval/image-cokernel comparison to
the increasing partial-total homology filtration.  It makes no spectral-page
or convergence claim.
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

/-- The canonical stable-interval abutment object is ordinary total homology
for the partial-total spectral object. -/
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

/-- The generic selected spectral image at a finite stage, identified with
the corresponding partial-total homology filtration step. -/
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

/-- The finite selected-image coordinate commutes with inclusion into total
homology. -/
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

/-- The spectral step at the predecessor of filtration degree zero is zero. -/
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

/-- The selected spectral image at the predecessor of filtration degree zero
is zero. -/
theorem isZero_partialTotalStablePreviousImage_zero (n : ℕ) :
    IsZero (B.partialTotalSpectralObject.stableIntervalStepImage
      (-(n : ℤ)) (((-1 : ℤ) : EInt))) :=
  IsZero.of_epi
    (Limits.factorThruImage
      (B.partialTotalSpectralObject.stableIntervalStepToAbutment
        (-(n : ℤ)) (((-1 : ℤ) : EInt))))
    (B.isZero_partialTotalStablePreviousStep_zero n)

/-- The generic previous selected image is the predecessor partial-total
homology filtration step. -/
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

/-- The previous selected-image coordinate commutes with inclusion into total
homology. -/
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

/-- The generic ordered image map is the adjacent partial-total homology
filtration map in the selected image coordinates. -/
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

/-- The direct stable interval for the partial-total filtration. -/
noncomputable abbrev partialTotalStableObj (n p : ℕ) : C :=
  B.partialTotalSpectralObject.stableIntervalObj
    (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)

/-- The bottom-to-stage spectral step mapped onto the finite homology
filtration step. -/
noncomputable def partialTotalSpectralStepToFiltration (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStep
        (-(n : ℤ)) ((p : ℤ) : EInt) ⟶
      (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) :=
  B.partialTotalSpectralObject.stableIntervalStepToImage
      (-(n : ℤ)) ((p : ℤ) : EInt) ≫
    (B.partialTotalStableStepImageFiltrationIso n p).hom

/-- A finite spectral step followed through its selected homology filtration
is ordinary homology of the partial-total inclusion. -/
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

/-- The finite homology filtration step maps canonically to its stable
interval. -/
noncomputable def partialTotalHomologyFiltrationToStable (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ⟶
      B.partialTotalStableObj n p :=
  (B.partialTotalStableStepImageFiltrationIso n p).inv ≫
    B.partialTotalSpectralObject.stableIntervalImageToStable
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p)

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

@[reassoc (attr := simp)]
theorem partialTotalStableStepImageFiltrationIso_hom_comp_toStable
    (n p : ℕ) :
    (B.partialTotalStableStepImageFiltrationIso n p).hom ≫
        B.partialTotalHomologyFiltrationToStable n p =
      B.partialTotalSpectralObject.stableIntervalImageToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) := by
  simp only [partialTotalHomologyFiltrationToStable,
    Iso.hom_inv_id_assoc]

/-- The adjacent homology filtration map followed by the stable quotient is
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

/-- The partial-total stable quotient is a cokernel of the adjacent homology
filtration map. -/
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

/-- The generic selected-image cokernel identifies with the adjacent
partial-total homology graded piece. -/
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

/-- The generic image-cokernel quotient becomes the partial-total graded
quotient in the selected image coordinates. -/
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

/-- The partial-total stable interval is canonically the adjacent homology
graded piece. -/
noncomputable def partialTotalStableGradedIso (n p : ℕ) :
    B.partialTotalStableObj n p ≅
      B.partialTotalHomologyGradedPiece n p :=
  B.partialTotalSpectralObject.stableIntervalImageCokernelIso
      (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) ≪≫
    B.partialTotalStableImageCokernelIsoGraded n p

/-- The stable/graded isomorphism identifies the stable quotient with the
canonical adjacent graded quotient. -/
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
