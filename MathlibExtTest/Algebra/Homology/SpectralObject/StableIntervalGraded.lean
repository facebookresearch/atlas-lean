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

public import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalGraded
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.Single

/-!
# A stable interval with a proper image inclusion

The filtration on three cuts is zero, zero, and the cochain complex concentrated in degree
zero on Q. Its mapping-cone spectral object has a zero lower image and a nonzero upper image.
The stable quotient comparison computes on its actual nonzero generator. Equal cuts give a
zero quotient. All coefficient identifications come from zero-differential homology data.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open scoped ZeroObject

namespace MathlibExtTest.Algebra.Homology.SpectralObject.StableIntervalGraded

private abbrev C := ModuleCat ℚ
private abbrev Q := ModuleCat.of ℚ ℚ

private def single : CochainComplex C ℤ :=
  (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Q

private def zeroComplex : CochainComplex C ℤ := HomologicalComplex.zero

private def filtration : Fin 3 ⥤ CochainComplex C ℤ :=
  mk₂ (0 : zeroComplex ⟶ zeroComplex) (0 : zeroComplex ⟶ single)

private def Y : CategoryTheory.Abelian.SpectralObject C (Fin 3) :=
  ((HomotopyCategory.spectralObjectMappingCone C).precomp filtration).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)

private def cone (i : Fin 3) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (filtration.map (homOfLE (bot_le : (⊥ : Fin 3) ≤ i)))

private def stepIso (i : Fin 3) :
    Y.stableIntervalStep 0 i ≅ (cone i).homology 0 := by
  change ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).obj (cone i)) ≅ _
  exact (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) 0).app (cone i)

private theorem lowerConeZero (i : ℤ) : IsZero ((cone 1).X i) :=
  (CochainComplex.mappingCone.isZero_X_iff _ i).mpr ⟨isZero_zero C, isZero_zero C⟩

private theorem topConeMinusOneZero : IsZero ((cone 2).X (-1)) :=
  (CochainComplex.mappingCone.isZero_X_iff _ (-1)).mpr
    ⟨isZero_zero C,
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Q (-1) (by decide)⟩

private theorem topConeOneZero : IsZero ((cone 2).X 1) :=
  (CochainComplex.mappingCone.isZero_X_iff _ 1).mpr
    ⟨isZero_zero C,
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Q 1 (by decide)⟩

private def zeroH0Iso (K : CochainComplex C ℤ)
    (hm : IsZero (K.X (-1))) (hp : IsZero (K.X 1)) : K.homology 0 ≅ K.X 0 := by
  let h := ShortComplex.HomologyData.ofZeros (K.sc 0)
    (by
      change K.d ((ComplexShape.up ℤ).prev 0) 0 = 0
      rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by rfl)]
      exact hm.eq_of_src _ _)
    (by
      change K.d 0 ((ComplexShape.up ℤ).next 0) = 0
      rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 by rfl)]
      exact hp.eq_of_tgt _ _)
  exact h.left.homologyIso

private def topConeXIso : (cone 2).X 0 ≅ Q :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    (filtration.map (homOfLE (bot_le : (⊥ : Fin 3) ≤ (2 : Fin 3)))) 0 1 rfl ≪≫
    (isoZeroBiprod (isZero_zero C)).symm ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Q

private def topStepIso : Y.stableIntervalStep 0 2 ≅ Q :=
  stepIso 2 ≪≫ zeroH0Iso (cone 2) topConeMinusOneZero topConeOneZero ≪≫ topConeXIso

private theorem lowerStepZero : IsZero (Y.stableIntervalStep 0 1) :=
  IsZero.of_iso
    (IsZero.of_iso (lowerConeZero 0)
      (zeroH0Iso (cone 1) (lowerConeZero (-1)) (lowerConeZero 1))) (stepIso 1)

private theorem lowerImageZero : IsZero (Y.stableIntervalStepImage 0 1) := by
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (Y.stableIntervalStepToImage 0 1)).1
  simp only [Category.comp_id, comp_zero]
  exact lowerStepZero.eq_of_src _ _

private theorem strictImageMapZero : Y.stableIntervalImageMap 0 (show (1 : Fin 3) ≤ 2 by
    decide) = 0 := lowerImageZero.eq_of_src _ _

private theorem topStepToAbutment_id : Y.stableIntervalStepToAbutment 0 (2 : Fin 3) =
    𝟙 (Y.stableIntervalStep 0 2) := by
  change (Y.H 0).map (𝟙 (mk₁
    (CategoryTheory.Abelian.SpectralObject.stableIntervalFull (ι := Fin 3)))) = 𝟙 _
  exact (Y.H 0).map_id _

private instance topImageInclusionIsIso :
    IsIso (image.ι (Y.stableIntervalStepToAbutment 0 (2 : Fin 3))) := by
  let _ : Epi (Y.stableIntervalStepToAbutment 0 (2 : Fin 3)) := by
    refine ⟨fun g h w => ?_⟩
    rw [topStepToAbutment_id] at w
    exact (Category.id_comp g).symm.trans (w.trans (Category.id_comp h))
  let _ : Epi (image.ι (Y.stableIntervalStepToAbutment 0 (2 : Fin 3))) :=
    epi_image_of_epi (Y.stableIntervalStepToAbutment 0 (2 : Fin 3))
  exact isIso_of_mono_of_epi (image.ι (Y.stableIntervalStepToAbutment 0 (2 : Fin 3)))

private def topImageIso : Y.stableIntervalStepImage 0 2 ≅ Q :=
  asIso (image.ι (Y.stableIntervalStepToAbutment 0 (2 : Fin 3))) ≪≫ topStepIso

private def strictQuotientIso :
    cokernel (Y.stableIntervalImageMap 0 (show (1 : Fin 3) ≤ 2 by decide)) ≅ Q :=
  cokernelIsoOfEq strictImageMapZero ≪≫ cokernelZeroIsoTarget ≪≫ topImageIso

private def stableIso : Y.stableIntervalObj 0 (show (1 : Fin 3) ≤ 2 by decide) ≅ Q :=
  Y.stableIntervalImageCokernelIso 0 (show (1 : Fin 3) ≤ 2 by decide) ≪≫ strictQuotientIso

private def imageOne : Y.stableIntervalStepImage 0 2 := topImageIso.inv.hom (1 : ℚ)

private def quotientOne : Y.stableIntervalObj 0 (show (1 : Fin 3) ≤ 2 by decide) :=
  stableIso.inv.hom (1 : ℚ)

example : quotientOne ≠ 0 := by
  intro h
  have he := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) stableIso.inv_hom_id
  have h1 : stableIso.hom.hom quotientOne = (1 : ℚ) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, quotientOne,
      ModuleCat.hom_id, LinearMap.id_apply] using he
  rw [h, map_zero] at h1
  exact zero_ne_one h1

example :
    (stableIso.hom).hom
      ((Y.stableIntervalImageToStable 0 (show (1 : Fin 3) ≤ 2 by decide)).hom imageOne) =
      (1 : ℚ) := by
  have hπ : cokernel.π
      (Y.stableIntervalImageMap 0 (show (1 : Fin 3) ≤ 2 by decide)) ≫
      strictQuotientIso.hom = topImageIso.hom := by
    simp only [strictQuotientIso, Iso.trans_hom, Category.assoc,
      π_comp_cokernelIsoOfEq_hom_assoc, cokernelZeroIsoTarget_hom,
      cokernel.π_desc_assoc, Category.id_comp]
  have hq : Y.stableIntervalImageToStable 0 (show (1 : Fin 3) ≤ 2 by decide) ≫
      stableIso.hom = topImageIso.hom := by
    change Y.stableIntervalImageToStable 0 (show (1 : Fin 3) ≤ 2 by decide) ≫
      (Y.stableIntervalImageCokernelIso 0 (show (1 : Fin 3) ≤ 2 by decide)).hom ≫
        strictQuotientIso.hom = topImageIso.hom
    rw [Y.stableIntervalImageToStable_comp_iso_hom_assoc, hπ]
  have hc := congrArg (fun f => f.hom imageOne) hq
  have h1 : topImageIso.hom.hom imageOne = (1 : ℚ) := by
    have he := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) topImageIso.inv_hom_id
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, imageOne,
      ModuleCat.hom_id, LinearMap.id_apply] using he
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hc.trans h1

example : IsZero (Y.stableIntervalObj 0 (show (2 : Fin 3) ≤ 2 by decide)) := by
  have hj : Y.stableIntervalImageMap 0 (show (2 : Fin 3) ≤ 2 by decide) = 𝟙 _ := by
    apply (cancel_mono (image.ι (Y.stableIntervalStepToAbutment 0 (2 : Fin 3)))).1
    rw [Y.stableIntervalImageMap_comp_ι, Category.id_comp]
  let _ : Epi (Y.stableIntervalImageMap 0 (show (2 : Fin 3) ≤ 2 by decide)) := by
    rw [hj]
    infer_instance
  exact IsZero.of_iso (isZero_cokernel_of_epi _)
    (Y.stableIntervalImageCokernelIso 0 (show (2 : Fin 3) ≤ 2 by decide))

end MathlibExtTest.Algebra.Homology.SpectralObject.StableIntervalGraded
