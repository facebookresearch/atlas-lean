/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient
import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
import Mathlib.Algebra.Homology.Single
import Mathlib.Data.ZMod.Basic
public meta import Lean.Elab.Tactic.Omega

/-!
# Positive pairing quotients over the ring of six elements

Both source complexes have the lifted regular module of ZMod 6 in degree
one, and the target has that module in degree two. The pairing is twice
tensor multiplication. Its degree-two image is 2R, its kernel contains the
nonzero tensor represented by 3 ⊗ 1, and the quotient class of 1 survives.

The smart-positive cokernel, strict-positive cokernel and component-image
quotient give the same nonzero class through their canonical projection
comparisons. Multiplication by 3 detects it. A nonidentity scalar-five
morphism of pairings also preserves the comparison square.
The scalar ring is in Type 0 and the coefficient modules are in Type 1.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.ChainGradedPairing
open scoped TensorProduct MonoidalCategory ModuleCat.UniverseTensor

namespace PositivePairingQuotientComparisonTests

private abbrev R := ZMod 6
private abbrev U := ULift.{1} R
private abbrev C := ModuleCat.{1} R
private abbrev shape := ComplexShape.down ℕ

local instance : MonoidalCategoryStruct C :=
  ModuleCat.UniverseTensor.tensorStructure.{0, 1} (R := R)

local instance : MonoidalCategory C :=
  ModuleCat.UniverseTensor.monoidalCategory.{0, 1} (R := R)

local instance : MonoidalPreadditive C :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{0, 1} (R := R)

private abbrev coefficient : C := ModuleCat.of R U

private def source : ChainComplex C ℕ :=
  (HomologicalComplex.single C shape 1).obj coefficient

private def target : ChainComplex C ℕ :=
  (HomologicalComplex.single C shape 2).obj coefficient

private def sourceCoordinate : source.X 1 ≅ coefficient :=
  HomologicalComplex.singleObjXSelf shape 1 coefficient

private def targetCoordinate : target.X 2 ≅ coefficient :=
  HomologicalComplex.singleObjXSelf shape 2 coefficient

private def sourceValue (r : R) : source.X 1 :=
  sourceCoordinate.inv.hom (ULift.up r : U)

private def targetValue (r : R) : target.X 2 :=
  targetCoordinate.inv.hom (ULift.up r : U)

private lemma sourceCoordinate_value (r : R) :
    sourceCoordinate.hom.hom (sourceValue r) = (ULift.up r : U) := by
  simpa only [sourceValue, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using
    ConcreteCategory.congr_hom sourceCoordinate.inv_hom_id (ULift.up r : U)

private lemma targetCoordinate_value (r : R) :
    targetCoordinate.hom.hom (targetValue r) = (ULift.up r : U) := by
  simpa only [targetValue, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using
    ConcreteCategory.congr_hom targetCoordinate.inv_hom_id (ULift.up r : U)

private lemma sourceValue_surjective : Function.Surjective sourceValue := by
  intro x
  refine ⟨(sourceCoordinate.hom.hom x).down, ?_⟩
  change sourceCoordinate.inv.hom
    (ULift.up ((sourceCoordinate.hom.hom x).down)) = x
  exact ConcreteCategory.congr_hom sourceCoordinate.hom_inv_id x

private lemma targetValue_ne_zero {r : R} (hr : r ≠ 0) :
    targetValue r ≠ 0 := by
  intro h
  have hh := congrArg targetCoordinate.hom.hom h
  rw [targetCoordinate_value, map_zero] at hh
  exact hr (congrArg ULift.down hh)

private lemma targetValue_injective : Function.Injective targetValue := by
  intro r s h
  have hh := congrArg targetCoordinate.hom.hom h
  rw [targetCoordinate_value, targetCoordinate_value] at hh
  exact congrArg ULift.down hh

@[simp] private lemma source_d (i j : ℕ) : source.d i j = 0 := rfl

private lemma tensor_d (n : ℕ) :
    (HomologicalComplex.tensorObj source source).d (n + 1) n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := source) (K₂ := source) (F := curriedTensor C) (c := shape)
  intro p q h
  change ιTensorObj source source p q (n + 1) h ≫
      (HomologicalComplex.tensorObj source source).d (n + 1) n =
    ιTensorObj source source p q (n + 1) h ≫ 0
  rw [ιTensorObj_comp_d_down_nat source source p q n h]
  simp [source_d]

private def product (c : R) : coefficient ⊗ coefficient ⟶ coefficient :=
  ModuleCat.ofHom (c • (λ_ coefficient).hom.hom)

private lemma product_tmul (c r s : R) :
    (product c).hom ((ULift.up r : U) ⊗ₜ[R] (ULift.up s : U)) =
      (ULift.up (c * (r * s)) : U) := by
  change c • ((TensorProduct.lid R U)
    ((TensorProduct.congr (ULift.moduleEquiv : U ≃ₗ[R] R)
      (LinearEquiv.refl R U)) ((ULift.up r : U) ⊗ₜ[R] (ULift.up s : U)))) = _
  rw [TensorProduct.congr_tmul, TensorProduct.lid_tmul]
  rfl

private def component (c : R) (p q : ℕ) (_h : p + q = 2) :
    source.X p ⊗ source.X q ⟶ coefficient :=
  if hp : p = 1 then
    if hq : q = 1 then
      ((HomologicalComplex.singleObjXIsoOfEq shape 1 coefficient p hp).hom ⊗ₘ
        (HomologicalComplex.singleObjXIsoOfEq shape 1 coefficient q hq).hom) ≫ product c
    else 0
  else 0

private def totalComponent (c : R) :
    (HomologicalComplex.tensorObj source source).X 2 ⟶ coefficient :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := source) (K₂ := source) (F := curriedTensor C) (c := shape) (component c)

private def pairing (c : R) : ChainGradedPairing source source target :=
  HomologicalComplex.mkHomToSingle (totalComponent c) (by
    intro i hi
    change 2 + 1 = i at hi
    subst i
    rw [tensor_d, zero_comp])

private lemma pairing_pairAt (c : R) (p q : ℕ) (h : p + q = 2) :
    pairAt (pairing c) p q 2 h = component c p q h ≫ targetCoordinate.inv := by
  rw [pairAt, pairing, HomologicalComplex.mkHomToSingle_f]
  change ιMapBifunctor source source (curriedTensor C) shape p q 2 h ≫
      (totalComponent c ≫ targetCoordinate.inv) = _
  rw [← Category.assoc, totalComponent, HomologicalComplex.ι_mapBifunctorDesc]

private lemma pairing_pairAt_one (c : R) :
    pairAt (pairing c) 1 1 2 rfl =
      (MonoidalCategory.tensorIso sourceCoordinate sourceCoordinate).hom ≫
        product c ≫ targetCoordinate.inv := by
  rw [pairing_pairAt]
  simp only [component, dite_eq_left rfl]
  rfl

private lemma pairing_pairAt_value (c r s : R) :
    (pairAt (pairing c) 1 1 2 rfl).hom
        (sourceValue r ⊗ₜ[R] sourceValue s) = targetValue (c * (r * s)) := by
  rw [pairing_pairAt_one]
  change targetCoordinate.inv.hom
      ((product c).hom (TensorProduct.map sourceCoordinate.hom.hom
        sourceCoordinate.hom.hom (sourceValue r ⊗ₜ[R] sourceValue s))) = _
  rw [TensorProduct.map_tmul, sourceCoordinate_value, sourceCoordinate_value,
    product_tmul]
  rfl

private def tensorValue (r s : R) :
    (HomologicalComplex.tensorObj source source).X 2 :=
  (ιTensorObj source source 1 1 2 rfl).hom (sourceValue r ⊗ₜ[R] sourceValue s)

private lemma pairing_value (c r s : R) :
    ((pairing c).f 2).hom (tensorValue r s) = targetValue (c * (r * s)) := by
  change (pairAt (pairing c) 1 1 2 rfl).hom
    (sourceValue r ⊗ₜ[R] sourceValue s) = _
  exact pairing_pairAt_value c r s

private def pairCoordinate : source.X 1 ⊗ source.X 1 ≅ target.X 2 :=
  MonoidalCategory.tensorIso sourceCoordinate sourceCoordinate ≪≫
    (λ_ coefficient) ≪≫ targetCoordinate.symm

private def scale (c : R) : target.X 2 →ₗ[R] target.X 2 :=
  c • LinearMap.id

private lemma scale_value (c r : R) :
    scale c (targetValue r) = targetValue (c * r) := by
  change c • targetCoordinate.inv.hom (ULift.up r : U) =
    targetCoordinate.inv.hom (ULift.up (c * r) : U)
  rw [← map_smul]
  rfl

private lemma pairing_pairAt_scale (c : R) :
    (pairAt (pairing c) 1 1 2 rfl).hom =
      (scale c).comp pairCoordinate.hom.hom := by
  rw [pairing_pairAt_one]
  change targetCoordinate.inv.hom.comp
      ((c • (λ_ coefficient).hom.hom).comp
        (MonoidalCategory.tensorIso sourceCoordinate sourceCoordinate).hom.hom) =
    (c • LinearMap.id).comp
      (targetCoordinate.inv.hom.comp ((λ_ coefficient).hom.hom.comp
        (MonoidalCategory.tensorIso sourceCoordinate sourceCoordinate).hom.hom))
  simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp]

private lemma positiveImages_two :
    positiveImages (pairing 2) 2 =
      LinearMap.range (pairAt (pairing 2) 1 1 2 rfl).hom := by
  apply le_antisymm
  · rw [positiveImages]
    apply iSup_le
    rintro ⟨⟨p, q⟩, hp, hq, hn⟩
    have hp1 : p = 1 := by omega
    have hq1 : q = 1 := by omega
    subst p
    subst q
    exact le_rfl
  · rintro z ⟨x, rfl⟩
    exact pairAt_mem_positiveImages (pairing 2) 1 1 2 rfl
      (by decide) (by decide) x

private lemma relations_two :
    positiveImages (pairing 2) 2 = LinearMap.range (scale 2) := by
  rw [positiveImages_two, pairing_pairAt_scale]
  have hs : Function.Surjective pairCoordinate.hom.hom :=
    pairCoordinate.toLinearEquiv.surjective
  apply le_antisymm
  · rintro z ⟨x, hx⟩
    exact ⟨pairCoordinate.hom.hom x, hx⟩
  · rintro z ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hs y
    refine ⟨x, ?_⟩
    rw [LinearMap.comp_apply, hx]
    exact hy

private abbrev inputBoundaryZero : source.d 1 0 = 0 := by rfl
private abbrev positiveEmbedding := ChainComplex.kernelTailEmbedding
private abbrev smartQuotient :=
  truncationQuotient positiveEmbedding (pairing 2)
private abbrev strictQuotient :=
  strictPositiveCokernel (pairing 2) inputBoundaryZero inputBoundaryZero
private abbrev imageQuotient :=
  positiveImageQuotient (pairing 2) inputBoundaryZero inputBoundaryZero
private abbrev smartToStrict :=
  truncationQuotientIsoStrictPositiveCokernel (pairing 2) inputBoundaryZero inputBoundaryZero
private abbrev strictToImage :=
  strictPositiveCokernelIsoPositiveImageQuotient (pairing 2) inputBoundaryZero inputBoundaryZero
private abbrev smartToImage :=
  truncationQuotientIsoPositiveImageQuotient (pairing 2) inputBoundaryZero inputBoundaryZero

private def smartClass (r : R) : smartQuotient.X 2 :=
  ((truncationProjection positiveEmbedding (pairing 2)).f 2).hom (targetValue r)

private def strictClass (r : R) : strictQuotient.X 2 :=
  ((strictPositiveProjection (pairing 2) inputBoundaryZero inputBoundaryZero).f 2).hom
    (targetValue r)

private def imageClass (r : R) : imageQuotient.X 2 :=
  ((positiveImageProjection (pairing 2) inputBoundaryZero inputBoundaryZero).f 2).hom
    (targetValue r)

private lemma relation_le_kernel_three :
    positiveImages (pairing 2) 2 ≤ LinearMap.ker (scale 3) := by
  rw [relations_two]
  rintro z ⟨y, rfl⟩
  change (3 : R) • ((2 : R) • y) = 0
  rw [smul_smul]
  have h : (3 : R) * 2 = 0 := by decide
  rw [h, zero_smul]

private def detector : imageQuotient.X 2 →ₗ[R] target.X 2 :=
  (positiveImages (pairing 2) 2).liftQ (scale 3) relation_le_kernel_three

private lemma detector_imageClass (r : R) :
    detector (imageClass r) = targetValue (3 * r) := by
  have h := DFunLike.congr_fun
    (Submodule.liftQ_mkQ (positiveImages (pairing 2) 2)
      (scale 3) relation_le_kernel_three) (targetValue r)
  exact h.trans (scale_value 3 r)

private lemma imageClass_even (r : R) : imageClass (2 * r) = 0 := by
  have hx : targetValue (2 * r) ∈ positiveImages (pairing 2) 2 := by
    rw [relations_two]
    exact ⟨targetValue r, scale_value 2 r⟩
  have hk : targetValue (2 * r) ∈
      LinearMap.ker (positiveImages (pairing 2) 2).mkQ := by
    rw [Submodule.ker_mkQ]
    exact hx
  exact hk

private lemma imageClass_one_ne_zero : imageClass 1 ≠ 0 := by
  intro h
  have hh := congrArg detector h
  rw [detector_imageClass, map_zero, mul_one] at hh
  exact targetValue_ne_zero (by decide : (3 : R) ≠ 0) hh

private lemma smart_strict_value (r : R) :
    (smartToStrict.hom.f 2).hom (smartClass r) = strictClass r := by
  have h := congrArg (fun f : target ⟶ strictQuotient => (f.f 2).hom (targetValue r))
    (truncationProjection_isoStrictPositive_hom (pairing 2) inputBoundaryZero inputBoundaryZero)
  simpa only [smartClass, strictClass, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply] using h

private lemma strict_image_value (r : R) :
    (strictToImage.hom.f 2).hom (strictClass r) = imageClass r := by
  have h := congrArg (fun f : target ⟶ imageQuotient => (f.f 2).hom (targetValue r))
    (strictPositiveProjection_isoPositiveImage_hom (pairing 2)
      inputBoundaryZero inputBoundaryZero)
  simpa only [strictClass, imageClass, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply] using h

private lemma smart_image_value (r : R) :
    (smartToImage.hom.f 2).hom (smartClass r) = imageClass r := by
  have h := congrArg (fun f : target ⟶ imageQuotient => (f.f 2).hom (targetValue r))
    (truncationProjection_isoPositiveImage_hom (pairing 2)
      inputBoundaryZero inputBoundaryZero)
  simpa only [smartClass, imageClass, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply] using h

private lemma image_strict_value (r : R) :
    (strictToImage.inv.f 2).hom (imageClass r) = strictClass r := by
  have h := congrArg (fun f : target ⟶ strictQuotient => (f.f 2).hom (targetValue r))
    (positiveImageProjection_isoStrictPositive_inv (pairing 2)
      inputBoundaryZero inputBoundaryZero)
  simpa only [strictClass, imageClass, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply] using h

private lemma strict_smart_value (r : R) :
    (smartToStrict.inv.f 2).hom (strictClass r) = smartClass r := by
  have h := congrArg (fun f : target ⟶ smartQuotient => (f.f 2).hom (targetValue r))
    (strictPositiveProjection_isoTruncation_inv (pairing 2)
      inputBoundaryZero inputBoundaryZero)
  simpa only [smartClass, strictClass, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply] using h

private lemma strictClass_one_ne_zero : strictClass 1 ≠ 0 := by
  intro h
  have hh := congrArg (strictToImage.hom.f 2).hom h
  rw [strict_image_value, map_zero] at hh
  exact imageClass_one_ne_zero hh

private lemma smartClass_one_ne_zero : smartClass 1 ≠ 0 := by
  intro h
  have hh := congrArg (smartToImage.hom.f 2).hom h
  rw [smart_image_value, map_zero] at hh
  exact imageClass_one_ne_zero hh

private lemma strictClass_two_zero : strictClass 2 = 0 := by
  have h := image_strict_value 2
  have hz : imageClass 2 = 0 := by simpa using imageClass_even 1
  rw [hz, map_zero] at h
  exact h.symm

private lemma smartClass_two_zero : smartClass 2 = 0 := by
  have h := strict_smart_value 2
  rw [strictClass_two_zero, map_zero] at h
  exact h.symm

private def sourceFive : source ⟶ source :=
  (HomologicalComplex.single C shape 1).map
    (ModuleCat.ofHom ((5 : R) • (LinearMap.id : U →ₗ[R] U)))

private def targetFive : target ⟶ target :=
  (HomologicalComplex.single C shape 2).map
    (ModuleCat.ofHom ((5 : R) • (LinearMap.id : U →ₗ[R] U)))

private lemma sourceFive_value (r : R) :
    (sourceFive.f 1).hom (sourceValue r) = sourceValue (5 * r) := by
  rw [sourceFive, HomologicalComplex.single_map_f_self]
  change sourceCoordinate.inv.hom
    ((5 : R) • sourceCoordinate.hom.hom (sourceValue r)) = _
  rw [sourceCoordinate_value]
  rfl

private lemma targetFive_value (r : R) :
    (targetFive.f 2).hom (targetValue r) = targetValue (5 * r) := by
  rw [targetFive, HomologicalComplex.single_map_f_self]
  change targetCoordinate.inv.hom
    ((5 : R) • targetCoordinate.hom.hom (targetValue r)) = _
  rw [targetCoordinate_value]
  rfl

private lemma pairing_five :
    tensorHom sourceFive (𝟙 source) ≫ pairing 2 = pairing 2 ≫ targetFive := by
  apply HomologicalComplex.to_single_hom_ext
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := source) (K₂ := source) (F := curriedTensor C) (c := shape)
  intro p q h
  change ιTensorObj source source p q 2 h ≫
      ((tensorHom sourceFive (𝟙 source)).f 2 ≫ (pairing 2).f 2) =
    ιTensorObj source source p q 2 h ≫
      ((pairing 2).f 2 ≫ targetFive.f 2)
  rw [← Category.assoc, ιTensorObj_tensorHom, Category.assoc]
  change (sourceFive.f p ⊗ₘ 𝟙 (source.X q)) ≫
      pairAt (pairing 2) p q 2 h =
    pairAt (pairing 2) p q 2 h ≫ targetFive.f 2
  by_cases hp : p = 1
  · subst p
    by_cases hq : q = 1
    · subst q
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      intro x y
      obtain ⟨r, rfl⟩ := sourceValue_surjective x
      obtain ⟨s, rfl⟩ := sourceValue_surjective y
      change (pairAt (pairing 2) 1 1 2 rfl).hom
          (TensorProduct.map (sourceFive.f 1).hom LinearMap.id
            (sourceValue r ⊗ₜ[R] sourceValue s)) =
        (targetFive.f 2).hom
          ((pairAt (pairing 2) 1 1 2 rfl).hom (sourceValue r ⊗ₜ[R] sourceValue s))
      rw [TensorProduct.map_tmul, sourceFive_value, LinearMap.id_apply,
        pairing_pairAt_value, pairing_pairAt_value, targetFive_value]
      congr 1
      simp only [mul_assoc]
      exact mul_left_comm (2 : R) 5 (r * s)
    · simp [pairing_pairAt, component, hq]
  · simp [pairing_pairAt, component, hp]

private def imageMapFive : imageQuotient ⟶ imageQuotient :=
  positiveImageQuotientMap (pairing 2) inputBoundaryZero inputBoundaryZero
    (pairing 2) inputBoundaryZero inputBoundaryZero sourceFive (𝟙 source)
    targetFive pairing_five

private def smartMapFive : smartQuotient ⟶ smartQuotient :=
  truncationQuotientMap positiveEmbedding (pairing 2) (pairing 2)
    sourceFive (𝟙 source) targetFive pairing_five

private lemma imageMapFive_value (r : R) :
    (imageMapFive.f 2).hom (imageClass r) = imageClass (5 * r) := by
  have h := congrArg (fun f : target ⟶ imageQuotient => (f.f 2).hom (targetValue r))
    (positiveImageProjection_map (pairing 2) inputBoundaryZero inputBoundaryZero
      (pairing 2) inputBoundaryZero inputBoundaryZero sourceFive (𝟙 source)
      targetFive pairing_five)
  change (imageMapFive.f 2).hom (imageClass r) =
    ((positiveImageProjection (pairing 2) inputBoundaryZero inputBoundaryZero).f 2).hom
      ((targetFive.f 2).hom (targetValue r)) at h
  rw [targetFive_value] at h
  exact h

private lemma imageClass_five : imageClass 5 = imageClass 1 := by
  apply sub_eq_zero.mp
  change ((positiveImageProjection (pairing 2) inputBoundaryZero inputBoundaryZero).f 2).hom
      (targetValue 5) -
    ((positiveImageProjection (pairing 2) inputBoundaryZero inputBoundaryZero).f 2).hom
      (targetValue 1) = 0
  rw [← map_sub]
  have hv : targetValue 5 - targetValue 1 = targetValue (5 - 1) := by
    change targetCoordinate.inv.hom (ULift.up (5 : R)) -
      targetCoordinate.inv.hom (ULift.up (1 : R)) =
        targetCoordinate.inv.hom (ULift.up ((5 : R) - 1))
    rw [← map_sub]
    rfl
  rw [hv]
  have h : (5 : R) - 1 = 2 * 2 := by decide
  rw [h]
  exact imageClass_even 2

example :
    ((pairing 2).f 2).hom (tensorValue 1 1) = targetValue 2 ∧
      targetValue 2 ≠ 0 := by
  constructor
  · simpa using pairing_value 2 1 1
  · exact targetValue_ne_zero (by decide)

example :
    tensorValue 3 1 ≠ 0 ∧ ((pairing 2).f 2).hom (tensorValue 3 1) = 0 := by
  constructor
  · intro h
    have hh := congrArg ((pairing 1).f 2).hom h
    rw [pairing_value, map_zero, one_mul, mul_one] at hh
    exact targetValue_ne_zero (by decide : (3 : R) ≠ 0) hh
  · have h : (2 : R) * (3 * 1) = 0 := by decide
    rw [pairing_value, h]
    simp [targetValue]

example :
    LinearMap.range ((strictPositivePairing (pairing 2)
      inputBoundaryZero inputBoundaryZero).f 2).hom =
      LinearMap.range (scale 2) := by
  rw [range_strictPositivePairing, relations_two]

example :
    detector (imageClass 1) = targetValue 3 ∧ detector (imageClass 1) ≠ 0 := by
  constructor
  · simpa using detector_imageClass 1
  · rw [detector_imageClass, mul_one]
    exact targetValue_ne_zero (by decide)

example : imageClass 1 ≠ 0 ∧ imageClass 2 = 0 := by
  exact ⟨imageClass_one_ne_zero, by simpa using imageClass_even 1⟩

example : (smartToStrict.hom.f 2).hom (smartClass 1) = strictClass 1 :=
  smart_strict_value 1

example : (strictToImage.hom.f 2).hom (strictClass 1) = imageClass 1 :=
  strict_image_value 1

example :
    (smartToImage.hom.f 2).hom (smartClass 1) = imageClass 1 ∧
      (strictToImage.hom.f 2).hom
        ((smartToStrict.hom.f 2).hom (smartClass 1)) = imageClass 1 := by
  exact ⟨smart_image_value 1, by rw [smart_strict_value, strict_image_value]⟩

example : (strictToImage.inv.f 2).hom (imageClass 1) = strictClass 1 :=
  image_strict_value 1

example : (smartToStrict.inv.f 2).hom (strictClass 1) = smartClass 1 :=
  strict_smart_value 1

example : smartClass 1 ≠ 0 ∧ strictClass 1 ≠ 0 ∧ imageClass 1 ≠ 0 :=
  ⟨smartClass_one_ne_zero, strictClass_one_ne_zero, imageClass_one_ne_zero⟩

example : smartClass 2 = 0 ∧ strictClass 2 = 0 ∧ imageClass 2 = 0 :=
  ⟨smartClass_two_zero, strictClass_two_zero, by simpa using imageClass_even 1⟩

example :
    (smartToImage.hom.f 2).hom ((smartMapFive.f 2).hom (smartClass 1)) = imageClass 1 ∧
      (imageMapFive.f 2).hom (imageClass 1) = imageClass 1 ∧
      (targetFive.f 2).hom (targetValue 1) ≠ targetValue 1 := by
  have h := congrArg
    (fun f : smartQuotient ⟶ imageQuotient => (f.f 2).hom (smartClass 1))
    (truncationQuotientIsoPositiveImageQuotient_naturality
      (pairing 2) inputBoundaryZero inputBoundaryZero
      (pairing 2) inputBoundaryZero inputBoundaryZero
      sourceFive (𝟙 source) targetFive pairing_five)
  have himage : (imageMapFive.f 2).hom (imageClass 1) = imageClass 1 := by
    rw [imageMapFive_value, mul_one, imageClass_five]
  refine ⟨?_, himage, ?_⟩
  · change (smartToImage.hom.f 2).hom ((smartMapFive.f 2).hom (smartClass 1)) =
      (imageMapFive.f 2).hom ((smartToImage.hom.f 2).hom (smartClass 1)) at h
    rw [smart_image_value, himage] at h
    exact h
  · rw [targetFive_value, mul_one]
    intro heq
    exact (by decide : (5 : R) ≠ 1) (targetValue_injective heq)

end PositivePairingQuotientComparisonTests
