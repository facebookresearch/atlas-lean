/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.Connecting
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An integral cycles/image connecting square with nonflat coefficients

The right complex has integers squared in degree zero, integers in degree minus
one, and differential (a,b) ↦ 2a. Its terms and images are projective. The left
complex is ZMod 2 in degree zero. The full image-tensor homology has a nonzero
canonical class, and the general connecting square applies with these nonflat
left coefficients.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex ChainComplex.BalancedTensor
open scoped TensorProduct

namespace MathlibExtTest.BalancedTensorConnecting

private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ
private abbrev Zsq : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ (ℤ × ℤ)
private abbrev Z2 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)

private def rightEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rightBasis : Basis PUnit ℤᵐᵒᵖ ℤ :=
  (Basis.singleton PUnit ℤᵐᵒᵖ).map rightEquiv

private instance Z_projective : Projective Z := ModuleCat.projective_of_free rightBasis

private instance Zsq_projective : Projective Zsq :=
  ModuleCat.projective_of_free (rightBasis.prod rightBasis)

private def twiceFirst : Zsq ⟶ Z := ModuleCat.ofHom
  { toFun := fun x => 2 * x.1
    map_add' := fun x y => by change 2 * (x.1 + y.1) = _; ring
    map_smul' := fun r x => by
      change 2 * (x.1 * r.unop) = (2 * x.1) * r.unop
      ring }

private def X (i : ℤ) : ModuleCat.{0} ℤᵐᵒᵖ :=
  if i = 0 then Zsq else if i = -1 then Z else 0

private def d (i : ℤ) : X (i + 1) ⟶ X i :=
  if hi : i = -1 then by subst i; exact twiceFirst else 0

private theorem d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases hi : i = -1
  · subst i
    rw [show d ((-1 : ℤ) + 1) = 0 by simp [d]]
    exact zero_comp
  · rw [show d i = 0 by simp [d, hi]]
    exact comp_zero

private def P : ChainComplex (ModuleCat.{0} ℤᵐᵒᵖ) ℤ := ChainComplex.of X d d_sq

private def Q : ChainComplex (ModuleCat.{0} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} ℤ) (ComplexShape.down ℤ) 0).obj Z2

theorem original_differential (a b : ℤ) : (P.d 0 (-1)).hom (a, b) = 2 * a := by
  change (ChainComplex.of.d X d ((-1 : ℤ) + 1) (-1)).hom (a, b) = _
  rw [ChainComplex.of_d]
  simp only [d, dif_pos rfl]
  rfl

private theorem next_int (i : ℤ) : (ComplexShape.down ℤ).next i = i - 1 :=
  (ComplexShape.down ℤ).next_eq' (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private theorem P_d_zero_negOne : P.d 0 (-1) = twiceFirst := by
  change ChainComplex.of.d X d ((-1 : ℤ) + 1) (-1) = _
  rw [ChainComplex.of_d]
  simp [d]

private def imageArrowIso (j : ℤ) (hj : j = -1) :
    Arrow.mk (P.d 0 j) ≅ Arrow.mk twiceFirst := by
  subst j
  rw [P_d_zero_negOne]
  exact Iso.refl _

private def imageDegreeIso : connectingImages ℤ P 0 ≅ Abelian.image twiceFirst :=
  (Abelian.im (C := ModuleCat.{0} ℤᵐᵒᵖ)).mapIso
    (imageArrowIso ((ComplexShape.down ℤ).next 0) (next_int 0))

private instance P_term_projective (i : ℤ) : Projective (P.X i) := by
  change Projective (X i)
  by_cases h0 : i = 0
  · simpa only [P, X, if_pos h0] using (inferInstance : Projective Zsq)
  · by_cases h1 : i = -1
    · simpa only [P, X, if_neg h0, if_pos h1] using (inferInstance : Projective Z)
    · simpa only [P, X, if_neg h0, if_neg h1] using
        (inferInstance : Projective (0 : ModuleCat.{0} ℤᵐᵒᵖ))

private def toRange : ℤ →ₗ[ℤᵐᵒᵖ] twiceFirst.hom.range :=
  twiceFirst.hom.rangeRestrict.comp (LinearMap.inl ℤᵐᵒᵖ ℤ ℤ)

private theorem toRange_bijective : Function.Bijective toRange := by
  constructor
  · intro a b h
    have hval : 2 * a = 2 * b := congrArg Subtype.val h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hval
  · rintro ⟨z, hz⟩
    obtain ⟨⟨a, b⟩, h⟩ := hz
    exact ⟨a, Subtype.ext h⟩

private def rangeEquiv : ℤ ≃ₗ[ℤᵐᵒᵖ] twiceFirst.hom.range :=
  LinearEquiv.ofBijective toRange toRange_bijective

private instance range_projective :
    Projective (ModuleCat.of ℤᵐᵒᵖ twiceFirst.hom.range) :=
  ModuleCat.projective_of_free (rightBasis.map rangeEquiv)

private def imageRangeIso :
    Abelian.image twiceFirst ≅ ModuleCat.of ℤᵐᵒᵖ twiceFirst.hom.range :=
  Abelian.imageIsoImage twiceFirst ≪≫ ModuleCat.imageIsoRange twiceFirst

private theorem image_zero_projective
    {A B : ModuleCat.{0} ℤᵐᵒᵖ} : Projective (Abelian.image (0 : A ⟶ B)) := by
  let e := Abelian.imageIsoImage (0 : A ⟶ B) ≪≫ ModuleCat.imageIsoRange (0 : A ⟶ B)
  have hz : IsZero (ModuleCat.of ℤᵐᵒᵖ (0 : A ⟶ B).hom.range) := by
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact ModuleCat.isZero_iff_subsingleton.2 inferInstance
  exact Projective.of_iso e.symm hz.projective

private instance P_image_projective (i : ℤ) :
    Projective (connectingImages ℤ P i) := by
  by_cases hi : i = 0
  · subst i
    exact Projective.of_iso imageDegreeIso.symm
      (Projective.of_iso imageRangeIso.symm inferInstance)
  · have hd : P.d i ((ComplexShape.down ℤ).next i) = 0 := by
      rw [next_int]
      have hneg : i - 1 ≠ -1 := by omega
      simp [P, ChainComplex.of.d, d, hneg]
    change Projective (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))
    rw [hd]
    exact image_zero_projective

private instance terms_exact :
    ∀ i : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P.X i)).PreservesHomology :=
  fun i => ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ (P.X i)

private instance images_exact :
    ∀ i : ℤ,
      ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj
        (connectingImages ℤ P i)).PreservesHomology :=
  fun i => ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ
    (connectingImages ℤ P i)

private def QCyclesIso : Q.cycles 0 ≅ Z2 :=
  HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.down ℤ) 0 Z2

private def QHomologyIso : Q.homology 0 ≅ Z2 :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℤ) 0 Z2

private def oneCycle : Q.cycles 0 := QCyclesIso.inv.hom 1

private theorem oneCycle_class_value :
    QHomologyIso.hom.hom ((Q.homologyπ 0).hom oneCycle) = 1 := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom
      (ComplexShape.down ℤ) 0 Z2) oneCycle
  have hI := ConcreteCategory.congr_hom QCyclesIso.inv_hom_id (1 : ZMod 2)
  exact h.trans hI

private def imageHalfIso : connectingImages ℤ P 0 ≅ Z :=
  imageDegreeIso ≪≫ imageRangeIso ≪≫ rangeEquiv.symm.toModuleIso

private def imageOne : connectingImages ℤ P 0 := imageHalfIso.inv.hom 1

private def regularTensorIso (R : Type) [Ring R] (M : ModuleCat.{0} R) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ R)).obj M ≅
      (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let e := TensorProduct.Balanced.leftUnitor ℤ R M
  exact
    { hom := AddCommGrpCat.ofHom e.toLinearMap.toAddMonoidHom
      inv := AddCommGrpCat.ofHom e.symm.toLinearMap.toAddMonoidHom
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }

private theorem regularTensorIso_mk (R : Type) [Ring R] (M : ModuleCat.{0} R)
    (r : R) (m : M) :
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (regularTensorIso R M).hom.hom (TensorProduct.Balanced.mk ℤ R R M r m) = r • m :=
  TensorProduct.Balanced.leftUnitor_mk ℤ R M r m

private def j : {pq : ℤ × ℤ // pq.1 + pq.2 = 0} := ⟨(0, 0), by norm_num⟩
private abbrev F := connectingImageHomologyFamily ℤ P Q 0

private def sourceTensor : F j := by
  letI : Module ℤ (Q.homology 0) := Module.compHom (Q.homology 0) (algebraMap ℤ ℤ)
  exact TensorProduct.Balanced.mk ℤ ℤ (connectingImages ℤ P 0) (Q.homology 0)
    imageOne ((Q.homologyπ 0).hom oneCycle)

private def fiberEvaluate : F j ⟶ (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj Z2 :=
  ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map imageHalfIso.hom).app (Q.homology 0) ≫
    (regularTensorIso ℤ (Q.homology 0)).hom ≫
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).map QHomologyIso.hom

private theorem fiberEvaluate_value : fiberEvaluate.hom sourceTensor = 1 := by
  letI : Module ℤ (Q.homology 0) := Module.compHom (Q.homology 0) (algebraMap ℤ ℤ)
  have hI : imageHalfIso.hom.hom imageOne = 1 :=
    ConcreteCategory.congr_hom imageHalfIso.inv_hom_id (1 : ℤ)
  change QHomologyIso.hom.hom ((regularTensorIso ℤ (Q.homology 0)).hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor ℤ).map imageHalfIso.hom).app
      (Q.homology 0)).hom
      (TensorProduct.Balanced.mk ℤ ℤ (connectingImages ℤ P 0) (Q.homology 0)
        imageOne ((Q.homologyπ 0).hom oneCycle)))) = _
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, hI,
    regularTensorIso_mk, one_smul, oneCycle_class_value]

private def sourceProjection : (∐ F) ⟶ F j :=
  Sigma.desc (fun pq => if h : pq = j then eqToHom (congrArg F h) else 0)

@[reassoc]
private theorem sourceProjection_ι : Sigma.ι F j ≫ sourceProjection = 𝟙 (F j) := by
  simp [sourceProjection]

private def imageClass :
    (cyclesTensorSequence ℤ P Q).X₃.homology 0 :=
  (Sigma.ι F j ≫ (connectingImageHomologyIso ℤ P Q 0).hom).hom sourceTensor

private def classEvaluate :
    (cyclesTensorSequence ℤ P Q).X₃.homology 0 ⟶
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj Z2 :=
  (connectingImageHomologyIso ℤ P Q 0).inv ≫ sourceProjection ≫ fiberEvaluate

theorem image_class_value : classEvaluate.hom imageClass = 1 := by
  have h :
      Sigma.ι F j ≫ (connectingImageHomologyIso ℤ P Q 0).hom ≫ classEvaluate = fiberEvaluate := by
    simp only [classEvaluate, Category.assoc, Iso.hom_inv_id_assoc, sourceProjection_ι_assoc,
      Category.id_comp]
  have hp := ConcreteCategory.congr_hom h sourceTensor
  exact hp.trans fiberEvaluate_value

theorem image_class_nonzero : imageClass ≠ 0 := by
  intro h
  have hv := congrArg classEvaluate.hom h
  rw [image_class_value, map_zero] at hv
  norm_num at hv

theorem integral_connecting_square :
    Sigma.ι (connectingImageHomologyFamily ℤ P Q 0) ⟨(0, 0), by norm_num⟩ ≫
        (connectingImageHomologyIso ℤ P Q 0).hom ≫ cyclesTensorConnecting ℤ P Q 0 =
      ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map
        (HomologicalComplex.boundaryCyclesMap P 0 ((ComplexShape.down ℤ).next 0))).app
          (Q.homology 0) ≫
        Sigma.ι (connectingCyclesHomologyFamily ℤ P Q (-1))
          ⟨((ComplexShape.down ℤ).next 0, 0), by rw [next_int]; norm_num⟩ ≫
        (connectingCyclesHomologyIso ℤ P Q (-1)).hom :=
  cyclesTensorConnecting_square ℤ P Q 0 0 0 (by norm_num)

theorem nonflat_left_coefficient : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  let : Module.Flat ℤ (ZMod 2) := h
  have hreg : IsRegular (2 : ℤ) := by
    constructor
    · intro a b h
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h
    · intro a b h
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      simpa only [mul_comm] using h
  have hinj : IsSMulRegular (ZMod 2) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_isRegular hreg
  have hmul : (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • 0 := by
    norm_num [smul_eq_mul]
  have hzero : (1 : ZMod 2) = 0 := hinj hmul
  norm_num at hzero

end MathlibExtTest.BalancedTensorConnecting
