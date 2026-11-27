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

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundary
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import MathlibExtTest.Algebra.Homology.ChainComplex.BalancedTensor.ConnectingTests
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A nonzero integral Tor boundary

Every term of the right complex is the regular integer module. Its only
nonzero differential is multiplication by two from degree zero to degree minus
one. The left coefficient is ZMod 2. A nonzero tensor boundary lies in the
tensor-inclusion kernel and therefore gives a nonzero native first-Tor class.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.BalancedTensorTorBoundary

private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ
private abbrev N : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
local notation "c" => ComplexShape.down ℤ

private def rightEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private instance Z_projective : Projective Z :=
  ModuleCat.projective_of_free ((Basis.singleton PUnit ℤᵐᵒᵖ).map rightEquiv)

private def twice : Z ⟶ Z := ModuleCat.ofHom
  { toFun := fun x => 2 * x
    map_add' := fun x y => by change 2 * (x + y) = _; ring
    map_smul' := fun r x => by
      change 2 * (x * r.unop) = (2 * x) * r.unop
      ring }

private def d (i : ℤ) : Z ⟶ Z := if i = -1 then twice else 0

private theorem d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases hi : i = -1
  · subst i
    have hd : d ((-1 : ℤ) + 1) = 0 := by simp [d]
    calc
      _ = (0 : Z ⟶ Z) ≫ d (-1) :=
        congrArg (fun k : Z ⟶ Z => k ≫ d (-1)) hd
      _ = 0 := by simp only [zero_comp]
  · have hd : d i = 0 := by simp [d, hi]
    calc
      _ = d (i + 1) ≫ (0 : Z ⟶ Z) :=
        congrArg (fun k : Z ⟶ Z => d (i + 1) ≫ k) hd
      _ = 0 := by simp only [comp_zero]

private def P : ChainComplex (ModuleCat.{0} ℤᵐᵒᵖ) ℤ :=
  ChainComplex.of (fun _ : ℤ => Z) d d_sq

theorem original_differential (a : ℤ) : (P.d 0 (-1)).hom a = 2 * a := by
  change (ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1)).hom a = _
  simpa only [ChainComplex.of_d] using (show (d (-1)).hom a = 2 * a from rfl)

private theorem next_int (i : ℤ) : c.next i = i - 1 :=
  c.next_eq' (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private theorem incoming : c.prev (-1) = 0 :=
  c.prev_eq' (by change (-1 : ℤ) + 1 = 0; norm_num)

private theorem outgoing_zero : P.d (-1) (c.next (-1)) = 0 := by
  have hd : P.d (-1) (-2) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-2 : ℤ) + 1) (-2) = 0
    simpa only [ChainComplex.of_d] using (show d (-2) = 0 from rfl)
  exact (congrArg (fun k : ℤ => (show Z ⟶ Z from P.d (-1) k)) (next_int (-1))).trans hd

private instance term_exact :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P.X (-1))).PreservesHomology := by
  change ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj Z).PreservesHomology
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ Z

private theorem image_zero_projective
    {A B : ModuleCat.{0} ℤᵐᵒᵖ} : Projective (Abelian.image (0 : A ⟶ B)) := by
  let e := Abelian.imageIsoImage (0 : A ⟶ B) ≪≫ ModuleCat.imageIsoRange (0 : A ⟶ B)
  have hz : IsZero (ModuleCat.of ℤᵐᵒᵖ (0 : A ⟶ B).hom.range) := by
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact ModuleCat.isZero_iff_subsingleton.2 inferInstance
  exact Projective.of_iso e.symm hz.projective

private instance image_exact :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj
      (Abelian.image (P.d (-1) (c.next (-1))))).PreservesHomology := by
  let : Projective (Abelian.image (P.d (-1) (c.next (-1)))) := by
    rw [outgoing_zero]
    exact image_zero_projective
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ _

private abbrev f := P.d 0 (-1)
private abbrev B := Abelian.image f

private def toRange : ℤ →ₗ[ℤᵐᵒᵖ] f.hom.range := f.hom.rangeRestrict

private theorem toRange_bijective : Function.Bijective toRange := by
  constructor
  · intro a b h
    have hv := congrArg Subtype.val h
    change f.hom a = f.hom b at hv
    rw [original_differential, original_differential] at hv
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hv
  · rintro ⟨z, hz⟩
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Subtype.ext ha⟩

private def rangeEquiv : ℤ ≃ₗ[ℤᵐᵒᵖ] f.hom.range :=
  LinearEquiv.ofBijective toRange toRange_bijective

private def imageRangeIso : B ≅ ModuleCat.of ℤᵐᵒᵖ f.hom.range :=
  Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f

private theorem imageRangeIso_ι :
    imageRangeIso.hom ≫ ModuleCat.ofHom f.hom.range.subtype = Abelian.image.ι f := by
  dsimp only [imageRangeIso, Iso.trans_hom]
  rw [Category.assoc, ModuleCat.imageIsoRange_hom_subtype]
  exact Abelian.imageIsoImage_hom_comp_image_ι f

private def imageHalfIso : B ≅ Z := imageRangeIso ≪≫ rangeEquiv.symm.toModuleIso

private def imageOne : B := (Abelian.factorThruImage f).hom 1

private theorem imageHalfIso_value : imageHalfIso.hom.hom imageOne = 1 := by
  have hRange : imageRangeIso.hom.hom imageOne = rangeEquiv 1 := by
    apply Subtype.ext
    have h₁ := ConcreteCategory.congr_hom imageRangeIso_ι imageOne
    have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) (1 : ℤ)
    change Subtype.val (imageRangeIso.hom.hom imageOne) = f.hom 1
    exact h₁.trans h₂
  change rangeEquiv.symm (imageRangeIso.hom.hom imageOne) = 1
  rw [hRange]
  exact rangeEquiv.symm_apply_apply 1

private def cyclesIso : P.cycles (-1) ≅ Z :=
  P.iCyclesIso (-1) (c.next (-1)) rfl outgoing_zero

private def β : B ⟶ P.cycles (-1) := HomologicalComplex.boundaryCyclesMap P 0 (-1)

private theorem β_value : cyclesIso.hom.hom (β.hom imageOne) = 2 := by
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.boundaryCyclesMap_i P 0 (-1))
    imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) (1 : ℤ)
  change (P.iCycles (-1)).hom (β.hom imageOne) = 2
  exact h₁.trans (h₂.trans (by simpa only [mul_one] using original_differential 1))

private def regularTensorIso (R : Type) [Ring R] (M : ModuleCat.{0} R) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ R)).obj M ≅
      (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  exact (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso
    (TensorProduct.Balanced.leftUnitor ℤ R M).toModuleIso

private theorem regularTensorIso_mk (R : Type) [Ring R] (M : ModuleCat.{0} R)
    (r : R) (m : M) :
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (regularTensorIso R M).hom.hom (TensorProduct.Balanced.mk ℤ R R M r m) = r • m :=
  TensorProduct.Balanced.leftUnitor_mk ℤ R M r m

private abbrev T := ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj B).obj N
private def tensorInclusion : T ⟶
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P.cycles (-1))).obj N :=
  ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map β).app N

private def sourceOne : T := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  exact TensorProduct.Balanced.mk ℤ ℤ B N imageOne 1

private def sourceEvaluate : T ⟶ (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj N :=
  ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map imageHalfIso.hom).app N ≫
    (regularTensorIso ℤ N).hom

private theorem sourceOne_value : sourceEvaluate.hom sourceOne = 1 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  change (regularTensorIso ℤ N).hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor ℤ).map imageHalfIso.hom).app N).hom
      (TensorProduct.Balanced.mk ℤ ℤ B N imageOne 1)) = 1
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, imageHalfIso_value,
    regularTensorIso_mk, one_smul]

private theorem sourceOne_kernel : tensorInclusion.hom sourceOne = 0 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  let e := ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map cyclesIso.hom).app N ≫
    (regularTensorIso ℤ N).hom
  let : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change (regularTensorIso ℤ N).hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor ℤ).map cyclesIso.hom).app N).hom
      ((((ModuleCat.BalancedTensor.groupBifunctor ℤ).map β).app N).hom
        (TensorProduct.Balanced.mk ℤ ℤ B N imageOne 1))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, β_value, regularTensorIso_mk]
  norm_num [zsmul_eq_mul]

private def sourceOneMap : AddCommGrpCat.of ℤ ⟶ T :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z • sourceOne
      map_zero' := zero_zsmul sourceOne
      map_add' := fun x y => add_zsmul sourceOne x y }

private theorem sourceOneMap_zero : sourceOneMap ≫ tensorInclusion = 0 := by
  apply ConcreteCategory.ext_apply
  intro z
  change tensorInclusion.hom (z • sourceOne) = 0
  rw [map_zsmul, sourceOne_kernel, smul_zero]

private def kernelOneMap : AddCommGrpCat.of ℤ ⟶ kernel tensorInclusion :=
  kernel.lift tensorInclusion sourceOneMap sourceOneMap_zero

private def kernelIso :
    ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (P.homology (-1))).obj N ≅
      kernel tensorInclusion :=
  torBoundaryKernelIso ℤ P N 0 (-1) incoming

private def torClass :
    ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (P.homology (-1))).obj N :=
  kernelIso.inv.hom (kernelOneMap.hom 1)

private theorem torClass_boundary :
    (torBoundary ℤ P N 0 (-1) incoming).hom torClass = sourceOne := by
  have h₁ := ConcreteCategory.congr_hom
    (torBoundaryKernelIso_inv_boundary ℤ P N 0 (-1) incoming) (kernelOneMap.hom 1)
  have h₂ := ConcreteCategory.congr_hom
    (kernel.lift_ι tensorInclusion sourceOneMap sourceOneMap_zero) (1 : ℤ)
  have h₃ : sourceOneMap.hom 1 = sourceOne := by
    change (1 : ℤ) • sourceOne = sourceOne
    exact one_zsmul sourceOne
  exact h₁.trans (h₂.trans h₃)

theorem tor_boundary_value :
    sourceEvaluate.hom ((torBoundary ℤ P N 0 (-1) incoming).hom torClass) = 1 := by
  rw [torClass_boundary, sourceOne_value]

theorem tor_class_nonzero : torClass ≠ 0 := by
  intro h
  have hv := congrArg (fun x =>
    sourceEvaluate.hom ((torBoundary ℤ P N 0 (-1) incoming).hom x)) h
  rw [tor_boundary_value, map_zero, map_zero] at hv
  norm_num at hv

theorem tor_object_nonzero :
    ¬ IsZero (((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (P.homology (-1))).obj N) := by
  intro h
  have hid :
      (𝟙 (((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (P.homology (-1))).obj N)) = 0 :=
    h.eq_of_src _ _
  have hz := ConcreteCategory.congr_hom hid torClass
  change torClass = 0 at hz
  exact tor_class_nonzero hz

theorem nonflat_coefficient : ¬ Module.Flat ℤ (ZMod 2) :=
  MathlibExtTest.BalancedTensorConnecting.nonflat_left_coefficient

private def scaleChain (z : ℤ) : P ⟶ P := z • 𝟙 P

private theorem scaleChain_f (z i : ℤ) :
    (scaleChain z).f i = z • 𝟙 (P.X i) := by
  simp only [scaleChain, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]

private abbrev scaleImage (z : ℤ) :=
  ((HomologicalComplex.boundariesCyclesHomologySequenceFunctor
    (C := ModuleCat.{0} ℤᵐᵒᵖ) («c» := c) 0 (-1)).map (scaleChain z)).τ₁

private theorem scaleImage_eq (z : ℤ) : scaleImage z = z • 𝟙 B := by
  apply (cancel_mono (Abelian.image.ι f)).1
  rw [HomologicalComplex.boundariesCyclesHomologySequenceFunctor_map_image_ι]
  simp only [scaleChain_f, comp_zsmul, comp_id, zsmul_comp, id_comp]

private abbrev tensorScaleImage (z : ℤ) :=
  ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map (scaleImage z)).app N

private theorem tensorScaleImage_eq (z : ℤ) : tensorScaleImage z = z • 𝟙 T := by
  let F : ModuleCat.{0} ℤᵐᵒᵖ ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor ℤ).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor ℤ) N
  change F.map (scaleImage z) = z • 𝟙 (F.obj B)
  rw [scaleImage_eq, Functor.map_zsmul, Functor.map_id]

private theorem tensorScaleImage_value (z : ℤ) :
    sourceEvaluate.hom ((tensorScaleImage z).hom sourceOne) = (z : ZMod 2) := by
  rw [tensorScaleImage_eq, AddCommGrpCat.hom_zsmul, AddCommGrpCat.hom_id]
  change sourceEvaluate.hom (z • sourceOne) = _
  rw [map_zsmul, sourceOne_value]
  simp only [zsmul_eq_mul, mul_one]

private abbrev torScale (z : ℤ) :=
  ((ModuleCat.BalancedTensor.torFirst ℤ 1).map
    (HomologicalComplex.homologyMap (scaleChain z) (-1))).app N

private theorem torScale_boundary_value (z : ℤ) :
    sourceEvaluate.hom
      ((torBoundary ℤ P N 0 (-1) incoming).hom ((torScale z).hom torClass)) =
        (z : ZMod 2) := by
  have h := ConcreteCategory.congr_hom
    (torBoundary_naturality ℤ N 0 (-1) incoming (scaleChain z)) torClass
  change (torBoundary ℤ P N 0 (-1) incoming).hom ((torScale z).hom torClass) =
    (tensorScaleImage z).hom
      ((torBoundary ℤ P N 0 (-1) incoming).hom torClass) at h
  rw [torClass_boundary] at h
  exact (congrArg sourceEvaluate.hom h).trans (tensorScaleImage_value z)

/-- At integral term zero, the multiply-by-three chain map sends `1` to `3`. -/
example : ((scaleChain 3).f 0).hom (1 : ℤ) = 3 := by
  rw [scaleChain_f, ModuleCat.hom_zsmul, ModuleCat.hom_id]
  change (3 : ℤ) • (1 : ℤ) = 3
  norm_num [zsmul_eq_mul]

/-- The induced first-Tor map for multiplication by three retains the nonzero boundary value. -/
example : sourceEvaluate.hom
    ((torBoundary ℤ P N 0 (-1) incoming).hom ((torScale 3).hom torClass)) = 1 := by
  have h := torScale_boundary_value 3
  norm_num at h
  exact h

/-- Multiplication by two on the integral complex kills the detected tensor-boundary value. -/
example : sourceEvaluate.hom
    ((torBoundary ℤ P N 0 (-1) incoming).hom ((torScale 2).hom torClass)) = 0 := by
  have h := torScale_boundary_value 2
  norm_num at h
  exact h

/-- The first-Tor image under multiplication by three is nonzero. -/
example : (torScale 3).hom torClass ≠ 0 := by
  intro hz
  have h := torScale_boundary_value 3
  rw [hz, map_zero, map_zero] at h
  norm_num at h

end MathlibExtTest.BalancedTensorTorBoundary
