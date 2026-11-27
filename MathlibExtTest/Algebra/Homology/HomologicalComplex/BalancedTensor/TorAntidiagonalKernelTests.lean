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

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorAntidiagonalKernel
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Nonzero Tor boundary images over ℤ/4

Let R=ℤ/4 and N=ℤ/2, with the left R-action through reduction. The right
complex P has the regular module R in every integer degree, and its only
nonzero differential is multiplication by two from degree zero to degree
minus one. Its boundary image there is the ideal (2). The generator
2 ⊗ 1 is nonzero in (2) ⊗ᴿ N and maps to zero in R ⊗ᴿ N.

For a family indexed by Fin 2, take two copies of P and N and the same
boundary degrees. The coproduct tensor kernel has two independently
detected coordinates. The image-of-coproduct Tor comparison carries a
nonzero image class to a kernel element with value one in each coordinate.

The coefficient tensor functor fails to preserve homology. The right
terms remain regular R-modules; the image comparison applies without
flatness of N. This fixture uses the finite two-element coproduct.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.TorAntidiagonalKernel

private abbrev R := ZMod 4
private abbrev S := ZMod 2

private def reduction : R →+* S := ZMod.castHom (by decide : 2 ∣ 4) S

private instance : Algebra R S := reduction.toAlgebra

private abbrev Z : ModuleCat.{0} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ R
private abbrev N : ModuleCat.{0} R := ModuleCat.of R S

private def twice : Z ⟶ Z := ModuleCat.ofHom
  { toFun := fun x => 2 * x
    map_add' := fun x y => mul_add 2 x y
    map_smul' := fun r x => by
      change 2 * (x * r.unop) = (2 * x) * r.unop
      exact (mul_assoc 2 x r.unop).symm }

private def d (i : ℤ) : Z ⟶ Z := if i = -1 then twice else 0

private theorem d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases hi : i = -1
  · subst i
    have hz : d ((-1 : ℤ) + 1) = 0 := by simp [d]
    exact (congrArg (fun f : Z ⟶ Z => f ≫ d (-1)) hz).trans zero_comp
  · have hz : d i = 0 := by simp [d, hi]
    exact (congrArg (fun f : Z ⟶ Z => d (i + 1) ≫ f) hz).trans comp_zero

private def P : ChainComplex (ModuleCat.{0} Rᵐᵒᵖ) ℤ :=
  ChainComplex.of (fun _ : ℤ => Z) d d_sq

private theorem differential_eq : P.d 0 (-1) = twice := by
  change ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1) = twice
  simpa only [ChainComplex.of_d] using (show d (-1) = twice from by simp [d])

private theorem differential_value (a : R) : (P.d 0 (-1)).hom a = 2 * a := by
  rw [differential_eq]
  rfl

theorem acting_ring_zero_divisor : (2 : R) ≠ 0 ∧ (2 : R) * 2 = 0 := by decide

private theorem next_int (i : ℤ) : (ComplexShape.down ℤ).next i = i - 1 :=
  (ComplexShape.down ℤ).next_eq'
    (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private theorem incoming : (ComplexShape.down ℤ).prev (-1) = 0 :=
  (ComplexShape.down ℤ).prev_eq' (by change (-1 : ℤ) + 1 = 0; norm_num)

private theorem outgoing_zero : P.d (-1) ((ComplexShape.down ℤ).next (-1)) = 0 := by
  have hz : P.d (-1) (-2) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-2 : ℤ) + 1) (-2) = 0
    simpa only [ChainComplex.of_d] using (show d (-2) = 0 from by simp [d])
  exact (congrArg (fun k : ℤ => (show Z ⟶ Z from P.d (-1) k)) (next_int (-1))).trans hz

private abbrev f := P.d 0 (-1)
private abbrev B := Abelian.image f
private abbrev H : ModuleCat.{0} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ f.hom.range

private def imageRangeIso : B ≅ H :=
  Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f

private theorem imageRangeIso_ι :
    imageRangeIso.hom ≫ ModuleCat.ofHom f.hom.range.subtype = Abelian.image.ι f := by
  dsimp only [imageRangeIso, Iso.trans_hom]
  rw [Category.assoc, ModuleCat.imageIsoRange_hom_subtype]
  exact Abelian.imageIsoImage_hom_comp_image_ι f

private theorem range_cases (x : H) : (x : R) = 0 ∨ (x : R) = 2 := by
  obtain ⟨a, ha⟩ := x.property
  have hv : f.hom a = 0 ∨ f.hom a = 2 := by
    rw [differential_value]
    fin_cases a <;> decide
  exact hv.imp (fun h => ha.symm.trans h) (fun h => ha.symm.trans h)

private def half : H →+ S where
  toFun x := if (x : R) = 2 then 1 else 0
  map_zero' := by change (if (0 : R) = 2 then (1 : S) else 0) = 0; decide
  map_add' x y := by
    change (if (x : R) + (y : R) = 2 then (1 : S) else 0) =
      (if (x : R) = 2 then (1 : S) else 0) + (if (y : R) = 2 then (1 : S) else 0)
    rcases range_cases x with hx | hx <;> rcases range_cases y with hy | hy <;>
      simp only [hx, hy] <;> decide

private theorem half_scalar (r : R) (x : H) :
    half (MulOpposite.op r • x) = reduction r * half x := by
  change (if (x : R) * r = 2 then (1 : S) else 0) =
    reduction r * (if (x : R) = 2 then (1 : S) else 0)
  rcases range_cases x with hx | hx
  · simp only [hx]
    fin_cases r <;> decide
  · simp only [hx]
    fin_cases r <;> decide

private def halfLinear :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    H →ₗ[ℤ] N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact
    { toFun := half
      map_add' := half.map_add
      map_smul' := fun z x => by
        change half (z • x) = (algebraMap ℤ R z) • half x
        exact map_intCast_smul half ℤ R z x }

private def rangePairing :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    H →ₗ[ℤ] N →ₗ[ℤ] N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let mul : N →ₗ[ℤ] N →ₗ[ℤ] N :=
    (Algebra.lsmul ℤ ℤ N : N →ₐ[ℤ] Module.End ℤ N).toLinearMap
  exact mul.comp halfLinear

private theorem rangePairing_balanced :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    ∀ (r : R) (x : H) (y : N),
      rangePairing (MulOpposite.op r • x) y = rangePairing x (r • y) := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  intro r x y
  change half (MulOpposite.op r • x) * y = half x * (reduction r * y)
  rw [half_scalar]
  exact (congrArg (fun z : S => z * y) (mul_comm (reduction r) (half x))).trans
    (mul_assoc (half x) (reduction r) y)

private def rangeTensorEvaluation :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj H).obj N ⟶ AddCommGrpCat.of S := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact AddCommGrpCat.ofHom
    (TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := H) (N := N)
      rangePairing rangePairing_balanced).toAddMonoidHom

private theorem rangeTensorEvaluation_mk (x : H) (y : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    rangeTensorEvaluation.hom (TensorProduct.Balanced.mk ℤ R H N x y) = half x * y := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := H) (N := N)
    rangePairing rangePairing_balanced (TensorProduct.Balanced.mk ℤ R H N x y) = _
  rw [TensorProduct.Balanced.lift_mk]
  rfl

private def imageOne : B := (Abelian.factorThruImage f).hom 1

private def rangeTwo : H :=
  ⟨2, ⟨1, (differential_value 1).trans (mul_one 2)⟩⟩

private theorem imageRangeIso_value : imageRangeIso.hom.hom imageOne = rangeTwo := by
  apply Subtype.ext
  have h₁ := ConcreteCategory.congr_hom imageRangeIso_ι imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) (1 : R)
  exact h₁.trans (h₂.trans ((differential_value 1).trans (mul_one 2)))

private def cyclesIso : P.cycles (-1) ≅ Z :=
  P.iCyclesIso (-1) ((ComplexShape.down ℤ).next (-1)) rfl outgoing_zero

private def β : B ⟶ P.cycles (-1) := HomologicalComplex.boundaryCyclesMap P 0 (-1)

private theorem β_value : cyclesIso.hom.hom (β.hom imageOne) = 2 := by
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.boundaryCyclesMap_i P 0 (-1)) imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) (1 : R)
  change (P.iCycles (-1)).hom (β.hom imageOne) = 2
  exact h₁.trans (h₂.trans ((differential_value 1).trans (mul_one 2)))

private def regularTensorIso (T : Type) [Ring T] (M : ModuleCat.{0} T) :
    ((ModuleCat.BalancedTensor.groupBifunctor T).obj (ModuleCat.of Tᵐᵒᵖ T)).obj M ≅
      (forget₂ (ModuleCat.{0} T) AddCommGrpCat.{0}).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ T)
  exact (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso
    (TensorProduct.Balanced.leftUnitor ℤ T M).toModuleIso

private theorem regularTensorIso_mk (T : Type) [Ring T] (M : ModuleCat.{0} T)
    (r : T) (m : M) :
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ T)
    (regularTensorIso T M).hom.hom (TensorProduct.Balanced.mk ℤ T T M r m) = r • m :=
  TensorProduct.Balanced.leftUnitor_mk ℤ T M r m

private abbrev T := ((ModuleCat.BalancedTensor.groupBifunctor R).obj B).obj N

private def tensorInclusion : T ⟶
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles (-1))).obj N :=
  ((ModuleCat.BalancedTensor.groupBifunctor R).map β).app N

private def sourceOne : T := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact TensorProduct.Balanced.mk ℤ R B N imageOne 1

private def sourceEvaluate : T ⟶ AddCommGrpCat.of S :=
  ((ModuleCat.BalancedTensor.groupBifunctor R).map imageRangeIso.hom).app N ≫ rangeTensorEvaluation

private theorem sourceOne_value : sourceEvaluate.hom sourceOne = 1 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change rangeTensorEvaluation.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor R).map imageRangeIso.hom).app N).hom
      (TensorProduct.Balanced.mk ℤ R B N imageOne 1)) = 1
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, imageRangeIso_value,
    rangeTensorEvaluation_mk]
  decide

private theorem sourceOne_kernel : tensorInclusion.hom sourceOne = 0 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let e := ((ModuleCat.BalancedTensor.groupBifunctor R).map cyclesIso.hom).app N ≫
    (regularTensorIso R N).hom
  let : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change (regularTensorIso R N).hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor R).map cyclesIso.hom).app N).hom
      ((((ModuleCat.BalancedTensor.groupBifunctor R).map β).app N).hom
        (TensorProduct.Balanced.mk ℤ R B N imageOne 1))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, β_value, regularTensorIso_mk]
  change reduction (2 : R) * (1 : S) = 0
  decide

theorem nonzero_boundary_tensor : sourceOne ≠ 0 := by
  intro h
  have hv := congrArg sourceEvaluate.hom h
  rw [sourceOne_value, map_zero] at hv
  exact (by decide : (1 : S) ≠ 0) hv

theorem noninjective_tensor_inclusion : ¬ Mono tensorInclusion := by
  intro hm
  have hz := (AddCommGrpCat.mono_iff_injective tensorInclusion).1 hm
    (sourceOne_kernel.trans tensorInclusion.hom.map_zero.symm)
  exact nonzero_boundary_tensor hz

theorem coefficient_tensor_not_exact :
    ¬ ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).PreservesHomology := by
  intro h
  let F : ModuleCat.{0} Rᵐᵒᵖ ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive := Functor.LeftDerivedBalance.flippedObjAdditive
    (ModuleCat.BalancedTensor.groupBifunctor R) N
  let : F.PreservesHomology := h
  let : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  let : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
  let C := HomologicalComplex.boundariesCyclesHomologySequence P 0 (-1)
  have hc : C.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P 0 (-1) incoming
  have hm : Mono (F.map C.f) := (hc.map_of_exact F).mono_f
  exact noninjective_tensor_inclusion hm

private def sourceOneMap : AddCommGrpCat.of ℤ ⟶ T := AddCommGrpCat.ofHom
  { toFun := fun z => z • sourceOne
    map_zero' := zero_zsmul sourceOne
    map_add' := fun x y => add_zsmul sourceOne x y }

private theorem sourceOneMap_zero : sourceOneMap ≫ tensorInclusion = 0 := by
  apply ConcreteCategory.ext_apply
  intro z
  change tensorInclusion.hom (z • sourceOne) = 0
  rw [map_zsmul, sourceOne_kernel, smul_zero]

private abbrev I := Fin 2
private abbrev PF : I → ChainComplex (ModuleCat.{0} Rᵐᵒᵖ) ℤ := fun _ => P
private abbrev NF : I → ModuleCat.{0} R := fun _ => N
private abbrev iF : I → ℤ := fun _ => 0
private abbrev jF : I → ℤ := fun _ => -1
private theorem incomingF (a : I) : (ComplexShape.down ℤ).prev (jF a) = iF a := incoming

private abbrev X : I → AddCommGrpCat.{0} := fun _ => T
private abbrev Y : I → AddCommGrpCat.{0} := fun _ =>
  ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles (-1))).obj N

private def tensorFamilyMap : (∐ X) ⟶ ∐ Y :=
  coproductBoundaryTensorMap R PF NF iF jF

private def torFamilyMap :
    (∐ fun _ : I => ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology (-1))).obj N) ⟶
      ∐ X :=
  coproductTorBoundary R PF NF iF jF incomingF

private def imageKernelIso : Abelian.image torFamilyMap ≅ kernel tensorFamilyMap :=
  coproductTorBoundaryImageKernelIso R PF NF iF jF incomingF

private def summandKernelMap (a : I) : AddCommGrpCat.of ℤ ⟶ kernel tensorFamilyMap :=
  kernel.lift tensorFamilyMap (sourceOneMap ≫ Sigma.ι X a) (by
    change (sourceOneMap ≫ Sigma.ι X a) ≫ Sigma.map (fun _ : I => tensorInclusion) = 0
    rw [Category.assoc, Sigma.ι_map, ← Category.assoc, sourceOneMap_zero, zero_comp])

private def projection (b : I) : (∐ X) ⟶ AddCommGrpCat.of S :=
  Sigma.desc (fun a : I => if a = b then sourceEvaluate else 0)

private def evaluate (b : I) : kernel tensorFamilyMap ⟶ AddCommGrpCat.of S :=
  kernel.ι tensorFamilyMap ≫ projection b

private theorem component_value (a b : I) :
    (evaluate b).hom ((summandKernelMap a).hom 1) = if a = b then (1 : S) else 0 := by
  have h : summandKernelMap a ≫ evaluate b =
      if a = b then sourceOneMap ≫ sourceEvaluate else 0 := by
    simp only [evaluate, summandKernelMap, Category.assoc, kernel.lift_ι_assoc,
      projection, Sigma.ι_desc]
    by_cases hab : a = b
    · simp only [if_pos hab]
    · simp only [if_neg hab, comp_zero]
  have hv := ConcreteCategory.congr_hom h (1 : ℤ)
  by_cases hab : a = b
  · simp only [if_pos hab] at hv ⊢
    exact hv.trans ((congrArg sourceEvaluate.hom (one_zsmul sourceOne)).trans sourceOne_value)
  · simpa only [if_neg hab] using hv

private def familyKernelElement : kernel tensorFamilyMap :=
  (summandKernelMap 0).hom 1 + (summandKernelMap 1).hom 1

theorem first_kernel_coordinate : (evaluate 0).hom familyKernelElement = 1 := by
  rw [familyKernelElement, map_add, component_value, component_value]
  norm_num

theorem second_kernel_coordinate : (evaluate 1).hom familyKernelElement = 1 := by
  rw [familyKernelElement, map_add, component_value, component_value]
  norm_num

private def familyImageElement : Abelian.image torFamilyMap :=
  imageKernelIso.inv.hom familyKernelElement

private theorem familyImageElement_inclusion :
    (Abelian.image.ι torFamilyMap).hom familyImageElement =
      (kernel.ι tensorFamilyMap).hom familyKernelElement := by
  have h : imageKernelIso.inv ≫ Abelian.image.ι torFamilyMap = kernel.ι tensorFamilyMap := by
    rw [← coproductTorBoundaryImageKernelIso_hom_ι R PF NF iF jF incomingF]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom h familyKernelElement

theorem first_image_coordinate :
    (projection 0).hom ((Abelian.image.ι torFamilyMap).hom familyImageElement) = 1 := by
  rw [familyImageElement_inclusion]
  exact first_kernel_coordinate

theorem second_image_coordinate :
    (projection 1).hom ((Abelian.image.ι torFamilyMap).hom familyImageElement) = 1 := by
  rw [familyImageElement_inclusion]
  exact second_kernel_coordinate

theorem nonzero_tor_boundary_image : familyImageElement ≠ 0 := by
  intro h
  have hv := congrArg (fun x => (projection 0).hom ((Abelian.image.ι torFamilyMap).hom x)) h
  rw [first_image_coordinate, map_zero, map_zero] at hv
  exact (by decide : (1 : S) ≠ 0) hv

end MathlibExtTest.TorAntidiagonalKernel
