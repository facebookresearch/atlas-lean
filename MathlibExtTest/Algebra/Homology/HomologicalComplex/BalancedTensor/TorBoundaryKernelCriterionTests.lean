/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Authors: @toskua, Codex
-/
module

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundaryKernelCriterion
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A tensor kernel with free cycles and nonexact terms

Let R=ℤ/4, let U=ℤ/2 as a right R-module and N=ℤ/2 as a left R-module,
both through reduction. The right complex P is
R → R⊕U → U in degrees two, one and zero, with maps
x ↦ (2x,0) and (x,u) ↦ u. Its degree-one cycles form the free right
module R, and its boundary is the image of x ↦ (2x,0).

Tensoring left modules with R⊕U or with the outgoing image U fails to
preserve homology. Nevertheless Tor₁ᴿ(cycles₁(P),N) vanishes, so the
cycles-to-homology Tor map is zero and the canonical boundary gives the
whole Tor-to-kernel isomorphism.

A nonzero Tor class has boundary represented by 2 ⊗ 1 in the boundary
tensor group, with detected value one. The forward comparison is the
canonical kernel lift of that connecting boundary.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.TorBoundaryKernelCriterion

private abbrev R := ZMod 4
private abbrev S := ZMod 2

private def reduction : R →+* S := ZMod.castHom (by decide : 2 ∣ 4) S

private def reductionOp : Rᵐᵒᵖ →+* S where
  toFun r := reduction r.unop
  map_zero' := reduction.map_zero
  map_one' := reduction.map_one
  map_add' x y := reduction.map_add x.unop y.unop
  map_mul' x y := by
    change reduction (y.unop * x.unop) = reduction x.unop * reduction y.unop
    rw [map_mul, mul_comm]

private instance : Algebra R S := reduction.toAlgebra
private instance : Algebra Rᵐᵒᵖ S := reductionOp.toAlgebra

private abbrev Z : ModuleCat.{0} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ R
private abbrev U : ModuleCat.{0} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ S
private abbrev N : ModuleCat.{0} R := ModuleCat.of R S
private abbrev K := Z ⊞ U

private def twice : Z ⟶ Z := ModuleCat.ofHom
  { toFun := fun x => 2 * x
    map_add' := fun x y => mul_add 2 x y
    map_smul' := fun r x => by
      change 2 * (x * r.unop) = (2 * x) * r.unop
      exact (mul_assoc 2 x r.unop).symm }

private def incomingMap : Z ⟶ K := twice ≫ biprod.inl
private def outgoingMap : K ⟶ U := biprod.snd

private theorem incoming_outgoing : incomingMap ≫ outgoingMap = 0 := by
  simp only [incomingMap, outgoingMap, Category.assoc, biprod.inl_snd, comp_zero]

private def X (n : ℤ) : ModuleCat.{0} Rᵐᵒᵖ :=
  if n = 2 then Z else if n = 1 then K else if n = 0 then U else 0

private def d (n : ℤ) : X (n + 1) ⟶ X n :=
  if h : n = 1 then by
    subst n
    change Z ⟶ K
    exact incomingMap
  else if h : n = 0 then by
    subst n
    change K ⟶ U
    exact outgoingMap
  else 0

private theorem d_one : d 1 = incomingMap := by simp [d]
private theorem d_zero : d 0 = outgoingMap := by simp [d]

private theorem d_other (n : ℤ) (hn₁ : n ≠ 1) (hn₀ : n ≠ 0) : d n = 0 := by
  simp only [d, dif_neg hn₁, dif_neg hn₀]

private theorem d_sq (n : ℤ) : d (n + 1) ≫ d n = 0 := by
  by_cases hn₁ : n = 1
  · subst n
    rw [d_other 2 (by decide) (by decide), zero_comp]
  · by_cases hn₀ : n = 0
    · subst n
      rw [d_one, d_zero]
      exact incoming_outgoing
    · rw [d_other n hn₁ hn₀, comp_zero]

private def P : ChainComplex (ModuleCat.{0} Rᵐᵒᵖ) ℤ := ChainComplex.of X d d_sq

private theorem differential_two : P.d 2 1 = incomingMap := by
  change ChainComplex.of.d X d ((1 : ℤ) + 1) 1 = incomingMap
  rw [ChainComplex.of_d, d_one]

private theorem differential_one : P.d 1 0 = outgoingMap := by
  change ChainComplex.of.d X d ((0 : ℤ) + 1) 0 = outgoingMap
  rw [ChainComplex.of_d, d_zero]

private theorem next_one : (ComplexShape.down ℤ).next 1 = 0 :=
  (ComplexShape.down ℤ).next_eq'
    (show (ComplexShape.down ℤ).Rel (1 : ℤ) 0 from rfl)

private theorem prev_one : (ComplexShape.down ℤ).prev 1 = 2 :=
  (ComplexShape.down ℤ).prev_eq'
    (show (ComplexShape.down ℤ).Rel (2 : ℤ) 1 from rfl)

theorem incoming_first_coordinate :
    P.d 2 1 ≫ (biprod.fst : K ⟶ Z) = twice := by
  rw [differential_two]
  simp only [incomingMap, Category.assoc, biprod.inl_fst, Category.comp_id]

theorem outgoing_is_projection : P.d 1 0 = (biprod.snd : K ⟶ U) := differential_one

private def cycleFork : KernelFork (P.d 1 0) :=
  KernelFork.ofι (biprod.inl : Z ⟶ K) (by
    rw [differential_one]
    exact biprod.inl_snd)

private def cycleForkIsLimit : IsLimit cycleFork := by
  simpa only [cycleFork, differential_one] using biprod.isKernelSndKernelFork Z U

private def cyclesIso : P.cycles 1 ≅ Z :=
  (P.cyclesIsKernel 1 0 next_one).conePointUniqueUpToIso cycleForkIsLimit

private theorem cyclesIso_hom_inl :
    cyclesIso.hom ≫ (biprod.inl : Z ⟶ K) = P.iCycles 1 := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (P.cyclesIsKernel 1 0 next_one)
    cycleForkIsLimit
    WalkingParallelPair.zero

private def rightEquiv : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private instance Z_projective : Projective Z :=
  ModuleCat.projective_of_free ((Basis.singleton PUnit Rᵐᵒᵖ).map rightEquiv)

private instance cycles_projective : Projective (P.cycles 1) :=
  Projective.of_iso cyclesIso.symm

private theorem cyclesTor_zero :
    IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles 1)).obj N) := by
  let F : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles 1)
  let : F.PreservesHomology :=
    ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective R (P.cycles 1)
  exact (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
    R (P.cycles 1)).1 (Functor.preservesFiniteLimits_of_preservesHomology F) N

theorem upstream_cycles_map_zero : torCyclesHomologyMap R P N 1 = 0 :=
  torCyclesHomologyMap_eq_zero_of_isZero R P N 1 cyclesTor_zero

theorem criterion_kernel_lift_isIso : IsIso (torBoundaryKernelLift R P N 2 1 prev_one) :=
  (torBoundaryKernelLift_isIso_iff R P N 2 1 prev_one).2 upstream_cycles_map_zero

private def kernelComparison :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology 1)).obj N ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P 2 1)).app N) :=
  torBoundaryKernelIsoOfCyclesMapZero R P N 2 1 prev_one upstream_cycles_map_zero

theorem vanishing_constructor_forward :
    (torBoundaryKernelIsoOfIsZeroCyclesTor R P N 2 1 prev_one cyclesTor_zero).hom ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P 2 1)).app N) =
      torBoundary R P N 2 1 prev_one :=
  torBoundaryKernelIsoOfIsZeroCyclesTor_hom_ι R P N 2 1 prev_one cyclesTor_zero


private abbrev ZL : ModuleCat.{0} R := ModuleCat.of R R
private def twiceLeft : ZL ⟶ ZL := ModuleCat.ofHom ((2 : R) • (LinearMap.id : R →ₗ[R] R))
private abbrev HL : ModuleCat.{0} R := ModuleCat.of R twiceLeft.hom.range

private def halve (x : R) : S := if x = 2 then 1 else 0

private theorem halve_add (x y : R) (hx : x = 0 ∨ x = 2) (hy : y = 0 ∨ y = 2) :
    halve (x + y) = halve x + halve y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y <;> decide

private theorem halve_mul (x r : R) (hx : x = 0 ∨ x = 2) :
    halve (x * r) = reduction r * halve x := by
  rcases hx with hx | hx <;> subst x <;> fin_cases r <;> decide

private theorem left_range_cases (x : HL) : (x : R) = 0 ∨ (x : R) = 2 := by
  obtain ⟨a, ha⟩ := x.property
  have hv : twiceLeft.hom a = 0 ∨ twiceLeft.hom a = 2 := by
    change (2 : R) * a = 0 ∨ (2 : R) * a = 2
    fin_cases a <;> decide
  exact hv.imp (fun h => ha.symm.trans h) (fun h => ha.symm.trans h)

private def halfLeft : HL →+ S where
  toFun x := halve (x : R)
  map_zero' := by change halve (0 : R) = 0; decide
  map_add' x y := halve_add (x : R) (y : R) (left_range_cases x) (left_range_cases y)

private def halfLeftLinear :
    letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
    HL →ₗ[ℤ] U := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  exact
    { toFun := halfLeft
      map_add' := halfLeft.map_add
      map_smul' := fun z x => by
        change halfLeft ((algebraMap ℤ R z) • x) = z • halfLeft x
        exact map_intCast_smul halfLeft R ℤ z x }

private def leftPairing :
    letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
    U →ₗ[ℤ] HL →ₗ[ℤ] U := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  let mul : U →ₗ[ℤ] U →ₗ[ℤ] U :=
    (Algebra.lsmul ℤ ℤ U : U →ₐ[ℤ] Module.End ℤ U).toLinearMap
  exact (mul.comp halfLeftLinear).flip

private theorem leftPairing_balanced :
    letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
    ∀ (r : R) (x : U) (y : HL),
      leftPairing (MulOpposite.op r • x) y = leftPairing x (r • y) := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  intro r x y
  change halve (y : R) * (reduction r * x) = halve (r * (y : R)) * x
  have hy : halve (r * (y : R)) = reduction r * halve (y : R) := by
    rw [mul_comm r (y : R)]
    exact halve_mul (y : R) r (left_range_cases y)
  rw [hy]
  exact (mul_assoc (halve (y : R)) (reduction r) x).symm.trans
    (congrArg (fun z : S => z * x) (mul_comm (halve (y : R)) (reduction r)))

private def leftTensorEvaluation :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj U).obj HL ⟶ AddCommGrpCat.of S := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  exact AddCommGrpCat.ofHom
    (TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := U) (N := HL)
      leftPairing leftPairing_balanced).toAddMonoidHom

private theorem leftTensorEvaluation_mk (x : U) (y : HL) :
    letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
    leftTensorEvaluation.hom (TensorProduct.Balanced.mk ℤ R U HL x y) = halve (y : R) * x := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  change TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := U) (N := HL)
    leftPairing leftPairing_balanced (TensorProduct.Balanced.mk ℤ R U HL x y) = _
  rw [TensorProduct.Balanced.lift_mk]
  rfl

private def leftTwo : HL :=
  ⟨2, ⟨1, by change (2 : R) * 1 = 2; exact mul_one 2⟩⟩

private abbrev G : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
  (ModuleCat.BalancedTensor.groupBifunctor R).obj U

private def leftGenerator : G.obj HL := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  exact TensorProduct.Balanced.mk ℤ R U HL 1 leftTwo

private theorem leftGenerator_value : leftTensorEvaluation.hom leftGenerator = 1 := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  rw [leftGenerator, leftTensorEvaluation_mk]
  decide

private def leftInclusion : HL ⟶ ZL := ModuleCat.ofHom twiceLeft.hom.range.subtype

private instance leftInclusion_mono : Mono leftInclusion :=
  (ModuleCat.mono_iff_injective leftInclusion).2 Subtype.val_injective

private def regularRightIso : G.obj ZL ≅ AddCommGrpCat.of S := by
  letI : Module ℤ ZL := Module.compHom ZL (algebraMap ℤ R)
  exact (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso
    (TensorProduct.Balanced.rightUnitor ℤ R U).toModuleIso

private theorem regularRightIso_mk (x : U) (r : ZL) :
    letI : Module ℤ ZL := Module.compHom ZL (algebraMap ℤ R)
    regularRightIso.hom.hom (TensorProduct.Balanced.mk ℤ R U ZL x r) = MulOpposite.op (r : R) • x :=
  TensorProduct.Balanced.rightUnitor_mk ℤ R U x r

private theorem leftGenerator_kernel : (G.map leftInclusion).hom leftGenerator = 0 := by
  letI : Module ℤ HL := Module.compHom HL (algebraMap ℤ R)
  letI : Module ℤ ZL := Module.compHom ZL (algebraMap ℤ R)
  apply (AddCommGrpCat.mono_iff_injective regularRightIso.hom).1 inferInstance
  change regularRightIso.hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor R).obj U).map leftInclusion).hom
      (TensorProduct.Balanced.mk ℤ R U HL 1 leftTwo)) = regularRightIso.hom.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk, regularRightIso_mk]
  change reduction (2 : R) * (1 : S) = 0
  decide

private theorem leftGenerator_nonzero : leftGenerator ≠ 0 := by
  intro h
  have hv := congrArg leftTensorEvaluation.hom h
  rw [leftGenerator_value, map_zero] at hv
  exact (by decide : (1 : S) ≠ 0) hv

private theorem residue_tensor_not_mono : ¬ Mono (G.map leftInclusion) := by
  intro h
  have hz := (AddCommGrpCat.mono_iff_injective (G.map leftInclusion)).1 h
    (leftGenerator_kernel.trans (G.map leftInclusion).hom.map_zero.symm)
  exact leftGenerator_nonzero hz

theorem residue_right_tensor_not_exact : ¬ G.PreservesHomology := by
  intro h
  let : G.PreservesHomology := h
  let : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
  let : Mono (G.map leftInclusion) := inferInstance
  exact residue_tensor_not_mono inferInstance

theorem mixed_term_tensor_not_exact :
    ¬ ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X 1)).PreservesHomology := by
  intro h
  let F : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).obj K
  let : F.PreservesHomology := h
  let : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  let : Mono (F.map leftInclusion) := inferInstance
  let η : G ⟶ F := (ModuleCat.BalancedTensor.groupBifunctor R).map (biprod.inr : U ⟶ K)
  let π : F ⟶ G := (ModuleCat.BalancedTensor.groupBifunctor R).map (biprod.snd : K ⟶ U)
  have hηπ : η ≫ π = 𝟙 G := by
    change (ModuleCat.BalancedTensor.groupBifunctor R).map (biprod.inr : U ⟶ K) ≫
      (ModuleCat.BalancedTensor.groupBifunctor R).map (biprod.snd : K ⟶ U) = _
    rw [← (ModuleCat.BalancedTensor.groupBifunctor R).map_comp, biprod.inr_snd,
      (ModuleCat.BalancedTensor.groupBifunctor R).map_id]
  have hsplit : η.app HL ≫ π.app HL = 𝟙 (G.obj HL) :=
    congrArg (fun t : G ⟶ G => t.app HL) hηπ
  let : Mono (η.app HL) := mono_of_mono_fac hsplit
  have hh := ConcreteCategory.congr_hom (η.naturality leftInclusion) leftGenerator
  change (η.app ZL).hom ((G.map leftInclusion).hom leftGenerator) =
    (F.map leftInclusion).hom ((η.app HL).hom leftGenerator) at hh
  rw [leftGenerator_kernel, map_zero] at hh
  have hz := (AddCommGrpCat.mono_iff_injective (F.map leftInclusion)).1 inferInstance
    (hh.symm.trans (F.map leftInclusion).hom.map_zero.symm)
  have hx := (AddCommGrpCat.mono_iff_injective (η.app HL)).1 inferInstance
    (hz.trans (η.app HL).hom.map_zero.symm)
  exact leftGenerator_nonzero hx

private def outgoingImageIsoZero : Abelian.image (P.d 1 0) ≅ U := by
  let : Epi (P.d 1 0) := by rw [differential_one]; infer_instance
  let : Epi (Abelian.image.ι (P.d 1 0)) := epi_of_epi_fac (Abelian.image.fac (P.d 1 0))
  let : IsIso (Abelian.image.ι (P.d 1 0)) := inferInstance
  exact asIso (Abelian.image.ι (P.d 1 0))

private def outgoingImageIso : Abelian.image (P.d 1 ((ComplexShape.down ℤ).next 1)) ≅ U :=
  eqToIso (congrArg (fun k : ℤ => Abelian.image (P.d 1 k)) next_one) ≪≫ outgoingImageIsoZero

theorem outgoing_image_tensor_not_exact :
    ¬ ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image (P.d 1 ((ComplexShape.down ℤ).next 1)))).PreservesHomology := by
  intro h
  let F : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image (P.d 1 ((ComplexShape.down ℤ).next 1)))
  let : F.PreservesHomology := h
  let : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  let : Mono (F.map leftInclusion) := inferInstance
  let e : F ≅ G := (ModuleCat.BalancedTensor.groupBifunctor R).mapIso outgoingImageIso
  have he : G.map leftInclusion = (e.app HL).inv ≫ F.map leftInclusion ≫ (e.app ZL).hom := by
    apply (cancel_epi (e.app HL).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (e.hom.naturality leftInclusion).symm
  let : Mono (G.map leftInclusion) := by rw [he]; infer_instance
  exact residue_tensor_not_mono inferInstance



private abbrev B := Abelian.image (P.d 2 1)
private abbrev HR : ModuleCat.{0} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ twice.hom.range

private def β : B ⟶ P.cycles 1 := HomologicalComplex.boundaryCyclesMap P 2 1
private def boundaryToFree : B ⟶ Z := β ≫ cyclesIso.hom

private theorem boundaryToFree_inl :
    boundaryToFree ≫ (biprod.inl : Z ⟶ K) = Abelian.image.ι (P.d 2 1) := by
  rw [boundaryToFree, Category.assoc, cyclesIso_hom_inl]
  exact HomologicalComplex.boundaryCyclesMap_i P 2 1

private theorem factor_boundaryToFree :
    Abelian.factorThruImage (P.d 2 1) ≫ boundaryToFree = twice := by
  apply (cancel_mono (biprod.inl : Z ⟶ K)).1
  rw [Category.assoc, boundaryToFree_inl, Abelian.image.fac, differential_two]
  rfl

private def boundaryRangeIso : B ≅ HR := by
  let : Mono β := mono_of_mono_fac (HomologicalComplex.boundaryCyclesMap_i P 2 1)
  let : Mono boundaryToFree := inferInstance
  let : StrongEpi (Abelian.factorThruImage (P.d 2 1)) :=
    (Abelian.imageStrongEpiMonoFactorisation (P.d 2 1)).e_strong_epi
  exact image.isoStrongEpiMono (Abelian.factorThruImage (P.d 2 1)) boundaryToFree
      factor_boundaryToFree ≪≫ ModuleCat.imageIsoRange twice

private theorem boundaryRangeIso_ι :
    boundaryRangeIso.hom ≫ ModuleCat.ofHom twice.hom.range.subtype = boundaryToFree := by
  let : Mono β := mono_of_mono_fac (HomologicalComplex.boundaryCyclesMap_i P 2 1)
  let : Mono boundaryToFree := inferInstance
  let : StrongEpi (Abelian.factorThruImage (P.d 2 1)) :=
    (Abelian.imageStrongEpiMonoFactorisation (P.d 2 1)).e_strong_epi
  change (image.isoStrongEpiMono (Abelian.factorThruImage (P.d 2 1)) boundaryToFree
      factor_boundaryToFree).hom ≫ (ModuleCat.imageIsoRange twice).hom ≫
        ModuleCat.ofHom twice.hom.range.subtype = boundaryToFree
  rw [Category.assoc, ModuleCat.imageIsoRange_hom_subtype]
  exact image.isoStrongEpiMono_hom_comp_ι _ _ _

private theorem right_range_cases (x : HR) : (x : R) = 0 ∨ (x : R) = 2 := by
  obtain ⟨a, ha⟩ := x.property
  have hv : twice.hom a = 0 ∨ twice.hom a = 2 := by
    change (2 : R) * a = 0 ∨ (2 : R) * a = 2
    fin_cases a <;> decide
  exact hv.imp (fun h => ha.symm.trans h) (fun h => ha.symm.trans h)

private def halfRight : HR →+ S where
  toFun x := halve (x : R)
  map_zero' := by change halve (0 : R) = 0; decide
  map_add' x y := halve_add (x : R) (y : R) (right_range_cases x) (right_range_cases y)

private def halfRightLinear :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    HR →ₗ[ℤ] N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact
    { toFun := halfRight
      map_add' := halfRight.map_add
      map_smul' := fun z x => by
        change halfRight (z • x) = (algebraMap ℤ R z) • halfRight x
        exact map_intCast_smul halfRight ℤ R z x }

private def rightPairing :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    HR →ₗ[ℤ] N →ₗ[ℤ] N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let mul : N →ₗ[ℤ] N →ₗ[ℤ] N :=
    (Algebra.lsmul ℤ ℤ N : N →ₐ[ℤ] Module.End ℤ N).toLinearMap
  exact mul.comp halfRightLinear

private theorem rightPairing_balanced :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    ∀ (r : R) (x : HR) (y : N),
      rightPairing (MulOpposite.op r • x) y = rightPairing x (r • y) := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  intro r x y
  change halve ((x : R) * r) * y = halve (x : R) * (reduction r * y)
  rw [halve_mul (x : R) r (right_range_cases x)]
  exact (congrArg (fun z : S => z * y) (mul_comm (reduction r) (halve (x : R)))).trans
    (mul_assoc (halve (x : R)) (reduction r) y)

private def rightTensorEvaluation :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj HR).obj N ⟶ AddCommGrpCat.of S := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact AddCommGrpCat.ofHom
    (TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := HR) (N := N)
      rightPairing rightPairing_balanced).toAddMonoidHom

private theorem rightTensorEvaluation_mk (x : HR) (y : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    rightTensorEvaluation.hom (TensorProduct.Balanced.mk ℤ R HR N x y) = halve (x : R) * y := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change TensorProduct.Balanced.lift (k := ℤ) (R := R) (M := HR) (N := N)
    rightPairing rightPairing_balanced (TensorProduct.Balanced.mk ℤ R HR N x y) = _
  rw [TensorProduct.Balanced.lift_mk]
  rfl

private def boundaryOne : B := (Abelian.factorThruImage (P.d 2 1)).hom 1
private def rightTwo : HR := ⟨2, ⟨1, by change (2 : R) * 1 = 2; exact mul_one 2⟩⟩

private theorem boundaryOne_free_value : boundaryToFree.hom boundaryOne = 2 := by
  have h := ConcreteCategory.congr_hom factor_boundaryToFree (1 : R)
  exact h.trans (mul_one 2)

private theorem boundaryOne_range_value : boundaryRangeIso.hom.hom boundaryOne = rightTwo := by
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom boundaryRangeIso_ι boundaryOne
  exact h.trans boundaryOne_free_value

private abbrev T := ((ModuleCat.BalancedTensor.groupBifunctor R).obj B).obj N
private def tensorInclusion : T ⟶
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles 1)).obj N :=
  ((ModuleCat.BalancedTensor.groupBifunctor R).map β).app N

private def sourceOne : T := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact TensorProduct.Balanced.mk ℤ R B N boundaryOne 1

private def sourceEvaluate : T ⟶ AddCommGrpCat.of S :=
  ((ModuleCat.BalancedTensor.groupBifunctor R).map boundaryRangeIso.hom).app N ≫
    rightTensorEvaluation

private theorem sourceOne_value : sourceEvaluate.hom sourceOne = 1 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change rightTensorEvaluation.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor R).map boundaryRangeIso.hom).app N).hom
      (TensorProduct.Balanced.mk ℤ R B N boundaryOne 1)) = 1
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, boundaryOne_range_value,
    rightTensorEvaluation_mk]
  decide

private def regularLeftIso :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj Z).obj N ≅ AddCommGrpCat.of S := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  exact (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso
    (TensorProduct.Balanced.leftUnitor ℤ R N).toModuleIso

private theorem regularLeftIso_mk (r : Z) (x : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    regularLeftIso.hom.hom (TensorProduct.Balanced.mk ℤ R Z N r x) = (r : R) • x :=
  TensorProduct.Balanced.leftUnitor_mk ℤ R N r x

private theorem sourceOne_kernel : tensorInclusion.hom sourceOne = 0 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let e := ((ModuleCat.BalancedTensor.groupBifunctor R).map cyclesIso.hom).app N ≫
    regularLeftIso.hom
  let : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change regularLeftIso.hom.hom
    ((((ModuleCat.BalancedTensor.groupBifunctor R).map cyclesIso.hom).app N).hom
      ((((ModuleCat.BalancedTensor.groupBifunctor R).map β).app N).hom
        (TensorProduct.Balanced.mk ℤ R B N boundaryOne 1))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk]
  change regularLeftIso.hom.hom
    (TensorProduct.Balanced.mk ℤ R Z N (boundaryToFree.hom boundaryOne) 1) = 0
  rw [boundaryOne_free_value, regularLeftIso_mk]
  change reduction (2 : R) * (1 : S) = 0
  decide

private def sourceOneMap : AddCommGrpCat.of ℤ ⟶ T := AddCommGrpCat.ofHom
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

private def torClass :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology 1)).obj N :=
  kernelComparison.inv.hom (kernelOneMap.hom 1)

private theorem torClass_boundary : (torBoundary R P N 2 1 prev_one).hom torClass = sourceOne := by
  have h₁ := ConcreteCategory.congr_hom
    (torBoundaryKernelIsoOfCyclesMapZero_inv_boundary R P N 2 1 prev_one
      upstream_cycles_map_zero) (kernelOneMap.hom 1)
  have h₂ := ConcreteCategory.congr_hom
    (kernel.lift_ι tensorInclusion sourceOneMap sourceOneMap_zero) (1 : ℤ)
  exact h₁.trans (h₂.trans (one_zsmul sourceOne))

theorem canonical_boundary_value :
    sourceEvaluate.hom ((torBoundary R P N 2 1 prev_one).hom torClass) = 1 := by
  rw [torClass_boundary, sourceOne_value]

theorem nonzero_tor_class : torClass ≠ 0 := by
  intro h
  have hv := congrArg (fun x => sourceEvaluate.hom ((torBoundary R P N 2 1 prev_one).hom x)) h
  rw [canonical_boundary_value, map_zero, map_zero] at hv
  exact (by decide : (1 : S) ≠ 0) hv


end MathlibExtTest.TorBoundaryKernelCriterion
