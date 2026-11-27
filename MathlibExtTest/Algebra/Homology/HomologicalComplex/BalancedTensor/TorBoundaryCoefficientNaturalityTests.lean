/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundaryCoefficientNaturality
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.Algebra.Category.ModuleCat.RegularElementTor
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Reduction of a nonzero Tor boundary from ZMod 6 to ZMod 2

The right integer complex has regular terms and multiplication by two
from degree zero to degree minus one. The principal-quotient presentation
of ℤ/2 supplies that multiplication map and the projectivity of its regular
term. Its selected term and outgoing image are projective. The tensor-inclusion kernel for the coefficient
ℤ/6 contains the class with normalized boundary coordinate three.
The canonical kernel comparison gives a Tor class whose actual boundary
is that tensor class.

Reduction ℤ/6 → ℤ/2 sends three to one. Both routes around the coefficient
naturality square have this nonzero boundary coordinate. The right complex
starts in carrier universe zero and both left coefficients in universe
one; their common working height is two. The lifted factory and the native
natural transformation are used on the same concrete class.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.TorBoundaryCoefficientNaturality

private abbrev c := ComplexShape.down ℤ
private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ

private def rightRegularEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def regularIso : ModuleCat.RegularElement.rightRegular.{0, 0} ℤ ≅ Z :=
  ((ULift.moduleEquiv : ModuleCat.RegularElement.rightRegular.{0, 0} ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ).trans
    rightRegularEquiv).toModuleIso

private lemma twoRegular : IsLeftRegular (2 : ℤ) := by
  intro x y h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

private def twice : Z ⟶ Z :=
  regularIso.inv ≫ ModuleCat.RegularElement.leftMultiplication.{0, 0} ℤ 2 ≫ regularIso.hom

private instance twiceMono : Mono twice := by
  letI : Mono (ModuleCat.RegularElement.leftMultiplication.{0, 0} ℤ 2) :=
    (ModuleCat.RegularElement.leftMultiplication_mono_iff.{0, 0} ℤ 2).2 twoRegular
  dsimp only [twice]
  infer_instance

private def d (i : ℤ) : Z ⟶ Z := if i = -1 then twice else 0

private lemma d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases h : i = -1
  · subst i
    simp [d]
  · simp [d, h]

private def P : ChainComplex (ModuleCat.{0} ℤᵐᵒᵖ) ℤ :=
  ChainComplex.of (fun _ : ℤ => Z) d d_sq

private lemma differential_value (x : ℤ) : (P.d 0 (-1)).hom x = 2 * x := by
  change (ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1)).hom x = _
  simpa only [ChainComplex.of_d] using (show (d (-1)).hom x = 2 * x from rfl)

private lemma next_int (i : ℤ) : c.next i = i - 1 :=
  c.next_eq' (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private lemma incoming : c.prev (-1) = 0 :=
  c.prev_eq' (by change (-1 : ℤ) + 1 = 0; norm_num)

private lemma outgoing_zero : P.d (-1) (c.next (-1)) = 0 := by
  have h : P.d (-1) (-2) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-2 : ℤ) + 1) (-2) = 0
    simpa only [ChainComplex.of_d] using (show d (-2) = 0 from rfl)
  exact (congrArg (fun j : ℤ => (show Z ⟶ Z from P.d (-1) j)) (next_int (-1))).trans h

private abbrev ZL : ModuleCat.{2} ℤᵐᵒᵖ :=
  (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).obj Z

private abbrev PL : ChainComplex (ModuleCat.{2} ℤᵐᵒᵖ) ℤ :=
  ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).mapHomologicalComplex c).obj P

private abbrev N₆ : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ (ZMod 6))

private abbrev N₂ : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ (ZMod 2))

private abbrev NL₆ : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N₆
private abbrev NL₂ : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N₂

private def reduction : ZMod 6 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)

private def g₀ : ModuleCat.of ℤ (ZMod 6) ⟶ ModuleCat.of ℤ (ZMod 2) :=
  ModuleCat.ofHom reduction.toAddMonoidHom.toIntLinearMap

private abbrev g₁ : N₆ ⟶ N₂ := (ModuleCat.uliftFunctor.{1, 0} ℤ).map g₀
private abbrev gL : NL₆ ⟶ NL₂ := (ModuleCat.uliftFunctor.{2, 1} ℤ).map g₁

private def three : NL₆ := ULift.up (ULift.up (3 : ZMod 6))
private def one : NL₂ := ULift.up (ULift.up (1 : ZMod 2))

private lemma reduction_three : reduction (3 : ZMod 6) = 1 := by decide

private lemma gL_three : gL.hom three = one := by
  change ULift.up (ULift.up (reduction (3 : ZMod 6))) = ULift.up (ULift.up (1 : ZMod 2))
  apply ULift.ext
  apply ULift.ext
  exact reduction_three

private def regularIsoL : ModuleCat.RegularElement.rightRegular.{0, 2} ℤ ≅ ZL :=
  (((ULift.moduleEquiv : ModuleCat.RegularElement.rightRegular.{0, 2} ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ).trans
    rightRegularEquiv).trans (ULift.moduleEquiv : ZL ≃ₗ[ℤᵐᵒᵖ] ℤ).symm).toModuleIso

private instance liftedProjective : Projective ZL :=
  Projective.of_iso regularIsoL
    ((ModuleCat.RegularElement.projectiveResolution.{0, 2} ℤ 2 twoRegular).projective 0)

private lemma lifted_outgoing_zero : PL.d (-1) (c.next (-1)) = 0 := by
  change (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d (-1) (c.next (-1))) = 0
  rw [outgoing_zero, Functor.map_zero]

private abbrev G := ModuleCat.BalancedTensor.groupBifunctor ℤ

private instance termExact : (G.obj (PL.X (-1))).PreservesHomology := by
  change (G.obj ZL).PreservesHomology
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ ZL

private instance outgoingExact :
    (G.obj (Abelian.image (PL.d (-1) (c.next (-1))))).PreservesHomology := by
  let e := Abelian.imageIsoImage (0 : ZL ⟶ ZL) ≪≫ ModuleCat.imageIsoRange (0 : ZL ⟶ ZL)
  have hz : IsZero (ModuleCat.of ℤᵐᵒᵖ (0 : ZL ⟶ ZL).hom.range) := by
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact ModuleCat.isZero_iff_subsingleton.2 inferInstance
  let : Projective (Abelian.image (PL.d (-1) (c.next (-1)))) := by
    rw [lifted_outgoing_zero]
    exact Projective.of_iso e.symm hz.projective
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ _

private abbrev f : ZL ⟶ ZL := PL.d 0 (-1)
private abbrev B : ModuleCat.{2} ℤᵐᵒᵖ := Abelian.image f
private def oneZ : ZL := ULift.up (1 : ℤ)

private lemma f_apply (x : ZL) : f.hom x = ULift.up (2 * x.down) := by
  change ULift.up ((P.d 0 (-1)).hom x.down) = _
  rw [differential_value]

private instance f_mono : Mono f := by
  change Mono ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d 0 (-1)))
  have hd : P.d 0 (-1) = twice := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1) = twice
    simpa only [ChainComplex.of_d] using (show d (-1) = twice from rfl)
  rw [hd]
  infer_instance

private def imageIso : ZL ≅ B := asIso (Abelian.factorThruImage f)
private def imageOne : B := (Abelian.factorThruImage f).hom oneZ

private lemma imageOne_normalized : imageIso.inv.hom imageOne = oneZ :=
  ConcreteCategory.congr_hom imageIso.hom_inv_id oneZ

private def cyclesIso : PL.cycles (-1) ≅ ZL :=
  PL.iCyclesIso (-1) (c.next (-1)) rfl lifted_outgoing_zero

private abbrev β : B ⟶ PL.cycles (-1) := HomologicalComplex.boundaryCyclesMap PL 0 (-1)

private lemma β_value : cyclesIso.hom.hom (β.hom imageOne) = ULift.up (2 : ℤ) := by
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.boundaryCyclesMap_i PL 0 (-1)) imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) oneZ
  change (PL.iCycles (-1)).hom (β.hom imageOne) = ULift.up (2 : ℤ)
  exact h₁.trans (h₂.trans (by simpa only [oneZ, mul_one] using f_apply oneZ))

private def regularTensorIso (W : ModuleCat.{2} ℤ) :
    (G.obj ZL).obj W ≅ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj W :=
  (G.flip.obj W).mapIso regularIsoL.symm ≪≫
    ModuleCat.RegularElement.regularTensorIso.{0, 2} ℤ W

private lemma regularTensorIso_mk (W : ModuleCat.{2} ℤ) (x : ZL) (w : W) :
    letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
    (regularTensorIso W).hom.hom (TensorProduct.Balanced.mk ℤ ℤ ZL W x w) = x.down • w := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  change (ModuleCat.RegularElement.regularTensorIso.{0, 2} ℤ W).hom.hom
    (((G.map regularIsoL.inv).app W).hom (TensorProduct.Balanced.mk ℤ ℤ ZL W x w)) = x.down • w
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.RegularElement.regularTensorIso_mk]
  rfl

private def boundaryEval (W : ModuleCat.{2} ℤ) :
    (G.obj B).obj W ⟶ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj W :=
  (G.map imageIso.inv).app W ≫ (regularTensorIso W).hom

private def boundaryPoint (W : ModuleCat.{2} ℤ) (w : W) : (G.obj B).obj W :=
  ModuleCat.BalancedTensor.groupPure ℤ B W imageOne w

private lemma boundaryPoint_value (W : ModuleCat.{2} ℤ) (w : W) :
    (boundaryEval W).hom (boundaryPoint W w) = w := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  change (regularTensorIso W).hom.hom
    (((G.map imageIso.inv).app W).hom (TensorProduct.Balanced.mk ℤ ℤ B W imageOne w)) = w
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, imageOne_normalized,
    regularTensorIso_mk]
  change (1 : ℤ) • w = w
  exact one_smul ℤ w

private abbrev T₆ := (G.obj B).obj NL₆
private abbrev T₂ := (G.obj B).obj NL₂
private abbrev θ₆ : T₆ := boundaryPoint NL₆ three
private abbrev θ₂ : T₂ := boundaryPoint NL₂ one

private abbrev tensorInclusion : T₆ ⟶ (G.obj (PL.cycles (-1))).obj NL₆ :=
  (G.map β).app NL₆

private lemma θ₆_kernel : tensorInclusion.hom θ₆ = 0 := by
  letI : Module ℤ NL₆ := Module.compHom NL₆ (algebraMap ℤ ℤ)
  let e : (G.obj (PL.cycles (-1))).obj NL₆ ⟶
      (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj NL₆ :=
    (G.map cyclesIso.hom).app NL₆ ≫ (regularTensorIso NL₆).hom
  let : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change (regularTensorIso NL₆).hom.hom
    (((G.map cyclesIso.hom).app NL₆).hom
      (((G.map β).app NL₆).hom (TensorProduct.Balanced.mk ℤ ℤ B NL₆ imageOne three))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, β_value, regularTensorIso_mk]
  change (2 : ℤ) • three = 0
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • (3 : ZMod 6) = 0
  decide

private abbrev J : AddCommGrpCat.{2} := AddCommGrpCat.of ZL

private def pointMap : J ⟶ T₆ := AddCommGrpCat.ofHom
  ((zmultiplesHom θ₆).comp (ULift.moduleEquiv : ZL ≃ₗ[ℤ] ℤ).toAddEquiv.toAddMonoidHom)

private lemma pointMap_apply (x : J) : pointMap.hom x = x.down • θ₆ := rfl

private lemma pointMap_zero : pointMap ≫ tensorInclusion = 0 := by
  apply ConcreteCategory.ext_apply
  intro x
  change tensorInclusion.hom (pointMap.hom x) = 0
  rw [pointMap_apply, map_zsmul, θ₆_kernel, smul_zero]

private def kernelPointMap : J ⟶ kernel tensorInclusion :=
  kernel.lift tensorInclusion pointMap pointMap_zero

private def kernelPoint : kernel tensorInclusion := kernelPointMap.hom oneZ

private lemma kernelPoint_ι : (kernel.ι tensorInclusion).hom kernelPoint = θ₆ := by
  have h := ConcreteCategory.congr_hom (kernel.lift_ι tensorInclusion pointMap pointMap_zero) oneZ
  change (kernel.ι tensorInclusion).hom kernelPoint = pointMap.hom oneZ at h
  exact h.trans (by rw [pointMap_apply]; change (1 : ℤ) • θ₆ = θ₆; exact one_zsmul θ₆)

private def kernelComparison :
    ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology (-1))).obj NL₆ ≅
      kernel tensorInclusion :=
  torBoundaryKernelIso ℤ PL NL₆ 0 (-1) incoming

private def τ : ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology (-1))).obj NL₆ :=
  kernelComparison.inv.hom kernelPoint

private abbrev δ₆ := torBoundary ℤ PL NL₆ 0 (-1) incoming
private abbrev δ₂ := torBoundary ℤ PL NL₂ 0 (-1) incoming
private abbrev torMap := ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology (-1))).map gL
private abbrev tensorMap : T₆ ⟶ T₂ := (G.obj B).map gL

private lemma τ_boundary : δ₆.hom τ = θ₆ := by
  have h := ConcreteCategory.congr_hom
    (torBoundaryKernelIso_inv_boundary ℤ PL NL₆ 0 (-1) incoming) kernelPoint
  exact h.trans kernelPoint_ι

private lemma tensorMap_point : tensorMap.hom θ₆ = θ₂ := by
  letI : Module ℤ NL₆ := Module.compHom NL₆ (algebraMap ℤ ℤ)
  letI : Module ℤ NL₂ := Module.compHom NL₂ (algebraMap ℤ ℤ)
  change ((G.obj B).map gL).hom (TensorProduct.Balanced.mk ℤ ℤ B NL₆ imageOne three) =
    TensorProduct.Balanced.mk ℤ ℤ B NL₂ imageOne one
  rw [ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk, gL_three]

private lemma tensor_route : tensorMap.hom (δ₆.hom τ) = θ₂ := by
  rw [τ_boundary, tensorMap_point]

private lemma derived_route : δ₂.hom (torMap.hom τ) = θ₂ := by
  have h := ConcreteCategory.congr_hom (torBoundary_coeff_naturality ℤ PL gL 0 (-1) incoming) τ
  exact h.trans tensor_route

private def residue₆ (x : NL₆) : ZMod 6 := x.down.down
private def residue₂ (x : NL₂) : ZMod 2 := x.down.down

private lemma source_boundary_value : residue₆ ((boundaryEval NL₆).hom (δ₆.hom τ)) = 3 := by
  rw [τ_boundary, boundaryPoint_value]
  rfl

private lemma tensor_route_value :
    residue₂ ((boundaryEval NL₂).hom (tensorMap.hom (δ₆.hom τ))) = 1 := by
  rw [tensor_route, boundaryPoint_value]
  rfl

private lemma derived_route_value :
    residue₂ ((boundaryEval NL₂).hom (δ₂.hom (torMap.hom τ))) = 1 := by
  rw [derived_route, boundaryPoint_value]
  rfl

example : gL.hom three = one := gL_three

example : residue₆ ((boundaryEval NL₆).hom (δ₆.hom τ)) = 3 := source_boundary_value

example : residue₂ ((boundaryEval NL₂).hom (tensorMap.hom (δ₆.hom τ))) = 1 :=
  tensor_route_value

example : residue₂ ((boundaryEval NL₂).hom (δ₂.hom (torMap.hom τ))) = 1 := derived_route_value

example :
    residue₂ ((boundaryEval NL₂).hom
      (((torBoundaryCoeffNatTrans ℤ PL 0 (-1) incoming).app NL₂).hom (torMap.hom τ))) = 1 := by
  have h := ConcreteCategory.congr_hom
    ((torBoundaryCoeffNatTrans ℤ PL 0 (-1) incoming).naturality gL) τ
  change δ₂.hom (torMap.hom τ) = tensorMap.hom (δ₆.hom τ) at h
  change residue₂ ((boundaryEval NL₂).hom (δ₂.hom (torMap.hom τ))) = 1
  rw [h]
  exact tensor_route_value

example :
    residue₂ ((boundaryEval NL₂).hom
      ((torBoundaryAt ℤ P N₂ 0 (-1) incoming).hom (torMap.hom τ))) = 1 := by
  have hsquare : torMap ≫ torBoundaryAt ℤ P N₂ 0 (-1) incoming =
      torBoundaryAt ℤ P N₆ 0 (-1) incoming ≫ tensorMap :=
    torBoundaryAt_coeff_naturality ℤ P g₁ 0 (-1) incoming
  have h := ConcreteCategory.congr_hom hsquare τ
  change (torBoundaryAt ℤ P N₂ 0 (-1) incoming).hom (torMap.hom τ) =
    tensorMap.hom (δ₆.hom τ) at h
  rw [h]
  exact tensor_route_value

example : τ ≠ 0 ∧ torMap.hom τ ≠ 0 ∧ δ₆.hom τ ≠ 0 ∧ δ₂.hom (torMap.hom τ) ≠ 0 := by
  have hδ₆ : δ₆.hom τ ≠ 0 := by
    intro h
    have hv := source_boundary_value
    rw [h, map_zero] at hv
    change (0 : ZMod 6) = 3 at hv
    exact (by decide : (0 : ZMod 6) ≠ 3) hv
  have hδ₂ : δ₂.hom (torMap.hom τ) ≠ 0 := by
    intro h
    have hv := derived_route_value
    rw [h, map_zero] at hv
    change (0 : ZMod 2) = 1 at hv
    exact (by decide : (0 : ZMod 2) ≠ 1) hv
  refine ⟨?_, ?_, hδ₆, hδ₂⟩
  · intro h
    apply hδ₆
    rw [h, map_zero]
  · intro h
    apply hδ₂
    rw [h, map_zero]

end MathlibExtTest.TorBoundaryCoefficientNaturality
