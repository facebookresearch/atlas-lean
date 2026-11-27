/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorColimits
import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroNaturality
import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundary
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.Algebra.Category.ModuleCat.RegularElementTor
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.LeftGroupAdjunction
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Degree-one coefficient colimits with nonflat integer torsion

The right integer complex has ℤ in every integer degree and multiplication
by two from degree zero to degree minus one. The principal-quotient
presentation of ℤ/2 supplies that map and the projectivity of the regular
term. Let A be its homology in degree minus one after the canonical lift
to universe two.

The coefficient diagram has two discrete objects, ℤ/4 and ℤ/6, with
carriers lifted first to universe one and then to universe two. Its target
has ℤ/2 at each object. Reduction modulo two gives the diagram morphism.

The native Tor boundary kernel comparison gives order-two classes in
Tor₁(A,ℤ/4), Tor₁(A,ℤ/6), and Tor₁(A,ℤ/2) with normalized boundary
coordinates two, three, and one. Reduction sends the first class to zero
and the second to the third class.

The sum of the first two classes defines a class in Tor₁(A,colim K)
through the canonical derived coefficient-colimit comparison. Both paths
in coefficient-diagram naturality send it to the right coproduct class
with coordinates (0,1). The class and both images are nonzero.

The right complex starts in carrier universe zero, its coefficients in
universe one, and the comparison uses common universe two. The regular
right terms and the zero outgoing image supply projectivity; exact
coproducts of abelian groups supply the colimit hypothesis. Neither
torsion coefficient is flat over ℤ.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.DerivedCoefficientColimit

local notation "c" => ComplexShape.down ℤ

private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ

private abbrev Z2 : ModuleCat.{2} ℤᵐᵒᵖ := (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).obj Z

private def rightRegularEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] Z2 where
  toFun r := ULift.up r.unop
  invFun z := MulOpposite.op z.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def regularIso : ModuleCat.RegularElement.rightRegular.{0, 0} ℤ ≅ Z :=
  (((ULift.moduleEquiv : ModuleCat.RegularElement.rightRegular.{0, 0} ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ).trans
    rightRegularEquiv).trans (ULift.moduleEquiv : Z2 ≃ₗ[ℤᵐᵒᵖ] ℤ)).toModuleIso

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

private lemma incoming : c.prev (-1) = 0 :=
  c.prev_eq' (by change (-1 : ℤ) + 1 = 0; norm_num)

private lemma next_int (i : ℤ) : c.next i = i - 1 :=
  c.next_eq' (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private lemma differential_value (a : ℤ) : (P.d 0 (-1)).hom a = 2 * a := by
  change (ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1)).hom a = _
  simpa only [ChainComplex.of_d] using (show (d (-1)).hom a = 2 * a from rfl)

private lemma outgoing_zero : P.d (-1) (c.next (-1)) = 0 := by
  have h : P.d (-1) (-2) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-2 : ℤ) + 1) (-2) = 0
    simpa only [ChainComplex.of_d] using (show d (-2) = 0 from rfl)
  exact (congrArg (fun j : ℤ => (show Z ⟶ Z from P.d (-1) j)) (next_int (-1))).trans h

private abbrev P2 : ChainComplex (ModuleCat.{2} ℤᵐᵒᵖ) ℤ :=
  ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).mapHomologicalComplex c).obj P

private def regularIso2 : ModuleCat.RegularElement.rightRegular.{0, 2} ℤ ≅ Z2 :=
  ((ULift.moduleEquiv : ModuleCat.RegularElement.rightRegular.{0, 2} ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ).trans
    rightRegularEquiv).toModuleIso

private instance regular_projective : Projective Z2 :=
  Projective.of_iso regularIso2
    ((ModuleCat.RegularElement.projectiveResolution.{0, 2} ℤ 2 twoRegular).projective 0)

private instance term_exact :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P2.X (-1))).PreservesHomology := by
  change ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj Z2).PreservesHomology
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ Z2

private lemma outgoing_lifted_zero : P2.d (-1) (c.next (-1)) = 0 := by
  change (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d (-1) (c.next (-1))) = 0
  rw [outgoing_zero, Functor.map_zero]

private lemma image_zero_projective {M N : ModuleCat.{2} ℤᵐᵒᵖ} :
    Projective (Abelian.image (0 : M ⟶ N)) := by
  let e := Abelian.imageIsoImage (0 : M ⟶ N) ≪≫ ModuleCat.imageIsoRange (0 : M ⟶ N)
  have hz : IsZero (ModuleCat.of ℤᵐᵒᵖ (0 : M ⟶ N).hom.range) := by
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact ModuleCat.isZero_iff_subsingleton.2 inferInstance
  exact Projective.of_iso e.symm hz.projective

private instance outgoing_image_exact :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj
      (Abelian.image (P2.d (-1) (c.next (-1))))).PreservesHomology := by
  letI : Projective (Abelian.image (P2.d (-1) (c.next (-1)))) := by
    rw [outgoing_lifted_zero]
    exact image_zero_projective
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ _

private abbrev G : ModuleCat.{2} ℤᵐᵒᵖ ⥤ ModuleCat.{2} ℤ ⥤ AddCommGrpCat.{2} :=
  ModuleCat.BalancedTensor.groupBifunctor ℤ

private instance partial_additive (N : ModuleCat.{2} ℤ) : (G.flip.obj N).Additive :=
  Functor.LeftDerivedBalance.flippedObjAdditive G N

private abbrev f : Z2 ⟶ Z2 := P2.d 0 (-1)

private lemma f_apply (x : Z2) : f.hom x = ULift.up (2 * x.down) := by
  change ULift.up ((P.d 0 (-1)).hom x.down) = _
  rw [differential_value]

private instance f_mono : Mono f := by
  change Mono ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d 0 (-1)))
  have hd : P.d 0 (-1) = twice := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1) = twice
    simpa only [ChainComplex.of_d] using (show d (-1) = twice from rfl)
  rw [hd]
  infer_instance

private abbrev B : ModuleCat.{2} ℤᵐᵒᵖ := Abelian.image f

private def imageIso : Z2 ≅ B := asIso (Abelian.factorThruImage f)

private def oneZ : Z2 := ULift.up (1 : ℤ)

private def imageOne : B := (Abelian.factorThruImage f).hom oneZ

private lemma imageOne_normalized : imageIso.inv.hom imageOne = oneZ :=
  ConcreteCategory.congr_hom imageIso.hom_inv_id oneZ

private def cyclesIso : P2.cycles (-1) ≅ Z2 :=
  P2.iCyclesIso (-1) (c.next (-1)) rfl outgoing_lifted_zero

private abbrev β : B ⟶ P2.cycles (-1) :=
  HomologicalComplex.boundaryCyclesMap P2 0 (-1)

private lemma β_value : cyclesIso.hom.hom (β.hom imageOne) = ULift.up (2 : ℤ) := by
  have h₁ := ConcreteCategory.congr_hom
    (HomologicalComplex.boundaryCyclesMap_i P2 0 (-1)) imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) oneZ
  change (P2.iCycles (-1)).hom (β.hom imageOne) = ULift.up (2 : ℤ)
  exact h₁.trans (h₂.trans (by simpa only [oneZ, mul_one] using f_apply oneZ))

private def regularTensorIso (N : ModuleCat.{2} ℤ) :
    (G.obj Z2).obj N ≅ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N :=
  (G.flip.obj N).mapIso regularIso2.symm ≪≫
    ModuleCat.RegularElement.regularTensorIso.{0, 2} ℤ N

private lemma regularTensorIso_mk (N : ModuleCat.{2} ℤ) (x : Z2) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
    (regularTensorIso N).hom.hom (TensorProduct.Balanced.mk ℤ ℤ Z2 N x n) =
      x.down • n := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  change (ModuleCat.RegularElement.regularTensorIso.{0, 2} ℤ N).hom.hom
    (((G.map regularIso2.inv).app N).hom (TensorProduct.Balanced.mk ℤ ℤ Z2 N x n)) = x.down • n
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.RegularElement.regularTensorIso_mk]
  rfl

private abbrev A := P2.homology (-1)
private abbrev L : ModuleCat.{2} ℤ ⥤ AddCommGrpCat.{2} := (G.leftDerivedBifunctor 1).obj A

private abbrev tensorInclusion (N : ModuleCat.{2} ℤ) :
    (G.obj B).obj N ⟶ (G.obj (P2.cycles (-1))).obj N :=
  (G.map β).app N

private def pointComparison (N : ModuleCat.{2} ℤ) : L.obj N ≅ kernel (tensorInclusion N) :=
  torBoundaryKernelIso ℤ P2 N 0 (-1) incoming

private def pointPure (N : ModuleCat.{2} ℤ) (n : N) : (G.obj B).obj N :=
  ModuleCat.BalancedTensor.groupPure ℤ B N imageOne n

private lemma pointPure_kernel (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    (tensorInclusion N).hom (pointPure N n) = 0 := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  let e : (G.obj (P2.cycles (-1))).obj N ⟶
      (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N :=
    (G.map cyclesIso.hom).app N ≫ (regularTensorIso N).hom
  letI : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change (regularTensorIso N).hom.hom
    (((G.map cyclesIso.hom).app N).hom
      (((G.map β).app N).hom (TensorProduct.Balanced.mk ℤ ℤ B N imageOne n))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, β_value, regularTensorIso_mk]
  exact hn

private abbrev I : AddCommGrpCat.{2} := AddCommGrpCat.of Z2

private def pointMap (N : ModuleCat.{2} ℤ) (n : N) : I ⟶ (G.obj B).obj N :=
  AddCommGrpCat.ofHom ((zmultiplesHom _ (pointPure N n)).comp
    (ULift.moduleEquiv : Z2 ≃ₗ[ℤ] ℤ).toAddEquiv.toAddMonoidHom)

private lemma pointMap_apply (N : ModuleCat.{2} ℤ) (n : N) (x : I) :
    (pointMap N n).hom x = x.down • pointPure N n := rfl

private lemma pointMap_zero (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    pointMap N n ≫ tensorInclusion N = 0 := by
  apply AddCommGrpCat.ext
  intro x
  change (tensorInclusion N).hom ((pointMap N n).hom x) = 0
  rw [pointMap_apply, map_zsmul, pointPure_kernel N n hn, smul_zero]

private def pointKernel (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    kernel (tensorInclusion N) :=
  (kernel.lift (tensorInclusion N) (pointMap N n) (pointMap_zero N n hn)).hom oneZ

private def torClass (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) : L.obj N :=
  (pointComparison N).inv.hom (pointKernel N n hn)

private lemma torClass_boundary (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    (torBoundary ℤ P2 N 0 (-1) incoming).hom (torClass N n hn) = pointPure N n := by
  have h₁ := ConcreteCategory.congr_hom
    (torBoundaryKernelIso_inv_boundary ℤ P2 N 0 (-1) incoming) (pointKernel N n hn)
  have h₂ := ConcreteCategory.congr_hom
    (kernel.lift_ι (tensorInclusion N) (pointMap N n) (pointMap_zero N n hn)) oneZ
  change (torBoundary ℤ P2 N 0 (-1) incoming).hom (torClass N n hn) =
    (kernel.ι (tensorInclusion N)).hom (pointKernel N n hn) at h₁
  change (kernel.ι (tensorInclusion N)).hom (pointKernel N n hn) =
    (pointMap N n).hom oneZ at h₂
  exact h₁.trans (h₂.trans (by
    rw [pointMap_apply]
    change (1 : ℤ) • pointPure N n = pointPure N n
    exact one_zsmul _))

private def pointDetector (N : ModuleCat.{2} ℤ) :
    L.obj N ⟶ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N :=
  torBoundary ℤ P2 N 0 (-1) incoming ≫
    (G.map imageIso.inv).app N ≫ (regularTensorIso N).hom

private lemma pointDetector_class (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    (pointDetector N).hom (torClass N n hn) = n := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  change (regularTensorIso N).hom.hom
    (((G.map imageIso.inv).app N).hom
      ((torBoundary ℤ P2 N 0 (-1) incoming).hom (torClass N n hn))) = n
  rw [torClass_boundary, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    regularTensorIso_mk, imageOne_normalized]
  change (1 : ℤ) • n = n
  exact one_smul _

private instance pointDetector_mono (N : ModuleCat.{2} ℤ) : Mono (pointDetector N) := by
  change Mono (torBoundary ℤ P2 N 0 (-1) incoming ≫
    (G.map imageIso.inv).app N ≫ (regularTensorIso N).hom)
  rw [← torBoundaryKernelIso_hom_ι ℤ P2 N 0 (-1) incoming]
  infer_instance

private lemma torClass_two (N : ModuleCat.{2} ℤ) (n : N) (hn : (2 : ℤ) • n = 0) :
    (2 : ℤ) • torClass N n hn = 0 := by
  apply (AddCommGrpCat.mono_iff_injective (pointDetector N)).1 inferInstance
  rw [map_zsmul, pointDetector_class, hn, map_zero]

private lemma boundary_coeff_naturality {N N' : ModuleCat.{2} ℤ} (g : N ⟶ N') :
    L.map g ≫ torBoundary ℤ P2 N' 0 (-1) incoming =
      torBoundary ℤ P2 N 0 (-1) incoming ≫ (G.obj B).map g := by
  let F := G.flip.obj N
  let F' := G.flip.obj N'
  let α : F ⟶ F' := G.flip.map g
  let S := HomologicalComplex.boundariesCyclesHomologySequence P2 0 (-1)
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P2 0 (-1) incoming
  have hδ := LeftDerivedDelta.LDdelta_natural_functor α 0 S hS
  have hzero :
      (NatTrans.leftDerived α 0).app S.X₁ ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom =
        (F.leftDerivedZeroIsoSelf.app S.X₁).hom ≫ α.app S.X₁ := by
    simpa only [NatTrans.comp_app, NatIso.app_hom] using congrArg
      (fun τ => τ.app S.X₁) (NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor α)
  change (NatTrans.leftDerived α 1).app S.X₃ ≫
      (LeftDerivedDelta.LDdelta F' 0 S hS ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) =
    (LeftDerivedDelta.LDdelta F 0 S hS ≫ (F.leftDerivedZeroIsoSelf.app S.X₁).hom) ≫
      α.app S.X₁
  calc
    _ = ((NatTrans.leftDerived α 1).app S.X₃ ≫
        LeftDerivedDelta.LDdelta F' 0 S hS) ≫
        (F'.leftDerivedZeroIsoSelf.app S.X₁).hom := (Category.assoc _ _ _).symm
    _ = (LeftDerivedDelta.LDdelta F 0 S hS ≫
        (NatTrans.leftDerived α 0).app S.X₁) ≫
        (F'.leftDerivedZeroIsoSelf.app S.X₁).hom :=
      congrArg (fun q => q ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) hδ
    _ = LeftDerivedDelta.LDdelta F 0 S hS ≫
        ((NatTrans.leftDerived α 0).app S.X₁ ≫
          (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) := Category.assoc _ _ _
    _ = LeftDerivedDelta.LDdelta F 0 S hS ≫
        ((F.leftDerivedZeroIsoSelf.app S.X₁).hom ≫ α.app S.X₁) :=
      congrArg (fun q => LeftDerivedDelta.LDdelta F 0 S hS ≫ q) hzero
    _ = _ := (Category.assoc _ _ _).symm

private lemma pointDetector_mapped {N N' : ModuleCat.{2} ℤ}
    (g : N ⟶ N') (n : N) (hn : (2 : ℤ) • n = 0) :
    (pointDetector N').hom ((L.map g).hom (torClass N n hn)) = g.hom n := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  letI : Module ℤ N' := Module.compHom N' (algebraMap ℤ ℤ)
  have h := ConcreteCategory.congr_hom (boundary_coeff_naturality g) (torClass N n hn)
  change (torBoundary ℤ P2 N' 0 (-1) incoming).hom ((L.map g).hom (torClass N n hn)) =
    ((G.obj B).map g).hom
      ((torBoundary ℤ P2 N 0 (-1) incoming).hom (torClass N n hn)) at h
  change (regularTensorIso N').hom.hom
    (((G.map imageIso.inv).app N').hom
      ((torBoundary ℤ P2 N' 0 (-1) incoming).hom ((L.map g).hom (torClass N n hn)))) =
        g.hom n
  rw [h, torClass_boundary, ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk, imageOne_normalized]
  change (1 : ℤ) • g.hom n = g.hom n
  exact one_smul _

private abbrev N40 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)
private abbrev N60 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 6)
private abbrev N20 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev N41 : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N40
private abbrev N61 : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N60
private abbrev N21 : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N20
private abbrev N42 : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N41
private abbrev N62 : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N61
private abbrev N22 : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N21
private abbrev I2 := (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N22

private def reduction40 : N40 ⟶ N20 :=
  ModuleCat.ofHom
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toIntLinearMap

private def reduction60 : N60 ⟶ N20 :=
  ModuleCat.ofHom
    (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)).toAddMonoidHom.toIntLinearMap

private def reduction4 : N42 ⟶ N22 :=
  (ModuleCat.uliftFunctor.{2, 1} ℤ).map
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).map reduction40)

private def reduction6 : N62 ⟶ N22 :=
  (ModuleCat.uliftFunctor.{2, 1} ℤ).map
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).map reduction60)

private def n4 : N42 := ULift.up (ULift.up (2 : ZMod 4))
private def n6 : N62 := ULift.up (ULift.up (3 : ZMod 6))
private def n2 : N22 := ULift.up (ULift.up (1 : ZMod 2))

private lemma n4_two : (2 : ℤ) • n4 = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • (2 : ZMod 4) = 0
  norm_num [zsmul_eq_mul]

private lemma n6_two : (2 : ℤ) • n6 = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • (3 : ZMod 6) = 0
  norm_num [zsmul_eq_mul]

private lemma n2_two : (2 : ℤ) • n2 = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • (1 : ZMod 2) = 0
  norm_num [zsmul_eq_mul]

private lemma reduction4_value : reduction4.hom n4 = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (2 : ZMod 4) = 0
  norm_num

private lemma reduction6_value : reduction6.hom n6 = n2 := by
  apply ULift.ext
  apply ULift.ext
  change (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) (3 : ZMod 6) = 1
  norm_num

private abbrev τ4 : L.obj N42 := torClass N42 n4 n4_two
private abbrev τ6 : L.obj N62 := torClass N62 n6 n6_two
private abbrev τ2 : L.obj N22 := torClass N22 n2 n2_two

private lemma reduction4_tor_zero : (L.map reduction4).hom τ4 = 0 := by
  apply (AddCommGrpCat.mono_iff_injective (pointDetector N22)).1 inferInstance
  change (pointDetector N22).hom ((L.map reduction4).hom (torClass N42 n4 n4_two)) =
    (pointDetector N22).hom 0
  rw [pointDetector_mapped, reduction4_value, map_zero]

private lemma reduction6_tor_class : (L.map reduction6).hom τ6 = τ2 := by
  apply (AddCommGrpCat.mono_iff_injective (pointDetector N22)).1 inferInstance
  change (pointDetector N22).hom ((L.map reduction6).hom (torClass N62 n6 n6_two)) =
    (pointDetector N22).hom (torClass N22 n2 n2_two)
  rw [pointDetector_mapped, pointDetector_class, reduction6_value]

private lemma n2_ne_zero : n2 ≠ 0 := by
  intro h
  have hv := congrArg (fun n : N22 => n.down.down) h
  exact (by decide : (1 : ZMod 2) ≠ 0) hv

private lemma τ4_ne_zero : τ4 ≠ 0 := by
  intro h
  have hv := pointDetector_class N42 n4 n4_two
  rw [show torClass N42 n4 n4_two = 0 from h, map_zero] at hv
  have hzero := congrArg (fun n : N42 => n.down.down) hv
  exact (by decide : (0 : ZMod 4) ≠ 2) hzero

private lemma τ6_ne_zero : τ6 ≠ 0 := by
  intro h
  have hv := pointDetector_class N62 n6 n6_two
  rw [show torClass N62 n6 n6_two = 0 from h, map_zero] at hv
  have hzero := congrArg (fun n : N62 => n.down.down) hv
  exact (by decide : (0 : ZMod 6) ≠ 3) hzero

private lemma nonflat4 : ¬ Module.Flat ℤ (ZMod 4) := by
  intro h
  letI : Module.Flat ℤ (ZMod 4) := h
  have hinj : Function.Injective (algebraMap ℤ (ZMod 4)) :=
    FaithfulSMul.algebraMap_injective ℤ (ZMod 4)
  have hz : algebraMap ℤ (ZMod 4) (4 : ℤ) = algebraMap ℤ (ZMod 4) 0 := by norm_num
  have hbad : (4 : ℤ) = 0 := hinj hz
  norm_num at hbad

private lemma nonflat6 : ¬ Module.Flat ℤ (ZMod 6) := by
  intro h
  letI : Module.Flat ℤ (ZMod 6) := h
  have hinj : Function.Injective (algebraMap ℤ (ZMod 6)) :=
    FaithfulSMul.algebraMap_injective ℤ (ZMod 6)
  have hz : algebraMap ℤ (ZMod 6) (6 : ℤ) = algebraMap ℤ (ZMod 6) 0 := by norm_num
  have hbad : (6 : ℤ) = 0 := hinj hz
  norm_num at hbad

private abbrev J := Discrete WalkingPair

private def coefficientFamily : WalkingPair → ModuleCat.{2} ℤ
  | .left => N42
  | .right => N62

private def coefficientMapFamily (i : WalkingPair) : coefficientFamily i ⟶ N22 :=
  match i with
  | .left => reduction4
  | .right => reduction6

private def K : J ⥤ ModuleCat.{2} ℤ := Discrete.functor coefficientFamily
private def K' : J ⥤ ModuleCat.{2} ℤ := Discrete.functor (fun _ => N22)

private def coefficientDiagramMap : K ⟶ K' :=
  Discrete.natTrans (fun j => coefficientMapFamily j.as)

private instance colimit_homology :
    (colim (J := J) (C := AddCommGrpCat.{2})).PreservesHomology := by
  letI : HasExactColimitsOfShape J AddCommGrpCat.{2} := inferInstance
  infer_instance

private instance coefficient_colimits (X : ModuleCat.{2} ℤᵐᵒᵖ) :
    PreservesColimitsOfShape J (G.obj X) := by infer_instance

private def comparisonK : L.obj (colimit K) ≅ colimit (K ⋙ L) :=
  G.leftDerivedBifunctorCoefficientColimitIso J A 1 K

private def comparisonK' : L.obj (colimit K') ≅ colimit (K' ⋙ L) :=
  G.leftDerivedBifunctorCoefficientColimitIso J A 1 K'

private def y : colimit (K ⋙ L) :=
  (colimit.ι (K ⋙ L) ⟨WalkingPair.left⟩).hom τ4 +
    (colimit.ι (K ⋙ L) ⟨WalkingPair.right⟩).hom τ6

private def wholeClass : L.obj (colimit K) := comparisonK.inv.hom y

private def diagramTorMap : K ⋙ L ⟶ K' ⋙ L :=
  Functor.whiskerRight coefficientDiagramMap L

private lemma diagramTorMap_y :
    (colimMap diagramTorMap).hom y =
      (colimit.ι (K' ⋙ L) ⟨WalkingPair.right⟩).hom τ2 := by
  have hleft := ConcreteCategory.congr_hom
    (ι_colimMap diagramTorMap ⟨WalkingPair.left⟩) τ4
  have hright := ConcreteCategory.congr_hom
    (ι_colimMap diagramTorMap ⟨WalkingPair.right⟩) τ6
  change (colimMap diagramTorMap).hom
      ((colimit.ι (K ⋙ L) ⟨WalkingPair.left⟩).hom τ4) =
    (colimit.ι (K' ⋙ L) ⟨WalkingPair.left⟩).hom ((L.map reduction4).hom τ4) at hleft
  change (colimMap diagramTorMap).hom
      ((colimit.ι (K ⋙ L) ⟨WalkingPair.right⟩).hom τ6) =
    (colimit.ι (K' ⋙ L) ⟨WalkingPair.right⟩).hom ((L.map reduction6).hom τ6) at hright
  rw [reduction4_tor_zero, map_zero] at hleft
  rw [reduction6_tor_class] at hright
  change (colimMap diagramTorMap).hom
    ((colimit.ι (K ⋙ L) ⟨WalkingPair.left⟩).hom τ4 +
      (colimit.ι (K ⋙ L) ⟨WalkingPair.right⟩).hom τ6) = _
  rw [map_add, hleft, hright, zero_add]

private def leftPath : colimit (K' ⋙ L) :=
  comparisonK'.hom.hom ((L.map (colimMap coefficientDiagramMap)).hom wholeClass)

private def rightPath : colimit (K' ⋙ L) :=
  (colimMap diagramTorMap).hom (comparisonK.hom.hom wholeClass)

private lemma naturality_paths : leftPath = rightPath :=
  ConcreteCategory.congr_hom
    (G.leftDerivedBifunctorCoefficientColimitIso_hom_naturality J A 1 coefficientDiagramMap)
    wholeClass

private lemma rightPath_value :
    rightPath = (colimit.ι (K' ⋙ L) ⟨WalkingPair.right⟩).hom τ2 := by
  have h := ConcreteCategory.congr_hom comparisonK.inv_hom_id y
  change comparisonK.hom.hom wholeClass = y at h
  change (colimMap diagramTorMap).hom (comparisonK.hom.hom wholeClass) = _
  rw [h]
  exact diagramTorMap_y

private def leftCoordinate : colimit (K' ⋙ L) ⟶ I2 :=
  colimit.desc (K' ⋙ L)
    { pt := I2
      ι := Discrete.natTrans fun j =>
        match j.as with
        | .left => pointDetector N22
        | .right => 0 }

private def rightCoordinate : colimit (K' ⋙ L) ⟶ I2 :=
  colimit.desc (K' ⋙ L)
    { pt := I2
      ι := Discrete.natTrans fun j =>
        match j.as with
        | .left => 0
        | .right => pointDetector N22 }

private lemma leftCoordinate_right :
    colimit.ι (K' ⋙ L) ⟨WalkingPair.right⟩ ≫ leftCoordinate = 0 :=
  colimit.ι_desc _ _ _

private lemma rightCoordinate_right :
    colimit.ι (K' ⋙ L) ⟨WalkingPair.right⟩ ≫ rightCoordinate = pointDetector N22 :=
  colimit.ι_desc _ _ _

private def coordinates (x : colimit (K' ⋙ L)) : N22 × N22 :=
  (leftCoordinate.hom x, rightCoordinate.hom x)

private lemma rightPath_coordinates : coordinates rightPath = (0, n2) := by
  rw [rightPath_value]
  apply Prod.ext
  · exact ConcreteCategory.congr_hom leftCoordinate_right τ2
  · exact (ConcreteCategory.congr_hom rightCoordinate_right τ2).trans
      (pointDetector_class N22 n2 n2_two)

private lemma leftPath_coordinates : coordinates leftPath = (0, n2) := by
  rw [naturality_paths]
  exact rightPath_coordinates

example : ¬ Module.Flat ℤ (ZMod 4) ∧ ¬ Module.Flat ℤ (ZMod 6) :=
  ⟨nonflat4, nonflat6⟩

example : τ4 ≠ 0 ∧ τ6 ≠ 0 := ⟨τ4_ne_zero, τ6_ne_zero⟩

example : (2 : ℤ) • τ4 = 0 ∧ (2 : ℤ) • τ6 = 0 :=
  ⟨torClass_two N42 n4 n4_two, torClass_two N62 n6 n6_two⟩

example : (L.map reduction4).hom τ4 = 0 ∧ (L.map reduction6).hom τ6 = τ2 :=
  ⟨reduction4_tor_zero, reduction6_tor_class⟩

example : coordinates leftPath = (0, ULift.up (ULift.up (1 : ZMod 2))) :=
  leftPath_coordinates

example : coordinates rightPath = (0, ULift.up (ULift.up (1 : ZMod 2))) :=
  rightPath_coordinates

example : wholeClass ≠ 0 ∧ leftPath ≠ 0 ∧ rightPath ≠ 0 := by
  have hright : rightPath ≠ 0 := by
    intro h
    have hc := rightPath_coordinates
    rw [h] at hc
    have hv := congrArg Prod.snd hc
    change rightCoordinate.hom 0 = n2 at hv
    rw [map_zero] at hv
    exact n2_ne_zero hv.symm
  have hleft : leftPath ≠ 0 := by rw [naturality_paths]; exact hright
  refine ⟨?_, hleft, hright⟩
  intro h
  apply hleft
  change comparisonK'.hom.hom ((L.map (colimMap coefficientDiagramMap)).hom wholeClass) = 0
  rw [h, map_zero, map_zero]

end MathlibExtTest.DerivedCoefficientColimit
