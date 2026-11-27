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

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.HomologyCokernel
import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorAntidiagonalKernel
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.SingleHomology
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A nonzero tensor cokernel with nonflat integer coefficients

The right integer complex P has regular ℤ in every integer degree,
multiplication by two from degree zero to degree minus one, and zero
differentials elsewhere. Take the left coefficient N=ℤ/2, which is not
flat over ℤ.

At degree minus one, the boundary inclusion is 2ℤ → ℤ. Its tensor with N
is zero, so its cokernel and homology₋₁(P) ⊗ℤ N both identify with ℤ/2.
The canonical comparison sends the cokernel class of 1 ⊗ 1 to the tensor
of the homology class of one with one. Both classes are nonzero and
have detected value one.

Coefficient naturality is exercised by the diagonal N → N×N and a
coordinate projection. The common-height comparison is also used with
a coefficient lifted to universe one.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace MathlibExtTest.BalancedTensorHomologyCokernel

private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ
private abbrev N : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev I := (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj N
local notation "c" => ComplexShape.down ℤ

private def twice : Z ⟶ Z := ModuleCat.ofHom
  { toFun := fun a => 2 * a
    map_add' := fun a b => by change 2 * (a + b) = _; ring
    map_smul' := fun r a => by
      change 2 * (a * r.unop) = (2 * a) * r.unop
      ring }

private def d (i : ℤ) : Z ⟶ Z := if i = -1 then twice else 0

private lemma d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases h : i = -1
  · subst i
    simp [d]
  · simp [d, h]

private def P : ChainComplex (ModuleCat.{0} ℤᵐᵒᵖ) ℤ :=
  ChainComplex.of (fun _ : ℤ => Z) d d_sq

private lemma differential_value (a : ℤ) : (P.d 0 (-1)).hom a = 2 * a := by
  change (ChainComplex.of.d (fun _ : ℤ => Z) d ((-1 : ℤ) + 1) (-1)).hom a = _
  simpa only [ChainComplex.of_d] using (show (d (-1)).hom a = 2 * a from rfl)

private lemma next_int (i : ℤ) : c.next i = i - 1 :=
  c.next_eq' (by change i - 1 + 1 = i; exact sub_add_cancel i 1)

private lemma incoming : c.prev (-1) = 0 :=
  c.prev_eq' (by change (-1 : ℤ) + 1 = 0; norm_num)

private lemma outgoing_zero : P.d (-1) (c.next (-1)) = 0 := by
  have h : P.d (-1) (-2) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((-2 : ℤ) + 1) (-2) = 0
    simpa only [ChainComplex.of_d] using (show d (-2) = 0 from rfl)
  exact (congrArg (fun j : ℤ => (show Z ⟶ Z from P.d (-1) j)) (next_int (-1))).trans h

private abbrev F := (ModuleCat.BalancedTensor.groupBifunctor ℤ).flip.obj N
private abbrev β := HomologicalComplex.boundaryCyclesMap P 0 (-1)
private abbrev f := P.d 0 (-1)

private def cyclesIso : P.cycles (-1) ≅ Z :=
  P.iCyclesIso (-1) (c.next (-1)) rfl outgoing_zero

private lemma cyclesIso_hom : cyclesIso.hom = P.iCycles (-1) := rfl

private def regularTensorIso : F.obj Z ≅ I := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  exact (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso
    (TensorProduct.Balanced.leftUnitor ℤ ℤ N).toModuleIso

private lemma regularTensorIso_mk (a : ℤ) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
    regularTensorIso.hom.hom (TensorProduct.Balanced.mk ℤ ℤ ℤ N a n) = a • n :=
  TensorProduct.Balanced.leftUnitor_mk ℤ ℤ N a n

private def cycleTensorIso : F.obj (P.cycles (-1)) ≅ I :=
  F.mapIso cyclesIso ≪≫ regularTensorIso

private lemma cycleTensorIso_hom :
    cycleTensorIso.hom = F.map (P.iCycles (-1)) ≫ regularTensorIso.hom := rfl

private lemma cycleTensorIso_mk (z : P.cycles (-1)) (n : N) :
    cycleTensorIso.hom.hom (ModuleCat.BalancedTensor.groupPure ℤ (P.cycles (-1)) N z n) =
      cyclesIso.hom.hom z • n := by
  change regularTensorIso.hom.hom ((F.map cyclesIso.hom).hom
    (ModuleCat.BalancedTensor.groupPure ℤ (P.cycles (-1)) N z n)) = _
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk]
  exact regularTensorIso_mk (cyclesIso.hom.hom z) n

private def oneCycle : P.cycles (-1) := cyclesIso.inv.hom (1 : ℤ)

private lemma oneCycle_value : cyclesIso.hom.hom oneCycle = 1 :=
  ConcreteCategory.congr_hom cyclesIso.inv_hom_id (1 : ℤ)

private def imageOne : Abelian.image f := (Abelian.factorThruImage f).hom (1 : ℤ)

private lemma boundary_value : cyclesIso.hom.hom (β.hom imageOne) = 2 := by
  have h₁ := ConcreteCategory.congr_hom
    (HomologicalComplex.boundaryCyclesMap_i P 0 (-1)) imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac f) (1 : ℤ)
  change (P.iCycles (-1)).hom (β.hom imageOne) = 2
  exact h₁.trans (h₂.trans (by simpa only [mul_one] using differential_value 1))

private lemma tensorDifferential_zero : F.map f ≫ regularTensorIso.hom = 0 := by
  apply ModuleCat.BalancedTensor.groupHom_ext ℤ Z N I
  intro a n
  change regularTensorIso.hom.hom ((F.map f).hom (TensorProduct.Balanced.mk ℤ ℤ Z N a n)) = 0
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk, differential_value]
  change ((2 * a : ℤ) : ZMod 2) * n = 0
  norm_num

private lemma tensorBoundary_zero : F.map β = 0 := by
  apply (cancel_mono cycleTensorIso.hom).1
  let a := Abelian.factorThruImage f
  letI : Epi (F.map a) := inferInstance
  apply (cancel_epi (F.map a)).1
  have h : F.map a ≫ F.map β ≫ cycleTensorIso.hom = F.map f ≫ regularTensorIso.hom := by
    rw [cycleTensorIso_hom]
    calc
      _ = F.map (a ≫ β ≫ P.iCycles (-1)) ≫ regularTensorIso.hom := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by
        rw [HomologicalComplex.boundaryCyclesMap_i, Abelian.image.fac]
  simpa only [Category.assoc, zero_comp, comp_zero] using h.trans tensorDifferential_zero

private abbrev K := cokernel (F.map β)

private def cokernelZMod2Iso : K ≅ I :=
  cokernelIsoOfEq tensorBoundary_zero ≪≫ cokernelZeroIsoTarget ≪≫ cycleTensorIso

private lemma cokernelZMod2Iso_π : cokernel.π (F.map β) ≫ cokernelZMod2Iso.hom =
    cycleTensorIso.hom := by
  simp only [cokernelZMod2Iso, Iso.trans_hom]
  rw [π_comp_cokernelIsoOfEq_hom_assoc, cokernelZeroIsoTarget_hom,
    cokernel.π_desc_assoc, Category.id_comp]

private def comparison : K ≅ F.obj (P.homology (-1)) :=
  homologyTensorCokernelIso ℤ P N 0 (-1) incoming

private def homologyTensorZMod2Iso : F.obj (P.homology (-1)) ≅ I :=
  comparison.symm ≪≫ cokernelZMod2Iso

private def sourceOne : K := (cokernel.π (F.map β)).hom
  (ModuleCat.BalancedTensor.groupPure ℤ (P.cycles (-1)) N oneCycle (1 : N))

private def targetOne : F.obj (P.homology (-1)) :=
  ModuleCat.BalancedTensor.groupPure ℤ (P.homology (-1)) N
    ((P.homologyπ (-1)).hom oneCycle) (1 : N)

private lemma sourceOne_value : cokernelZMod2Iso.hom.hom sourceOne = 1 := by
  have h := ConcreteCategory.congr_hom cokernelZMod2Iso_π
    (ModuleCat.BalancedTensor.groupPure ℤ (P.cycles (-1)) N oneCycle (1 : N))
  change cokernelZMod2Iso.hom.hom sourceOne = _ at h
  rw [cycleTensorIso_mk, oneCycle_value, one_smul] at h
  exact h

private lemma comparison_sourceOne : comparison.hom.hom sourceOne = targetOne :=
  homologyTensorCokernelIso_mk ℤ P N 0 (-1) incoming oneCycle (1 : N)

private lemma targetOne_value : homologyTensorZMod2Iso.hom.hom targetOne = 1 := by
  rw [← comparison_sourceOne]
  change cokernelZMod2Iso.hom.hom
    (comparison.inv.hom (comparison.hom.hom sourceOne)) = 1
  have h : comparison.inv.hom (comparison.hom.hom sourceOne) = sourceOne :=
    ConcreteCategory.congr_hom comparison.hom_inv_id sourceOne
  rw [h]
  exact sourceOne_value

example : (P.d 0 (-1)).hom (1 : ℤ) = 2 := by simpa using differential_value 1

example : cyclesIso.hom.hom (β.hom imageOne) = 2 := boundary_value

example : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  letI : Module.Flat ℤ (ZMod 2) := h
  have hinj : Function.Injective (algebraMap ℤ (ZMod 2)) :=
    FaithfulSMul.algebraMap_injective ℤ (ZMod 2)
  have hzero : algebraMap ℤ (ZMod 2) (2 : ℤ) = algebraMap ℤ (ZMod 2) 0 := by norm_num
  have hbad : (2 : ℤ) = 0 := hinj hzero
  norm_num at hbad

example : F.map β = 0 := tensorBoundary_zero

example : cokernelZMod2Iso.hom.hom sourceOne = 1 := sourceOne_value

example : sourceOne ≠ 0 := by
  intro h
  have hv := congrArg cokernelZMod2Iso.hom.hom h
  rw [sourceOne_value, map_zero] at hv
  exact (by decide : (1 : ZMod 2) ≠ 0) hv

example : comparison.hom.hom sourceOne = targetOne := comparison_sourceOne

example : homologyTensorZMod2Iso.hom.hom targetOne = 1 := targetOne_value

example : targetOne ≠ 0 := by
  intro h
  have hv := congrArg homologyTensorZMod2Iso.hom.hom h
  rw [targetOne_value, map_zero] at hv
  exact (by decide : (1 : ZMod 2) ≠ 0) hv

example : Nonempty (F.obj (P.homology (-1)) ≅ I) := ⟨homologyTensorZMod2Iso⟩

private abbrev N₂ : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2 × ZMod 2)

private def diagonal : N ⟶ N₂ := ModuleCat.ofHom
  ((LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2).prod LinearMap.id)

private def first : N₂ ⟶ N := ModuleCat.ofHom (LinearMap.fst ℤ (ZMod 2) (ZMod 2))

example :
    (((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P.homology (-1))).map first ≫
      homologyTensorZMod2Iso.hom).hom
      ((homologyTensorCokernelIso ℤ P N₂ 0 (-1) incoming).hom.hom
        ((homologyTensorCokernelCoeffMap ℤ P diagonal 0 (-1)).hom sourceOne)) = 1 := by
  let G := (ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (P.homology (-1))
  have h := ConcreteCategory.congr_hom
    (homologyTensorCokernelIso_coeff_naturality ℤ P diagonal 0 (-1) incoming) sourceOne
  change (G.map diagonal).hom (comparison.hom.hom sourceOne) =
    (homologyTensorCokernelIso ℤ P N₂ 0 (-1) incoming).hom.hom
      ((homologyTensorCokernelCoeffMap ℤ P diagonal 0 (-1)).hom sourceOne) at h
  rw [← h]
  have hp : G.map diagonal ≫ G.map first = 𝟙 (G.obj N) := by
    rw [← G.map_comp]
    have hd : diagonal ≫ first = 𝟙 N := by
      apply ModuleCat.hom_ext
      rfl
    rw [hd, G.map_id]
  have hv := ConcreteCategory.congr_hom hp (comparison.hom.hom sourceOne)
  change homologyTensorZMod2Iso.hom.hom
    ((G.map first).hom ((G.map diagonal).hom (comparison.hom.hom sourceOne))) = 1
  change (G.map first).hom ((G.map diagonal).hom (comparison.hom.hom sourceOne)) =
    comparison.hom.hom sourceOne at hv
  rw [hv, comparison_sourceOne]
  exact targetOne_value

example :
    let N₁ : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N
    let PL : HomologicalComplex (ModuleCat.{2} ℤᵐᵒᵖ) c :=
      ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).mapHomologicalComplex c).obj P
    let NL : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N₁
    Nonempty
      (cokernel (((ModuleCat.BalancedTensor.groupBifunctor ℤ).flip.obj NL).map
          (HomologicalComplex.boundaryCyclesMap PL 0 (-1))) ≅
        ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (PL.homology (-1))).obj NL) := by
  dsimp only
  exact ⟨homologyTensorCokernelIsoAt.{2} ℤ P ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj N)
    0 (-1) incoming⟩


/-!
## A whole integer antidiagonal with nonflat coefficients

The right complex P has regular integer terms in every degree and differential
multiplication by two from degree zero to degree minus one. Put the lifted
coefficient ℤ/2 in degree minus two of a single left complex. Lift the right
and left complexes from carrier universes zero and one to common height two.

The full antidiagonal p+q=−3 contains the pair (−1,−2), whose degree-one Tor
term has grading −2. All right terms and outgoing differential images are
projective. The comparison is therefore available with the nonflat left
homology coefficient. A point Tor class gives a nonzero class in the full
coproduct, and both the comparison and the connecting boundary have residue
one in its normalized boundary coordinate.
-/

namespace IntegerAntidiagonal

private abbrev ZL : ModuleCat.{2} ℤᵐᵒᵖ :=
  (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).obj Z

private abbrev N₁ : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N

private abbrev Q₁ : ChainComplex (ModuleCat.{1} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) c (-2)).obj N₁

private abbrev PL : ChainComplex (ModuleCat.{2} ℤᵐᵒᵖ) ℤ :=
  ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).mapHomologicalComplex c).obj P

private abbrev QL : ChainComplex (ModuleCat.{2} ℤ) ℤ :=
  ((ModuleCat.uliftFunctor.{2, 1} ℤ).mapHomologicalComplex c).obj Q₁

private abbrev N₂ : ModuleCat.{2} ℤ :=
  (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N₁

private abbrev I₂ : AddCommGrpCat.{2} :=
  (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N₂

private abbrev V : ModuleCat.{2} ℤ := QL.homology (-2)

private abbrev G := ModuleCat.BalancedTensor.groupBifunctor ℤ

private def rightRegularEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private instance integerProjective : Module.Projective ℤᵐᵒᵖ ℤ :=
  Module.Projective.of_equiv' rightRegularEquiv

private instance liftedModuleProjective : Module.Projective ℤᵐᵒᵖ ZL := by
  change Module.Projective ℤᵐᵒᵖ (ULift.{2} ℤ)
  infer_instance

private instance liftedProjective : Projective ZL :=
  ModuleCat.projective_of_categoryTheory_projective ZL

private lemma termProjective (p : ℤ) : Projective (PL.X p) := by
  change Projective ZL
  infer_instance

private abbrev fp : ZL ⟶ ZL := PL.d 0 (-1)

private lemma fp_apply (x : ZL) : fp.hom x = ULift.up (2 * x.down) := by
  change ULift.up ((P.d 0 (-1)).hom x.down) = _
  rw [differential_value]

private instance fp_mono : Mono fp := by
  apply (ModuleCat.mono_iff_injective fp).2
  intro x y h
  apply ULift.ext
  rw [fp_apply, fp_apply] at h
  have hv : 2 * x.down = 2 * y.down := congrArg ULift.down h
  exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)) hv

private lemma imageZeroProjective :
    Projective (Abelian.image (0 : ZL ⟶ ZL)) := by
  let a : ZL ⟶ Abelian.image (0 : ZL ⟶ ZL) :=
    Abelian.factorThruImage (0 : ZL ⟶ ZL)
  have hι : Abelian.image.ι (0 : ZL ⟶ ZL) = 0 := by
    apply (cancel_epi a).1
    exact (Abelian.image.fac (0 : ZL ⟶ ZL)).trans (comp_zero a).symm
  have hid : 𝟙 (Abelian.image (0 : ZL ⟶ ZL)) = 0 := by
    apply (cancel_mono (Abelian.image.ι (0 : ZL ⟶ ZL))).1
    simp only [hι, comp_zero]
  refine ⟨?_⟩
  intro E X g e _
  refine ⟨0, ?_⟩
  have hg : g = 0 := by
    calc
      g = (𝟙 _) ≫ g := (Category.id_comp g).symm
      _ = 0 := by rw [hid, zero_comp]
  simpa only [zero_comp] using hg.symm

private lemma outgoing_of_ne (p : ℤ) (hp : p ≠ 0) :
    PL.d p (c.next p) = 0 := by
  have hne : p - 1 ≠ (-1 : ℤ) := by
    intro h
    have h' : p = (-1 : ℤ) + 1 := (sub_eq_iff_eq_add).1 h
    norm_num at h'
    exact hp h'
  have hd : P.d ((p - 1) + 1) (p - 1) = 0 := by
    change ChainComplex.of.d (fun _ : ℤ => Z) d ((p - 1) + 1) (p - 1) = 0
    simp only [ChainComplex.of_d, d, if_neg hne]
  have hd' : P.d p (c.next p) = 0 := by
    rw [next_int]
    simpa only [sub_add_cancel] using hd
  change (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d p (c.next p)) = 0
  rw [hd', Functor.map_zero]

private lemma outgoingProjective (p : ℤ) :
    Projective (Abelian.image (PL.d p (c.next p))) := by
  by_cases hp : p = 0
  · subst p
    have hd : PL.d 0 (c.next 0) = fp := by
      rw [next_int]
      rfl
    rw [hd]
    exact Projective.of_iso (asIso (Abelian.factorThruImage fp))
      (inferInstance : Projective ZL)
  · rw [outgoing_of_ne p hp]
    exact imageZeroProjective

private lemma termExact (p : ℤ) :
    (G.obj (PL.X p)).PreservesHomology := by
  letI : Projective (PL.X p) := termProjective p
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective
    ℤ (PL.X p)

private lemma outgoingExact (p : ℤ) :
    (G.obj (Abelian.image (PL.d p (c.next p)))).PreservesHomology := by
  letI : Projective (Abelian.image (PL.d p (c.next p))) := outgoingProjective p
  exact ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective
    ℤ (Abelian.image (PL.d p (c.next p)))

private lemma QL_d_zero (i j : ℤ) : QL.d i j = 0 := by
  change (ModuleCat.uliftFunctor.{2, 1} ℤ).map (Q₁.d i j) = 0
  rw [HomologicalComplex.single_obj_d, Functor.map_zero]

private def coefficientIso : V ≅ N₂ :=
  (QL.isoHomologyπ (c.prev (-2)) (-2) rfl (QL_d_zero _ _)).symm ≪≫
    QL.iCyclesIso (-2) (c.next (-2)) rfl (QL_d_zero _ _) ≪≫
      (ModuleCat.uliftFunctor.{2, 1} ℤ).mapIso
        (HomologicalComplex.singleObjXSelf c (-2) N₁)

private def oneN : N₂ := ULift.up (ULift.up (1 : ZMod 2))

private def η : V := coefficientIso.inv.hom oneN

private lemma η_value : coefficientIso.hom.hom η = oneN :=
  ConcreteCategory.congr_hom coefficientIso.inv_hom_id oneN

private lemma coefficient_two (v : V) : (2 : ℤ) • v = 0 := by
  apply (ModuleCat.mono_iff_injective coefficientIso.hom).1 inferInstance
  rw [map_smul, map_zero]
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • (coefficientIso.hom.hom v).down.down = 0
  rw [zsmul_eq_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private lemma lifted_outgoing_zero : PL.d (-1) (c.next (-1)) = 0 := by
  change (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map
    (P.d (-1) (c.next (-1))) = 0
  rw [outgoing_zero, Functor.map_zero]

private def liftedCyclesIso : PL.cycles (-1) ≅ ZL :=
  PL.iCyclesIso (-1) (c.next (-1)) rfl lifted_outgoing_zero

private abbrev B : ModuleCat.{2} ℤᵐᵒᵖ := Abelian.image fp

private def imageIso : ZL ≅ B := asIso (Abelian.factorThruImage fp)

private def oneZ : ZL := ULift.up (1 : ℤ)

private def imageOne : B := (Abelian.factorThruImage fp).hom oneZ

private lemma imageOne_normalized : imageIso.inv.hom imageOne = oneZ :=
  ConcreteCategory.congr_hom imageIso.hom_inv_id oneZ

private abbrev β : B ⟶ PL.cycles (-1) :=
  HomologicalComplex.boundaryCyclesMap PL 0 (-1)

private lemma β_value : liftedCyclesIso.hom.hom (β.hom imageOne) = ULift.up (2 : ℤ) := by
  have h₁ := ConcreteCategory.congr_hom
    (HomologicalComplex.boundaryCyclesMap_i PL 0 (-1)) imageOne
  have h₂ := ConcreteCategory.congr_hom (Abelian.image.fac fp) oneZ
  change (PL.iCycles (-1)).hom (β.hom imageOne) = ULift.up (2 : ℤ)
  exact h₁.trans (h₂.trans (by simpa only [oneZ, mul_one] using fp_apply oneZ))

private def regularTensorIso (W : ModuleCat.{2} ℤ) :
    (G.obj ZL).obj W ≅ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj W := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  let e : TensorProduct.Balanced ℤ ℤ ZL W ≃ₗ[ℤ]
      TensorProduct.Balanced ℤ ℤ ℤ W :=
    TensorProduct.Balanced.congr (k := ℤ) (R := ℤ)
      (ULift.moduleEquiv : ZL ≃ₗ[ℤ] ℤ) (LinearEquiv.refl ℤ W)
      (by intro r x; rfl) (by intro r w; rfl)
  exact (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).mapIso
    (e.trans (TensorProduct.Balanced.leftUnitor ℤ ℤ W)).toModuleIso

private lemma regularTensorIso_mk (W : ModuleCat.{2} ℤ) (x : ZL) (w : W) :
    letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
    (regularTensorIso W).hom.hom
      (TensorProduct.Balanced.mk ℤ ℤ ZL W x w) = x.down • w := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  change (TensorProduct.Balanced.leftUnitor ℤ ℤ W)
    ((TensorProduct.Balanced.congr (k := ℤ) (R := ℤ)
      (ULift.moduleEquiv : ZL ≃ₗ[ℤ] ℤ) (LinearEquiv.refl ℤ W)
      (by intro r z; rfl) (by intro r z; rfl))
        (TensorProduct.Balanced.mk ℤ ℤ ZL W x w)) = _
  rw [TensorProduct.Balanced.congr_mk, TensorProduct.Balanced.leftUnitor_mk]
  rfl

private abbrev T : AddCommGrpCat.{2} := (G.obj B).obj V

private abbrev tensorInclusion : T ⟶ (G.obj (PL.cycles (-1))).obj V :=
  (G.map β).app V

private def pointOne : T := ModuleCat.BalancedTensor.groupPure ℤ B V imageOne η

private def pointDetector : T ⟶ I₂ :=
  (G.map imageIso.inv).app V ≫ (regularTensorIso V).hom ≫
    (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).map coefficientIso.hom

private lemma pointOne_value : pointDetector.hom pointOne = oneN := by
  letI : Module ℤ V := Module.compHom V (algebraMap ℤ ℤ)
  change coefficientIso.hom.hom
    ((regularTensorIso V).hom.hom
      (((G.map imageIso.inv).app V).hom
        (TensorProduct.Balanced.mk ℤ ℤ B V imageOne η))) = _
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk,
    imageOne_normalized]
  change coefficientIso.hom.hom ((1 : ℤ) • η) = oneN
  rw [one_smul, η_value]

private lemma pointOne_kernel : tensorInclusion.hom pointOne = 0 := by
  letI : Module ℤ V := Module.compHom V (algebraMap ℤ ℤ)
  let e : (G.obj (PL.cycles (-1))).obj V ⟶
      (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj V :=
    (G.map liftedCyclesIso.hom).app V ≫ (regularTensorIso V).hom
  letI : Mono e := inferInstance
  apply (AddCommGrpCat.mono_iff_injective e).1 inferInstance
  change (regularTensorIso V).hom.hom
    (((G.map liftedCyclesIso.hom).app V).hom
      (((G.map β).app V).hom
        (TensorProduct.Balanced.mk ℤ ℤ B V imageOne η))) = e.hom 0
  rw [map_zero, ModuleCat.BalancedTensor.groupBifunctor_map_mk,
    ModuleCat.BalancedTensor.groupBifunctor_map_mk, β_value, regularTensorIso_mk]
  change (2 : ℤ) • η = 0
  exact coefficient_two η

private abbrev J : AddCommGrpCat.{2} := AddCommGrpCat.of ZL

private def pointMap : J ⟶ T :=
  AddCommGrpCat.ofHom ((zmultiplesHom pointOne).comp
    (ULift.moduleEquiv : ZL ≃ₗ[ℤ] ℤ).toAddEquiv.toAddMonoidHom)

private lemma pointMap_apply (x : J) : pointMap.hom x = x.down • pointOne := rfl

private lemma pointMap_zero : pointMap ≫ tensorInclusion = 0 := by
  apply AddCommGrpCat.hom_ext
  intro x
  change tensorInclusion.hom (pointMap.hom x) = 0
  rw [pointMap_apply, map_zsmul, pointOne_kernel, smul_zero]

private def pointKernelMap : J ⟶ kernel tensorInclusion :=
  kernel.lift tensorInclusion pointMap pointMap_zero

private def pointKernelOne : kernel tensorInclusion := pointKernelMap.hom oneZ

private lemma pointKernelOne_ι : (kernel.ι tensorInclusion).hom pointKernelOne = pointOne := by
  have h := ConcreteCategory.congr_hom
    (kernel.lift_ι tensorInclusion pointMap pointMap_zero) oneZ
  change (kernel.ι tensorInclusion).hom pointKernelOne = pointMap.hom oneZ at h
  exact h.trans (by rw [pointMap_apply]; change (1 : ℤ) • pointOne = pointOne; exact one_zsmul _)

private def pointComparison :
    ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology (-1))).obj V ≅
      kernel tensorInclusion := by
  letI : (G.obj (PL.X (-1))).PreservesHomology := termExact (-1)
  letI : (G.obj (Abelian.image (PL.d (-1) (c.next (-1))))).PreservesHomology :=
    outgoingExact (-1)
  exact torBoundaryKernelIso ℤ PL V 0 (-1) incoming

private def τ :
    ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology (-1))).obj V :=
  pointComparison.inv.hom pointKernelOne

private lemma τ_boundary : (torBoundary ℤ PL V 0 (-1) incoming).hom τ = pointOne := by
  letI : (G.obj (PL.X (-1))).PreservesHomology := termExact (-1)
  letI : (G.obj (Abelian.image (PL.d (-1) (c.next (-1))))).PreservesHomology :=
    outgoingExact (-1)
  have h := ConcreteCategory.congr_hom
    (torBoundaryKernelIso_inv_boundary ℤ PL V 0 (-1) incoming) pointKernelOne
  change (torBoundary ℤ PL V 0 (-1) incoming).hom τ =
    (kernel.ι tensorInclusion).hom pointKernelOne at h
  exact h.trans pointKernelOne_ι

private abbrev A := torHomologyAntidiagonal (-3)

private def a₀ : A := ⟨(-1, -2), by norm_num⟩

private abbrev torFamily (a : A) : AddCommGrpCat.{2} :=
  ((ModuleCat.BalancedTensor.torFirst ℤ 1).obj (PL.homology a.val.1)).obj
    (QL.homology a.val.2)

private abbrev boundaryFamily (a : A) : AddCommGrpCat.{2} :=
  (G.obj (Abelian.image (PL.d (a.val.1 + 1) a.val.1))).obj (QL.homology a.val.2)

private abbrev cycleFamily (a : A) : AddCommGrpCat.{2} :=
  (G.obj (PL.cycles a.val.1)).obj (QL.homology a.val.2)

private abbrev wholeTor : AddCommGrpCat.{2} := ∐ torFamily

private abbrev S : (∐ boundaryFamily) ⟶ (∐ cycleFamily) :=
  torAntidiagonalTensorMap ℤ PL QL (-3)

private abbrev δ : wholeTor ⟶ (∐ boundaryFamily) :=
  torAntidiagonalBoundary ℤ PL QL (-3)

private def wholeComparison : wholeTor ≅ kernel S := by
  letI : ∀ p : ℤ, (G.obj (PL.X p)).PreservesHomology := termExact
  letI : ∀ p : ℤ, (G.obj (Abelian.image (PL.d p (c.next p)))).PreservesHomology :=
    outgoingExact
  exact torAntidiagonalKernelIsoAt ℤ P Q₁ (-3)

private lemma wholeComparison_ι :
    wholeComparison.hom ≫ kernel.ι S = δ := by
  letI : ∀ p : ℤ, (G.obj (PL.X p)).PreservesHomology := termExact
  letI : ∀ p : ℤ, (G.obj (Abelian.image (PL.d p (c.next p)))).PreservesHomology :=
    outgoingExact
  change (torAntidiagonalKernelIso ℤ PL QL (-3)).hom ≫
    kernel.ι (torAntidiagonalTensorMap ℤ PL QL (-3)) =
      torAntidiagonalBoundary ℤ PL QL (-3)
  exact torAntidiagonalKernelIso_hom_ι ℤ PL QL (-3)

private def y : wholeTor := (Limits.Sigma.ι torFamily a₀).hom τ

private def detector : (∐ boundaryFamily) ⟶ I₂ :=
  Limits.Sigma.desc (fun a => if h : a = a₀ then
    eqToHom (congrArg boundaryFamily h) ≫ pointDetector else 0)

private lemma detector_summand :
    Limits.Sigma.ι boundaryFamily a₀ ≫ detector = pointDetector := by
  simp only [detector, Limits.Sigma.ι_desc, dif_pos rfl, eqToHom_refl, Category.id_comp]

private lemma boundary_summand :
    Limits.Sigma.ι torFamily a₀ ≫ δ =
      torBoundary ℤ PL V 0 (-1) incoming ≫ Limits.Sigma.ι boundaryFamily a₀ := by
  change Limits.Sigma.ι torFamily a₀ ≫
    Limits.Sigma.map (fun a : A =>
      torBoundary ℤ PL (QL.homology a.val.2) (a.val.1 + 1) a.val.1
        ((ComplexShape.down ℤ).prev_eq'
          (show (ComplexShape.down ℤ).Rel (a.val.1 + 1) a.val.1 from rfl))) = _
  rw [Limits.Sigma.ι_map]
  rfl

private lemma boundary_y :
    δ.hom y = (Limits.Sigma.ι boundaryFamily a₀).hom pointOne := by
  have h := ConcreteCategory.congr_hom boundary_summand τ
  change δ.hom y =
    (Limits.Sigma.ι boundaryFamily a₀).hom ((torBoundary ℤ PL V 0 (-1) incoming).hom τ) at h
  rw [τ_boundary] at h
  exact h

private def residue (x : N₂) : ZMod 2 := x.down.down

private lemma boundary_value : residue (detector.hom (δ.hom y)) = 1 := by
  rw [boundary_y]
  have h := ConcreteCategory.congr_hom detector_summand pointOne
  change detector.hom ((Limits.Sigma.ι boundaryFamily a₀).hom pointOne) =
    pointDetector.hom pointOne at h
  rw [h, pointOne_value]
  rfl

private lemma comparison_value :
    residue (detector.hom ((kernel.ι S).hom (wholeComparison.hom.hom y))) = 1 := by
  have h := ConcreteCategory.congr_hom wholeComparison_ι y
  change (kernel.ι S).hom (wholeComparison.hom.hom y) = δ.hom y at h
  rw [h]
  exact boundary_value

example :
    residue (detector.hom ((kernel.ι S).hom (wholeComparison.hom.hom y))) = 1 :=
  comparison_value

example : residue (detector.hom (δ.hom y)) = 1 := boundary_value

example : y ≠ 0 ∧ wholeComparison.hom.hom y ≠ 0 ∧ δ.hom y ≠ 0 := by
  have hδ : δ.hom y ≠ 0 := by
    intro h
    have hv := boundary_value
    rw [h, map_zero] at hv
    change (0 : ZMod 2) = 1 at hv
    exact (by decide : (0 : ZMod 2) ≠ 1) hv
  refine ⟨?_, ?_, hδ⟩
  · intro h
    apply hδ
    rw [h, map_zero]
  · intro h
    have hv := comparison_value
    rw [h, map_zero, map_zero] at hv
    change (0 : ZMod 2) = 1 at hv
    exact (by decide : (0 : ZMod 2) ≠ 1) hv

end IntegerAntidiagonal

end MathlibExtTest.BalancedTensorHomologyCokernel
