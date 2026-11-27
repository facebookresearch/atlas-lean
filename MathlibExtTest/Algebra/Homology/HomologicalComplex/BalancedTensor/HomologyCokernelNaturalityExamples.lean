/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.HomologyCokernelNaturality
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A nonsplit coefficient quotient on a tensor boundary cokernel

The right integer complex has ℤ in every degree, multiplication by two
from degree zero to degree minus one, and zero differentials elsewhere.
Its boundary inclusion at degree minus one is 2ℤ → ℤ.

The coefficient quotient ℤ/4 → ℤ/2 has no ℤ-linear section. The right
complex starts in carrier universe zero and the coefficients in carrier
universe one; both are lifted canonically to universe two.

The coefficient-induced tensor boundary cokernel map sends the class of
1 ⊗ 1 to the class of 1 ⊗ 1. The target class is detected as one in the
lifted ℤ/2 coefficient. Coefficient naturality gives the same detected
value after the homology tensor comparison. The source class, its
cokernel image and its homology tensor image are therefore nonzero.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex.BalancedTensor

namespace HomologicalComplex.BalancedTensor.NaturalityExamples

private abbrev Z : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ
private abbrev N40 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)
private abbrev N20 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev N4 : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N40
private abbrev N2 : ModuleCat.{1} ℤ := (ModuleCat.uliftFunctor.{1, 0} ℤ).obj N20

private def quotient0 : N40 ⟶ N20 :=
  ModuleCat.ofHom
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toIntLinearMap

private def quotient1 : N4 ⟶ N2 := (ModuleCat.uliftFunctor.{1, 0} ℤ).map quotient0

private lemma quotient0_no_section :
    ¬ ∃ s : N20 ⟶ N40, s ≫ quotient0 = 𝟙 N20 := by
  rintro ⟨s, hs⟩
  have hq := ConcreteCategory.congr_hom hs (1 : ZMod 2)
  change quotient0.hom (s.hom (1 : ZMod 2)) = 1 at hq
  have htwo : (2 : ℤ) • s.hom (1 : ZMod 2) = 0 := by
    rw [← map_zsmul]
    norm_num
  have heven : s.hom (1 : ZMod 2) = 0 ∨ s.hom (1 : ZMod 2) = 2 :=
    (by decide : ∀ a : ZMod 4, (2 : ℤ) • a = 0 → a = 0 ∨ a = 2) _ htwo
  rcases heven with h | h
  · rw [h, map_zero] at hq
    exact (by decide : (0 : ZMod 2) ≠ 1) hq
  · rw [h] at hq
    change (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (2 : ZMod 4) = 1 at hq
    norm_num at hq

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

private abbrev Z2 : ModuleCat.{2} ℤᵐᵒᵖ := (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).obj Z
private abbrev P2 : ChainComplex (ModuleCat.{2} ℤᵐᵒᵖ) ℤ :=
  ((ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).mapHomologicalComplex c).obj P
private abbrev N42 : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N4
private abbrev N22 : ModuleCat.{2} ℤ := (ModuleCat.uliftFunctor.{2, 1} ℤ).obj N2
private abbrev quotient2 : N42 ⟶ N22 :=
  (ModuleCat.uliftFunctor.{2, 1} ℤ).map quotient1
private abbrev I2 := (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj N22
private abbrev G : ModuleCat.{2} ℤᵐᵒᵖ ⥤ ModuleCat.{2} ℤ ⥤ AddCommGrpCat.{2} :=
  ModuleCat.BalancedTensor.groupBifunctor ℤ

private lemma differential_lifted (x : Z2) :
    (P2.d 0 (-1)).hom x = ULift.up (2 * x.down) := by
  change ULift.up ((P.d 0 (-1)).hom x.down) = _
  rw [differential_value]

private lemma outgoing_lifted_zero : P2.d (-1) (c.next (-1)) = 0 := by
  change (ModuleCat.uliftFunctor.{2, 0} ℤᵐᵒᵖ).map (P.d (-1) (c.next (-1))) = 0
  rw [outgoing_zero, Functor.map_zero]

private def cyclesIso : P2.cycles (-1) ≅ Z2 :=
  P2.iCyclesIso (-1) (c.next (-1)) rfl outgoing_lifted_zero

private lemma cyclesIso_hom : cyclesIso.hom = P2.iCycles (-1) := rfl

private def oneCycle : P2.cycles (-1) := cyclesIso.inv.hom (ULift.up (1 : ℤ))

private lemma oneCycle_value : cyclesIso.hom.hom oneCycle = ULift.up (1 : ℤ) :=
  ConcreteCategory.congr_hom cyclesIso.inv_hom_id (ULift.up (1 : ℤ))

private def regularTensorIso (W : ModuleCat.{2} ℤ) :
    (G.obj Z2).obj W ≅ (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj W := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  let e : TensorProduct.Balanced ℤ ℤ Z2 W ≃ₗ[ℤ]
      TensorProduct.Balanced ℤ ℤ ℤ W :=
    TensorProduct.Balanced.congr (k := ℤ) (R := ℤ)
      (ULift.moduleEquiv : Z2 ≃ₗ[ℤ] ℤ) (LinearEquiv.refl ℤ W)
      (by intro r x; rfl) (by intro r w; rfl)
  exact (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).mapIso
    (e.trans (TensorProduct.Balanced.leftUnitor ℤ ℤ W)).toModuleIso

private lemma regularTensorIso_mk (W : ModuleCat.{2} ℤ) (x : Z2) (w : W) :
    letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
    (regularTensorIso W).hom.hom (TensorProduct.Balanced.mk ℤ ℤ Z2 W x w) =
      x.down • w := by
  letI : Module ℤ W := Module.compHom W (algebraMap ℤ ℤ)
  change (TensorProduct.Balanced.leftUnitor ℤ ℤ W)
    ((TensorProduct.Balanced.congr (k := ℤ) (R := ℤ)
      (ULift.moduleEquiv : Z2 ≃ₗ[ℤ] ℤ) (LinearEquiv.refl ℤ W)
      (by intro r z; rfl) (by intro r z; rfl))
        (TensorProduct.Balanced.mk ℤ ℤ Z2 W x w)) = _
  rw [TensorProduct.Balanced.congr_mk, TensorProduct.Balanced.leftUnitor_mk]
  rfl

private def cycleProjection (W : ModuleCat.{2} ℤ) :
    (G.obj (P2.cycles (-1))).obj W ⟶
      (forget₂ (ModuleCat.{2} ℤ) AddCommGrpCat.{2}).obj W :=
  (G.map cyclesIso.hom).app W ≫ (regularTensorIso W).hom

private lemma cycleProjection_mk (W : ModuleCat.{2} ℤ) (z : P2.cycles (-1)) (w : W) :
    (cycleProjection W).hom
      (ModuleCat.BalancedTensor.groupPure ℤ (P2.cycles (-1)) W z w) =
        (cyclesIso.hom.hom z).down • w := by
  change (regularTensorIso W).hom.hom
    (((G.map cyclesIso.hom).app W).hom
      (TensorProduct.Balanced.mk ℤ ℤ (P2.cycles (-1)) W z w)) = _
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk]

private abbrev β := HomologicalComplex.boundaryCyclesMap P2 0 (-1)
private abbrev F2 := G.flip.obj N22
private abbrev β2 := F2.map β

private lemma coefficient_two (n : N22) : (2 : ℤ) • n = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (2 : ℤ) • n.down.down = 0
  rw [zsmul_eq_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private lemma tensorDifferential_projection_zero :
    F2.map (P2.d 0 (-1)) ≫ (regularTensorIso N22).hom = 0 := by
  apply ModuleCat.BalancedTensor.groupHom_ext ℤ Z2 N22 I2
  intro x n
  change (regularTensorIso N22).hom.hom
    ((F2.map (P2.d 0 (-1))).hom (TensorProduct.Balanced.mk ℤ ℤ Z2 N22 x n)) = 0
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk,
    differential_lifted]
  change (2 * x.down) • n = 0
  rw [mul_comm, ← smul_smul, coefficient_two, smul_zero]

private lemma boundary_projection_zero : β2 ≫ cycleProjection N22 = 0 := by
  let a := Abelian.factorThruImage (P2.d 0 (-1))
  letI : Epi (F2.map a) := inferInstance
  apply (cancel_epi (F2.map a)).1
  have h :
      F2.map a ≫ F2.map β ≫ cycleProjection N22 =
        F2.map (P2.d 0 (-1)) ≫ (regularTensorIso N22).hom := by
    change F2.map a ≫ F2.map β ≫ F2.map cyclesIso.hom ≫
      (regularTensorIso N22).hom = _
    rw [cyclesIso_hom]
    calc
      _ = F2.map (a ≫ β ≫ P2.iCycles (-1)) ≫ (regularTensorIso N22).hom := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by rw [HomologicalComplex.boundaryCyclesMap_i, Abelian.image.fac]
  simpa only [Category.assoc, comp_zero] using h.trans tensorDifferential_projection_zero

private abbrev K4 := cokernel ((G.flip.obj N42).map β)
private abbrev K2 := cokernel β2

private def coefficientMap : K4 ⟶ K2 :=
  homologyTensorCokernelCoeffMapAt.{2} ℤ P quotient1 0 (-1)

private def comparison4 : K4 ≅ (G.obj (P2.homology (-1))).obj N42 :=
  homologyTensorCokernelIsoAt.{2} ℤ P N4 0 (-1) incoming

private def comparison2 : K2 ≅ (G.obj (P2.homology (-1))).obj N22 :=
  homologyTensorCokernelIsoAt.{2} ℤ P N2 0 (-1) incoming

private def homologyCoefficientMap :
    (G.obj (P2.homology (-1))).obj N42 ⟶ (G.obj (P2.homology (-1))).obj N22 :=
  (G.obj (P2.homology (-1))).map quotient2

private def one4 : N42 := ULift.up (ULift.up (1 : ZMod 4))
private def one2 : N22 := ULift.up (ULift.up (1 : ZMod 2))

private lemma quotient_one : quotient2.hom one4 = one2 := by
  change ULift.up (ULift.up
    ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (1 : ZMod 4))) =
      ULift.up (ULift.up (1 : ZMod 2))
  rw [map_one]

private def sourceOne : K4 := (cokernel.π ((G.flip.obj N42).map β)).hom
  (ModuleCat.BalancedTensor.groupPure ℤ (P2.cycles (-1)) N42 oneCycle one4)

private def targetOne : K2 := (cokernel.π β2).hom
  (ModuleCat.BalancedTensor.groupPure ℤ (P2.cycles (-1)) N22 oneCycle one2)

private lemma coefficientMap_sourceOne : coefficientMap.hom sourceOne = targetOne := by
  have h := homologyTensorCokernelCoeffMap_mk ℤ P2 quotient2 0 (-1) oneCycle one4
  change coefficientMap.hom sourceOne =
    (cokernel.π β2).hom
      (ModuleCat.BalancedTensor.groupPure ℤ (P2.cycles (-1)) N22 oneCycle
        (quotient2.hom one4)) at h
  rw [quotient_one] at h
  exact h

private def detector : K2 ⟶ I2 :=
  cokernel.desc β2 (cycleProjection N22) boundary_projection_zero

private lemma detector_targetOne : detector.hom targetOne = one2 := by
  have h := ConcreteCategory.congr_hom
    (cokernel.π_desc β2 (cycleProjection N22) boundary_projection_zero)
    (ModuleCat.BalancedTensor.groupPure ℤ (P2.cycles (-1)) N22 oneCycle one2)
  change detector.hom targetOne = _ at h
  rw [cycleProjection_mk, oneCycle_value] at h
  change detector.hom targetOne = (1 : ℤ) • one2 at h
  simpa only [one_smul] using h

private def homologyDetector : (G.obj (P2.homology (-1))).obj N22 ⟶ I2 :=
  comparison2.inv ≫ detector

private lemma homologyDetector_comparison_targetOne :
    homologyDetector.hom (comparison2.hom.hom targetOne) = one2 := by
  change detector.hom (comparison2.inv.hom (comparison2.hom.hom targetOne)) = one2
  have h := ConcreteCategory.congr_hom comparison2.hom_inv_id targetOne
  rw [h]
  exact detector_targetOne

private lemma coefficient_naturality_value :
    homologyDetector.hom
      (homologyCoefficientMap.hom (comparison4.hom.hom sourceOne)) = one2 := by
  have h := ConcreteCategory.congr_hom
    (homologyTensorCokernelIsoAt_coeff_naturality.{2} ℤ P quotient1 0 (-1) incoming)
    sourceOne
  change homologyCoefficientMap.hom (comparison4.hom.hom sourceOne) =
    comparison2.hom.hom (coefficientMap.hom sourceOne) at h
  rw [h, coefficientMap_sourceOne]
  exact homologyDetector_comparison_targetOne

example : ¬ ∃ s : N20 ⟶ N40, s ≫ quotient0 = 𝟙 N20 := quotient0_no_section

example : (P2.d 0 (-1)).hom (ULift.up (1 : ℤ)) = ULift.up (2 : ℤ) := by
  simpa only [mul_one] using differential_lifted (ULift.up (1 : ℤ))

example : detector.hom (coefficientMap.hom sourceOne) = one2 := by
  rw [coefficientMap_sourceOne]
  exact detector_targetOne

example :
    homologyDetector.hom
      (homologyCoefficientMap.hom (comparison4.hom.hom sourceOne)) = one2 :=
  coefficient_naturality_value

example :
    sourceOne ≠ 0 ∧ coefficientMap.hom sourceOne ≠ 0 ∧
      homologyCoefficientMap.hom (comparison4.hom.hom sourceOne) ≠ 0 := by
  have hone : one2 ≠ 0 := by
    intro h
    have hv := congrArg (fun n : N22 => n.down.down) h
    exact (by decide : (1 : ZMod 2) ≠ 0) hv
  have hmap : coefficientMap.hom sourceOne ≠ 0 := by
    intro h
    apply hone
    rw [← detector_targetOne, ← coefficientMap_sourceOne, h, map_zero]
  refine ⟨?_, hmap, ?_⟩
  · intro h
    apply hmap
    rw [h, map_zero]
  · intro h
    apply hone
    rw [← coefficient_naturality_value, h, map_zero]

end HomologicalComplex.BalancedTensor.NaturalityExamples
