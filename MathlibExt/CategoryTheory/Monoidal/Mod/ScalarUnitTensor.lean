/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar
public import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalarsCoherence
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The original scalar unit as the actual relative tensor coefficient map

The existing monadic balanced tensor, original scalar bimodule, both quotient
maps, original induction identity generator and actual scalar unit produce the
entire Arrow comparison. This is the point-set unit of Schwede–Shipley,
math/9801082v1, proof of Theorem 3.3, and EKMM Chapter III §4.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.ExtensionOfScalars.UnitTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : C} [MonObj A] [MonObj B]

/-- The sole original evaluation index of the balancing diagram. -/
abbrev point : Discrete PUnit.{1} := Discrete.mk PUnit.unit

/-- Evaluation at the original index of the balancing diagram. -/
def evalPoint : (Discrete PUnit.{1} ⥤ C) ⥤ C :=
  (evaluation (Discrete PUnit.{1}) C).obj point

theorem scalarRightAssoc (p : A ⟶ B) [IsMonHom p] :
    (α_ B A A).hom ≫ (B ◁ μ[A]) ≫ Mod.ExtensionOfScalars.rightAction p =
      (Mod.ExtensionOfScalars.rightAction p ▷ A) ≫ Mod.ExtensionOfScalars.rightAction p := by
  rw [Mod.ExtensionOfScalars.rightAction_assoc, Iso.hom_inv_id_assoc]

/-- The original right-action module defining the scalar coefficient. -/
def coefficientModule (p : A ⟶ B) [IsMonHom p] :
    Monad.RightModule (Monad.tensorMonad A) C :=
  Monad.rightModuleOfRightAction B A (Mod.ExtensionOfScalars.rightAction p)
    (Mod.ExtensionOfScalars.rightAction_one p) (scalarRightAssoc p)

/-- The original source module represented as a monadic left point module. -/
def inputModule (M : Mod C A) : Monad.LeftModule (Discrete PUnit.{1}) (Monad.tensorMonad A) :=
  Monad.leftPointModule A M.X

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The original right-module scalar coefficient. -/
def rightCoefficient (p : A ⟶ B) [IsMonHom p] : RightModuleFree.Carrier A where
  X := B
  mod :=
    { smul := (Mod.ExtensionOfScalars.scalarBimodule p).actRight
      one_smul := by
        change (B ◁ η[A]) ≫ Mod.ExtensionOfScalars.rightAction p = (ρ_ B).hom
        exact Mod.ExtensionOfScalars.rightAction_one p
      mul_smul := by
        change (B ◁ μ[A]) ≫ Mod.ExtensionOfScalars.rightAction p =
          (α_ B A A).inv ≫ (Mod.ExtensionOfScalars.rightAction p ▷ A) ≫
            Mod.ExtensionOfScalars.rightAction p
        exact Mod.ExtensionOfScalars.rightAction_assoc p }

theorem rightCoefficient_carrier (p : A ⟶ B) [IsMonHom p] : (rightCoefficient p).X = B := rfl

theorem rightCoefficient_action (p : A ⟶ B) [IsMonHom p] :
    (rightCoefficient p).mod.smul = (B ◁ p) ≫ μ[B] := rfl

theorem rightCoefficient_identity_action : (rightCoefficient (𝟙 A)).mod.smul = μ[A] := by
  simp only [rightCoefficient_action, whiskerLeft_id, Category.id_comp]

theorem freeUnit_formula (X : C) :
    Mod.ExtensionOfScalars.freeUnit (B := B) X = (λ_ X).inv ≫ (η[B] ▷ X) := by
  have h := Mod.freeForgetAdjunction_unit_app B X
  change Mod.ExtensionOfScalars.freeUnit (B := B) X =
    (λ_ X).inv ≫ (η[B] ▷ X) ≫ 𝟙 (B ⊗ X) at h
  simpa only [Category.comp_id] using h

/-- The first balancing map of the original scalar tensor coequalizer. -/
abbrev fst (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :=
  Monad.balanceFst (Monad.tensorMonad A) (coefficientModule p) (inputModule M)

/-- The second balancing map of the original scalar tensor coequalizer. -/
abbrev snd (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :=
  Monad.balanceSnd (Monad.tensorMonad A) (coefficientModule p) (inputModule M)

theorem fst_point (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    (fst p M).app point =
      (α_ B A M.X).inv ≫ (Mod.ExtensionOfScalars.rightAction p ▷ M.X) := by
  rfl

theorem snd_point (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    (snd p M).app point = B ◁ M.mod.smul := by
  rfl

section Colimits

variable [HasColimitsOfSize.{0, 0} C]

instance : PreservesColimitsOfShape WalkingParallelPair (evalPoint (C := C)) := by
  change PreservesColimitsOfShape WalkingParallelPair
    ((evaluation (Discrete PUnit.{1}) C).obj point)
  infer_instance

/-- The original monadic balanced tensor of the scalar coefficient and input. -/
abbrev balanced (p : A ⟶ B) [IsMonHom p] (M : Mod C A) : Discrete PUnit.{1} ⥤ C :=
  Monad.monoidalBalancedTensor B A M.X (Mod.ExtensionOfScalars.rightAction p)
    (Mod.ExtensionOfScalars.rightAction_one p) (scalarRightAssoc p)

/-- The scalar tensor obtained from the actual coequalizer. -/
abbrev tensorObject (p : A ⟶ B) [IsMonHom p] (M : Mod C A) : C :=
  (balanced p M).obj point

/-- The original quotient projection to the scalar tensor. -/
abbrev projection (p : A ⟶ B) [IsMonHom p] (M : Mod C A) : B ⊗ M.X ⟶ tensorObject p M :=
  (Monad.balancedTensorπ (Monad.tensorMonad A) (coefficientModule p) (inputModule M)).app point

/-- The comparison between the original balancing diagrams. -/
def rawDiagramIso (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    parallelPair ((evalPoint (C := C)).map (fst p M)) ((evalPoint (C := C)).map (snd p M)) ≅
      parallelPair ((Mod.ExtensionOfScalars.scalarBimodule p).actRight ▷ M.X)
        ((α_ B A M.X).hom ≫ (B ◁ M.mod.smul)) :=
  parallelPairIso _ _ _ _ (α_ B A M.X).symm (Iso.refl (B ⊗ M.X))
    (by
      change ((α_ B A M.X).inv ≫ (Mod.ExtensionOfScalars.rightAction p ▷ M.X)) ≫
        𝟙 (B ⊗ M.X) =
        (α_ B A M.X).inv ≫ (Mod.ExtensionOfScalars.rightAction p ▷ M.X)
      exact Category.comp_id _)
    (by
      change (B ◁ M.mod.smul) ≫ 𝟙 (B ⊗ M.X) =
        (α_ B A M.X).inv ≫ (α_ B A M.X).hom ≫ (B ◁ M.mod.smul)
      simp only [Category.comp_id, Iso.inv_hom_id_assoc])

/-- The original balanced-tensor carrier comparison. -/
def balancedCarrierIso (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    tensorObject p M ≅ Mod.ExtensionOfScalars.relativeTensorCarrier p M :=
  (PreservesCoequalizer.iso (evalPoint (C := C)) (fst p M) (snd p M)).symm ≪≫
    HasColimit.isoOfNatIso (rawDiagramIso p M)

theorem projection_carrier (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    projection p M ≫ (balancedCarrierIso p M).hom =
      Mod.ExtensionOfScalars.relativeTensorπ p M := by
  change (evalPoint (C := C)).map (coequalizer.π (fst p M) (snd p M)) ≫
      (PreservesCoequalizer.iso (evalPoint (C := C)) (fst p M) (snd p M)).inv ≫
        (HasColimit.isoOfNatIso (rawDiagramIso p M)).hom = _
  rw [map_π_preserves_coequalizer_inv_assoc, HasColimit.ι_isoOfNatIso_hom]
  exact Category.id_comp _

omit [HasColimitsOfSize.{0, 0} C] in
theorem coefficient_linear (p : A ⟶ B) [IsMonHom p] :
    (p ▷ A) ≫ Mod.ExtensionOfScalars.rightAction p =
      Mod.ExtensionOfScalars.rightAction (𝟙 A) ≫ p := by
  simp only [Mod.ExtensionOfScalars.rightAction, whiskerLeft_id, Category.id_comp]
  simpa only [tensorHom_def, Category.assoc] using (IsMonHom.mul_hom (f := p)).symm

omit [HasColimitsOfSize.{0, 0} C] in
/-- The coefficient map induced by the original scalar morphism. -/
def rightCoefficientMap (p : A ⟶ B) [IsMonHom p] :
    rightCoefficient (𝟙 A) ⟶ rightCoefficient p :=
  Mod.Hom.mk' p (by
    change Mod.ExtensionOfScalars.rightAction (𝟙 A) ≫ p =
      (p ▷ A) ≫ Mod.ExtensionOfScalars.rightAction p
    exact (coefficient_linear p).symm)

omit [HasColimitsOfSize.{0, 0} C] in
theorem rightCoefficientMap_hom (p : A ⟶ B) [IsMonHom p] :
    (rightCoefficientMap p).hom = p := rfl

/-- The evaluated original scalar coefficient map. -/
def coefficientMap (p : A ⟶ B) [IsMonHom p] :
    coefficientModule (𝟙 A) ⟶ coefficientModule p :=
  Monad.rightModuleHomOfRightComp p (coefficient_linear p)

omit [HasColimitsOfSize.{0, 0} C] in
theorem coefficientMap_original (p : A ⟶ B) [IsMonHom p] (X : C) :
    (coefficientMap p).f.app X = (rightCoefficientMap p).hom ▷ X := rfl

/-- The map on original scalar tensors induced by the coefficient morphism. -/
def tensorMap (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    tensorObject (𝟙 A) M ⟶ tensorObject p M :=
  (Monad.balancedTensorMap (coefficientMap p) (𝟙 (inputModule M))).app point

theorem tensorMap_projection (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    projection (𝟙 A) M ≫ tensorMap p M = (p ▷ M.X) ≫ projection p M := by
  have h := congrArg (fun f => f.app point)
    (Monad.balancedTensorMap_π (coefficientMap p) (𝟙 (inputModule M)))
  change projection (𝟙 A) M ≫ tensorMap p M =
    (Monad.barMap (coefficientMap p) (𝟙 (inputModule M)) 0).app point ≫ projection p M at h
  have hb : (Monad.barMap (coefficientMap p) (𝟙 (inputModule M)) 0).app point = p ▷ M.X := by
    change (A ◁ 𝟙 M.X) ≫ (p ▷ M.X) = p ▷ M.X
    rw [whiskerLeft_id, Category.id_comp]
  rw [hb] at h
  exact h

section ModuleCarrier

variable [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]

/-- The original module carrier identification for the scalar tensor. -/
def moduleCarrierIso (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    tensorObject p M ≅ (Mod.ExtensionOfScalars.object p M).X :=
  balancedCarrierIso p M ≪≫ (Mod.ExtensionOfScalars.carrierIso p M).symm

theorem projection_module (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    projection p M ≫ (moduleCarrierIso p M).hom = (Mod.ExtensionOfScalars.π p M).hom := by
  change projection p M ≫ (balancedCarrierIso p M).hom ≫
      (Mod.ExtensionOfScalars.carrierIso p M).inv = _
  rw [← Category.assoc, projection_carrier, ← Mod.ExtensionOfScalars.π_carrierIso p M]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end ModuleCarrier

section Regular

variable [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]

/-- The tensor identification using the original regular scalar coefficient. -/
def regularTensorIso (M : Mod C A) : tensorObject (𝟙 A) M ≅ M.X :=
  moduleCarrierIso (𝟙 A) M ≪≫
    (Mod.forget A).mapIso ((Mod.ExtensionOfScalars.inductionIdIso (A := A)).app M)

theorem regularTensorIso_inv (M : Mod C A) :
    (regularTensorIso M).inv =
      (λ_ M.X).inv ≫ (η[A] ▷ M.X) ≫ projection (𝟙 A) M := by
  apply (cancel_mono (regularTensorIso M).hom).mp
  rw [Iso.inv_hom_id]
  change 𝟙 M.X =
    ((λ_ M.X).inv ≫ (η[A] ▷ M.X) ≫ projection (𝟙 A) M) ≫
      (moduleCarrierIso (𝟙 A) M).hom ≫
        ((Mod.ExtensionOfScalars.inductionIdIso (A := A)).hom.app M).hom
  simp only [Category.assoc]
  rw [← Category.assoc (projection (𝟙 A) M) (moduleCarrierIso (𝟙 A) M).hom,
    projection_module]
  rw [← Category.assoc (λ_ M.X).inv (η[A] ▷ M.X), ← freeUnit_formula (B := A)]
  rw [← Category.assoc (Mod.ExtensionOfScalars.freeUnit (B := A) M.X)
    (Mod.ExtensionOfScalars.π (𝟙 A) M).hom]
  change 𝟙 M.X = Mod.ExtensionOfScalars.generator (𝟙 A) M ≫
    ((Mod.ExtensionOfScalars.inductionIdIso (A := A)).hom.app M).hom
  exact (Mod.ExtensionOfScalars.inductionIdIso_generator M).symm

end Regular

section UnitBridge

variable [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]

theorem unit_tensor_inverse (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    (regularTensorIso M).inv ≫ tensorMap p M ≫ (moduleCarrierIso p M).hom =
      ((Mod.ExtensionOfScalars.adjunction p).unit.app M).hom := by
  rw [Mod.ExtensionOfScalars.unit_hom]
  rw [regularTensorIso_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (projection (𝟙 A) M) (tensorMap p M), tensorMap_projection]
  simp only [Category.assoc]
  rw [projection_module]
  rw [← Category.assoc (η[A] ▷ M.X) (p ▷ M.X), ← comp_whiskerRight, IsMonHom.one_hom]
  rw [← Category.assoc (λ_ M.X).inv (η[B] ▷ M.X), ← freeUnit_formula (B := B)]
  rfl

theorem unit_tensor_square (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    (regularTensorIso M).hom ≫ ((Mod.ExtensionOfScalars.adjunction p).unit.app M).hom =
      tensorMap p M ≫ (moduleCarrierIso p M).hom := by
  rw [← unit_tensor_inverse p M]
  simp only [Iso.hom_inv_id_assoc]

/-- The whole Arrow comparison of the scalar tensor map with the original adjunction unit. -/
def unitTensorArrowIso (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    Arrow.mk (tensorMap p M) ≅
      Arrow.mk ((Mod.ExtensionOfScalars.adjunction p).unit.app M).hom :=
  Arrow.isoMk (regularTensorIso M) (moduleCarrierIso p M) (unit_tensor_square p M)

theorem unit_tensor_carrier (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    ((Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫
        (Mod.ExtensionOfScalars.carrierIso p M).hom =
      (regularTensorIso M).inv ≫ tensorMap p M ≫ (balancedCarrierIso p M).hom := by
  rw [← unit_tensor_inverse p M]
  simp only [moduleCarrierIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end UnitBridge

end Colimits

end CategoryTheory.Mod.ExtensionOfScalars.UnitTensor
