/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryJLoopComparison
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The whole original J loop functor and its ordinary derived adjunction

The original J path-cone functor gives the full point-set loop functor.
Every map in the based-path comparison is the original limiting map or the
original fixed-κ J middle map on a complete Arrow square. The resulting
comparison is natural in both actual path endpoints.

For the same original framing, this constructs a natural comparison with
the actual derived ordinary loops. The original J loop functor after the
same original R replacement therefore preserves weak equivalences and
descends to the whole original homotopy category. Its full adjunction with
ordinary suspension retains the original unit, counit and both Hom functions
through the earned natural isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped ZeroObject Simplicial

namespace HomotopicalAlgebra.OriginalOrdinaryJLoopFunctor

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "Pᵒ" => OriginalOrdinaryJPathCone.oppositeCone g Z hZ
local notation "ιᵒ" => OriginalOrdinaryJPathCone.oppositeInclusion g Z hZ
local notation "cᵒ" => OriginalOrdinaryJPathCone.oppositeCofiberCocone g Z hZ
local notation "hcᵒ" => OriginalOrdinaryJPathCone.oppositeCofiberIsColimit g Z hZ
local notation "J" => GeneratedArrowFactorizations.fibrant g
local notation "H" => toHomotopyCategory C

/-- The entire point-set loop functor is the actual original opposite chosen suspension. -/
def loopFunctor : C ⥤ C :=
  (OrdinaryHoChosenPuppe.suspensionFunctor Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op).unop

/-- Each full functor object is the same original J loop carrier. -/
theorem loopFunctor_obj (Y : C) :
    (loopFunctor g Z hZ).obj Y = OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ Y := rfl

/-- Every full functor map is the same original opposite chosen suspension map. -/
theorem loopFunctor_map {X Y : C} (f : X ⟶ Y) :
    (loopFunctor g Z hZ).map f =
      (OrdinaryHoChosenPuppe.suspensionMap Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op f.op).unop := rfl

/-- The full original point-set loop map retains the entire original path-object map. -/
@[reassoc (attr := simp)]
theorem loopFunctor_map_pathLeg {X Y : C} (f : X ⟶ Y) :
    (loopFunctor g Z hZ).map f ≫ OriginalOrdinaryJLoopComparison.loopPathLeg g Z hZ Y =
      OriginalOrdinaryJLoopComparison.loopPathLeg g Z hZ X ≫
        (OriginalOrdinaryJPathCone.pathObject g Z hZ).map f := by
  have h := congrArg Quiver.Hom.unop
    (OrdinaryHoChosenPuppe.suspensionMap_cone Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op f.op)
  simpa only [unop_comp, OriginalOrdinaryJPathCone.oppositeCone, Functor.op_map, Functor.op_obj,
    Quiver.Hom.unop_op, OriginalOrdinaryJLoopComparison.loopPathLeg, loopFunctor_map,
    loopFunctor_obj, OriginalOrdinaryCovariantPuppeConnection.loopObject] using h

/-- The full original point-set loop map retains the same original zero projection. -/
@[reassoc (attr := simp)]
theorem loopFunctor_map_zeroLeg {X Y : C} (f : X ⟶ Y) :
    (loopFunctor g Z hZ).map f ≫ OriginalOrdinaryJLoopComparison.loopZeroLeg g Z hZ Y =
      OriginalOrdinaryJLoopComparison.loopZeroLeg g Z hZ X := by
  have h := congrArg Quiver.Hom.unop
    (OrdinaryHoChosenPuppe.suspensionMap_zero Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op f.op)
  simpa only [unop_comp, OriginalOrdinaryJLoopComparison.loopZeroLeg, loopFunctor_map] using h

/-- Every actual original target arrow gives the full original J fibre map on the entire projection square. -/
def originalFiberMap {X Y : C} (f : X ⟶ Y) :
    OriginalOrdinaryJLoopComparison.originalFiber g Z hZ X ⟶
      OriginalOrdinaryJLoopComparison.originalFiber g Z hZ Y :=
  pullback.map ((OriginalOrdinaryJPathCone.projection g Z hZ).app X) (hZ.isInitial.to X)
    ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y)
    ((OriginalOrdinaryJPathCone.pathObject g Z hZ).map f) (𝟙 Z) f
    (by
      have h := (OriginalOrdinaryJPathCone.projection g Z hZ).naturality f
      change (OriginalOrdinaryJPathCone.pathObject g Z hZ).map f ≫
        (OriginalOrdinaryJPathCone.projection g Z hZ).app Y =
          (OriginalOrdinaryJPathCone.projection g Z hZ).app X ≫ f at h
      exact h.symm) (hZ.isInitial.hom_ext _ _)

/-- The whole original fibre map retains the actual original path-object map. -/
@[reassoc (attr := simp)]
theorem originalFiberMap_fst {X Y : C} (f : X ⟶ Y) :
    originalFiberMap g Z hZ f ≫
        pullback.fst ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) =
      pullback.fst ((OriginalOrdinaryJPathCone.projection g Z hZ).app X) (hZ.isInitial.to X) ≫
        (OriginalOrdinaryJPathCone.pathObject g Z hZ).map f :=
  pullback.lift_fst _ _ _

/-- The whole original fibre map retains the same original zero identity. -/
@[reassoc (attr := simp)]
theorem originalFiberMap_snd {X Y : C} (f : X ⟶ Y) :
    originalFiberMap g Z hZ f ≫
        pullback.snd ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) =
      pullback.snd ((OriginalOrdinaryJPathCone.projection g Z hZ).app X) (hZ.isInitial.to X) := by
  simpa only [Category.comp_id] using
    (show originalFiberMap g Z hZ f ≫
      pullback.snd ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) =
        pullback.snd ((OriginalOrdinaryJPathCone.projection g Z hZ).app X) (hZ.isInitial.to X) ≫ 𝟙 Z
      from pullback.lift_snd _ _ _)

/-- The complete original loop/fibre carrier isomorphism is natural on every original target arrow. -/
theorem loopIsoFiber_naturality {X Y : C} (f : X ⟶ Y) :
    (loopFunctor g Z hZ).map f ≫ (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom =
      (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ X).hom ≫ originalFiberMap g Z hZ f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, OriginalOrdinaryJLoopComparison.loopIsoFiber_fst, originalFiberMap_fst]
    rw [loopFunctor_map_pathLeg, ← Category.assoc,
      OriginalOrdinaryJLoopComparison.loopIsoFiber_fst]
  · simp only [Category.assoc, OriginalOrdinaryJLoopComparison.loopIsoFiber_snd, originalFiberMap_snd]
    exact loopFunctor_map_zeroLeg g Z hZ f

variable {Y Y' : C} (P : PathObject Y) (P' : PathObject Y')
  (f : Y ⟶ Y') (a : P.P ⟶ P'.P)
  (h₀ : a ≫ P'.p₀ = P.p₀ ≫ f) (h₁ : a ≫ P'.p₁ = P.p₁ ≫ f)

/-- Both original endpoint-map equations give the entire based-path Arrow map. -/
def basedArrowMap :
    OriginalOrdinaryJLoopComparison.basedArrow Z hZ P ⟶
      OriginalOrdinaryJLoopComparison.basedArrow Z hZ P' :=
  Arrow.homMk (OriginalGoodPathFiberGeometry.basedPathMap Z hZ P P' f a h₀) f
    (OriginalGoodPathFiberGeometry.basedPathMap_projection Z hZ P P' f a h₀ h₁)

/-- The actual original J middle map acts on that entire based-path Arrow square. -/
def middleMap : OriginalOrdinaryJLoopComparison.middle g Z hZ P ⟶
    OriginalOrdinaryJLoopComparison.middle g Z hZ P' :=
  (J).Z.map (basedArrowMap Z hZ P P' f a h₀ h₁)

/-- The complete original J left-factor naturality retains the actual whole based-path map. -/
theorem middleMap_left :
    OriginalOrdinaryJLoopComparison.middleLeft g Z hZ P ≫ middleMap g Z hZ P P' f a h₀ h₁ =
      OriginalGoodPathFiberGeometry.basedPathMap Z hZ P P' f a h₀ ≫
        OriginalOrdinaryJLoopComparison.middleLeft g Z hZ P' :=
  ((J).i.naturality (basedArrowMap Z hZ P P' f a h₀ h₁)).symm

/-- The complete original J right-factor naturality retains the actual whole target map. -/
theorem middleMap_right :
    middleMap g Z hZ P P' f a h₀ h₁ ≫ OriginalOrdinaryJLoopComparison.middleRight g Z hZ P' =
      OriginalOrdinaryJLoopComparison.middleRight g Z hZ P ≫ f := by
  have h := (J).p.naturality (basedArrowMap Z hZ P P' f a h₀ h₁)
  exact h

/-- The whole original zero/based-path squares commute before the same original J factory acts. -/
theorem zeroToBasedArrow_naturality :
    (OriginalOrdinaryJPathCone.initialArrowFunctor Z hZ).map f ≫
        OriginalOrdinaryJLoopComparison.zeroToBasedArrow Z hZ P' =
      OriginalOrdinaryJLoopComparison.zeroToBasedArrow Z hZ P ≫ basedArrowMap Z hZ P P' f a h₀ h₁ := by
  apply Arrow.hom_ext
  · exact hZ.isInitial.hom_ext _ _
  · simp [basedArrowMap, OriginalOrdinaryJLoopComparison.zeroToBasedArrow,
      OriginalOrdinaryJPathCone.initialArrowFunctor]

/-- Every actual path map retains the same complete original-to-middle square. -/
theorem originalToMiddle_naturality :
    (OriginalOrdinaryJPathCone.pathObject g Z hZ).map f ≫
        OriginalOrdinaryJLoopComparison.originalToMiddle g Z hZ P' =
      OriginalOrdinaryJLoopComparison.originalToMiddle g Z hZ P ≫ middleMap g Z hZ P P' f a h₀ h₁ := by
  have h := congrArg (fun q => (J).Z.map q)
    (zeroToBasedArrow_naturality Z hZ P P' f a h₀ h₁)
  simpa only [Functor.map_comp, OriginalOrdinaryJPathCone.pathObject, Functor.comp_map,
    OriginalOrdinaryJLoopComparison.originalToMiddle, middleMap] using h

/-- The full original middle-fibre map retains the entire original right-factor square. -/
def middleFiberMap :
    OriginalOrdinaryJLoopComparison.middleFiber g Z hZ P ⟶
      OriginalOrdinaryJLoopComparison.middleFiber g Z hZ P' :=
  pullback.map (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y)
    (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y')
    (middleMap g Z hZ P P' f a h₀ h₁) (𝟙 Z) f
    (middleMap_right g Z hZ P P' f a h₀ h₁).symm (hZ.isInitial.hom_ext _ _)

/-- The full original middle-fibre map retains the original middle map on its first projection. -/
@[reassoc (attr := simp)]
theorem middleFiberMap_fst :
    middleFiberMap g Z hZ P P' f a h₀ h₁ ≫
        pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y') =
      pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y) ≫
        middleMap g Z hZ P P' f a h₀ h₁ :=
  pullback.lift_fst _ _ _

/-- The full original middle-fibre map retains the same original zero projection. -/
@[reassoc (attr := simp)]
theorem middleFiberMap_snd :
    middleFiberMap g Z hZ P P' f a h₀ h₁ ≫
        pullback.snd (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y') =
      pullback.snd (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y) := by
  simpa only [Category.comp_id] using
    (show middleFiberMap g Z hZ P P' f a h₀ h₁ ≫
      pullback.snd (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y') =
        pullback.snd (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y) ≫ 𝟙 Z
      from pullback.lift_snd _ _ _)

/-- The whole original J fibre-to-middle comparison is natural on every actual path map. -/
theorem originalFiberToMiddle_naturality :
    originalFiberMap g Z hZ f ≫ OriginalOrdinaryJLoopComparison.originalFiberToMiddle g Z hZ P' =
      OriginalOrdinaryJLoopComparison.originalFiberToMiddle g Z hZ P ≫
        middleFiberMap g Z hZ P P' f a h₀ h₁ := by
  have hP : OriginalOrdinaryJLoopComparison.originalFiberToMiddle g Z hZ P ≫
      pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y) =
    pullback.fst ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) ≫
      OriginalOrdinaryJLoopComparison.originalToMiddle g Z hZ P := pullback.lift_fst _ _ _
  have hP' : OriginalOrdinaryJLoopComparison.originalFiberToMiddle g Z hZ P' ≫
      pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y') =
    pullback.fst ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y') (hZ.isInitial.to Y') ≫
      OriginalOrdinaryJLoopComparison.originalToMiddle g Z hZ P' := pullback.lift_fst _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFiberMap_fst]
    rw [hP', ← Category.assoc, originalFiberMap_fst, Category.assoc,
      originalToMiddle_naturality, ← Category.assoc, ← hP, Category.assoc]
  · exact hZ.isTerminal.hom_ext _ _

/-- The whole original based-fibre-to-middle comparison is natural on every actual path map. -/
theorem basedFiberToMiddle_naturality :
    OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁ ≫
        OriginalOrdinaryJLoopComparison.basedFiberToMiddle g Z hZ P' =
      OriginalOrdinaryJLoopComparison.basedFiberToMiddle g Z hZ P ≫
        middleFiberMap g Z hZ P P' f a h₀ h₁ := by
  have hP : OriginalOrdinaryJLoopComparison.basedFiberToMiddle g Z hZ P ≫
      pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P) (hZ.isInitial.to Y) =
    pullback.fst (OriginalGoodPathFiberGeometry.projection Z hZ P) (hZ.isInitial.to Y) ≫
      OriginalOrdinaryJLoopComparison.middleLeft g Z hZ P := pullback.lift_fst _ _ _
  have hP' : OriginalOrdinaryJLoopComparison.basedFiberToMiddle g Z hZ P' ≫
      pullback.fst (OriginalOrdinaryJLoopComparison.middleRight g Z hZ P') (hZ.isInitial.to Y') =
    pullback.fst (OriginalGoodPathFiberGeometry.projection Z hZ P') (hZ.isInitial.to Y') ≫
      OriginalOrdinaryJLoopComparison.middleLeft g Z hZ P' := pullback.lift_fst _ _ _
  have hF : OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁ ≫
      pullback.fst (OriginalGoodPathFiberGeometry.projection Z hZ P') (hZ.isInitial.to Y') =
    pullback.fst (OriginalGoodPathFiberGeometry.projection Z hZ P) (hZ.isInitial.to Y) ≫
      OriginalGoodPathFiberGeometry.basedPathMap Z hZ P P' f a h₀ := pullback.lift_fst _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFiberMap_fst]
    rw [hP', ← Category.assoc, hF, Category.assoc, ← middleMap_left,
      ← Category.assoc, ← hP, Category.assoc]
  · exact hZ.isTerminal.hom_ext _ _

variable [IsFibrant Y] [IsFibrant Y'] [P.IsGood] [P'.IsGood]

/-- The entire earned original J-loop/full-path Ho comparison is natural in both actual path endpoints. -/
theorem loopHoIsoPathFiber_naturality :
    (H).map ((loopFunctor g Z hZ).map f) ≫
        (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ P').hom =
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ P).hom ≫
        (H).map (OriginalGoodPathFiberGeometry.pathFiberMap Z hZ P P' f a h₀ h₁) := by
  have hL := congrArg (fun q => (H).map q) (loopIsoFiber_naturality g Z hZ f)
  have hJ := congrArg (fun q => (H).map q) (originalFiberToMiddle_naturality g Z hZ P P' f a h₀ h₁)
  have hB := congrArg (fun q => (H).map q) (basedFiberToMiddle_naturality g Z hZ P P' f a h₀ h₁)
  have hE := congrArg (fun q => (H).map q)
    (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber_naturality Z hZ P P' f a h₀ h₁)
  simp only [Functor.map_comp] at hL hJ hB hE
  change (H).map (originalFiberMap g Z hZ f) ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P').hom =
    (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P).hom ≫
      (H).map (middleFiberMap g Z hZ P P' f a h₀ h₁) at hJ
  change (H).map (OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁) ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').hom =
    (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P).hom ≫
      (H).map (middleFiberMap g Z hZ P P' f a h₀ h₁) at hB
  have hBinv :
      (H).map (middleFiberMap g Z hZ P P' f a h₀ h₁) ≫
          (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv =
        (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P).inv ≫
          (H).map (OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁) := by
    apply (cancel_epi (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
      congrArg (fun q => q ≫ (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv) hB.symm
  simp only [OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  calc
    _ = ((H).map ((loopFunctor g Z hZ).map f) ≫
        (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y').hom) ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P').hom ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by
        simp only [Category.assoc]
    _ = ((H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
        (H).map (originalFiberMap g Z hZ f)) ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P').hom ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by rw [hL]
    _ = (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
      ((H).map (originalFiberMap g Z hZ f) ≫
        (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P').hom) ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by
        simp only [Category.assoc]
    _ = (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
      ((OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P).hom ≫
        (H).map (middleFiberMap g Z hZ P P' f a h₀ h₁)) ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by rw [hJ]
    _ = (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P).hom ≫
      ((H).map (middleFiberMap g Z hZ P P' f a h₀ h₁) ≫
        (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P').inv) ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by
        simp only [Category.assoc]
    _ = (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P).hom ≫
      ((OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P).inv ≫
        (H).map (OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁)) ≫
      (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom := by rw [hBinv]
    _ = (H).map (OriginalOrdinaryJLoopComparison.loopIsoFiber g Z hZ Y).hom ≫
      (OriginalOrdinaryJLoopComparison.originalFiberIsoMiddle g Z hZ P).hom ≫
      (OriginalOrdinaryJLoopComparison.basedFiberIsoMiddle g Z hZ P).inv ≫
      ((H).map (OriginalGoodPathFiberGeometry.basedFiberMap Z hZ P P' f a h₀ h₁) ≫
        (H).map (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P').hom) := by
        simp only [Category.assoc]
    _ = _ := by rw [hE]

end HomotopicalAlgebra.OriginalOrdinaryJLoopFunctor

namespace HomotopicalAlgebra.OriginalOrdinaryJLoopFunctor

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  (Z : C) (hZ : IsZero Z)

/-- The zero morphisms of the original source category. -/
local instance sourceZeroMorphisms : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
local notation "H" => toHomotopyCategory C

/-- The original full R-path fibre map retains both actual original framing endpoint maps. -/
def originalPathMap (D : GeneratedFunctorialReplacements.Data (C := C)) {X Y : C} (f : X ⟶ Y) :
    DerivedSuspensionLoopAdjunction.originalPathFiber D X ⟶
      DerivedSuspensionLoopAdjunction.originalPathFiber D Y :=
  pullback.map (DerivedSuspensionLoopAdjunction.originalPathBoundary D X)
    (0 : (0 : C) ⟶ D.R.obj X ⨯ D.R.obj X)
    (DerivedSuspensionLoopAdjunction.originalPathBoundary D Y)
    (0 : (0 : C) ⟶ D.R.obj Y ⨯ D.R.obj Y)
    (((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌)) (𝟙 (0 : C))
    (prod.map (D.R.map f) (D.R.map f))
    (OriginalGoodPathFiberGeometry.pathMap_pair_condition
      (PointedFramingAction.rightPath D X) (PointedFramingAction.rightPath D Y) (D.R.map f)
      (((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌))
      (PointedFramingAction.rightPath_p₀_naturality D f)
      (PointedFramingAction.rightPath_p₁_naturality D f)).symm (by simp)

/-- The full original path-fibre map retains its actual original frame-degree-one map. -/
@[reassoc (attr := simp)]
theorem originalPathMap_projection (D : GeneratedFunctorialReplacements.Data (C := C))
    {X Y : C} (f : X ⟶ Y) :
    originalPathMap D f ≫ DerivedSuspensionLoopAdjunction.originalPathProjection D Y =
      DerivedSuspensionLoopAdjunction.originalPathProjection D X ≫
        ((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌) :=
  pullback.lift_fst _ _ _

/-- The complete caller-zero path-fibre map retains the actual full original framing map. -/
def callerPathMap (D : GeneratedFunctorialReplacements.Data (C := C)) {X Y : C} (f : X ⟶ Y) :
    OriginalGoodPathFiberGeometry.pathFiber Z hZ (PointedFramingAction.rightPath D X) ⟶
      OriginalGoodPathFiberGeometry.pathFiber Z hZ (PointedFramingAction.rightPath D Y) :=
  OriginalGoodPathFiberGeometry.pathFiberMap Z hZ
    (PointedFramingAction.rightPath D X) (PointedFramingAction.rightPath D Y) (D.R.map f)
    (((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌))
    (PointedFramingAction.rightPath_p₀_naturality D f)
    (PointedFramingAction.rightPath_p₁_naturality D f)

/-- The caller's actual zero isomorphism preserves every original full framing path map. -/
theorem framePathFiberIsoOriginal_naturality (D : GeneratedFunctorialReplacements.Data (C := C))
    {X Y : C} (f : X ⟶ Y) :
    callerPathMap Z hZ D f ≫ (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y).hom =
      (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X).hom ≫ originalPathMap D f := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change callerPathMap Z hZ D f ≫
        (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y).hom ≫
          DerivedSuspensionLoopAdjunction.originalPathProjection D Y =
      (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X).hom ≫
        originalPathMap D f ≫ DerivedSuspensionLoopAdjunction.originalPathProjection D Y
    rw [OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal_fst, originalPathMap_projection,
      ← Category.assoc]
    rw [show callerPathMap Z hZ D f ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌)
      from pullback.lift_fst _ _ _]
    rw [← OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal_fst, Category.assoc]
  · exact (isZero_zero C).isTerminal.hom_ext _ _

/-- The original frame-degree-zero identification is natural on every full original framing path map. -/
theorem originalPathIso_naturality (D : GeneratedFunctorialReplacements.Data (C := C))
    {X Y : C} (f : X ⟶ Y) :
    DerivedSuspensionLoopAdjunction.pathMap ((PointedFramingAction.rightFrame D).map f) ≫
        (DerivedSuspensionLoopAdjunction.originalPathIso D Y).hom =
      (DerivedSuspensionLoopAdjunction.originalPathIso D X).hom ≫ originalPathMap D f := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change DerivedSuspensionLoopAdjunction.pathMap ((PointedFramingAction.rightFrame D).map f) ≫
        (DerivedSuspensionLoopAdjunction.originalPathIso D Y).hom ≫
          DerivedSuspensionLoopAdjunction.originalPathProjection D Y =
      (DerivedSuspensionLoopAdjunction.originalPathIso D X).hom ≫
        originalPathMap D f ≫ DerivedSuspensionLoopAdjunction.originalPathProjection D Y
    rw [DerivedSuspensionLoopAdjunction.originalPathIso_projection, originalPathMap_projection]
    simp only [PointedFramingAction.rightPath_P, eqToIso_refl, Iso.refl_inv, Category.comp_id]
    rw [← Category.assoc, DerivedSuspensionLoopAdjunction.pathMap_projection,
      DerivedSuspensionLoopAdjunction.originalPathIso_projection]
    simp only [PointedFramingAction.rightPath_P, eqToIso_refl, Iso.refl_inv, Category.comp_id]
  · exact (isZero_zero C).isTerminal.hom_ext _ _

variable [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]

/-- The entire original circle/path Ho comparison is natural on every original source arrow. -/
theorem loopsPathIso_naturality (D : GeneratedFunctorialReplacements.Data (C := C))
    {X Y : C} (f : X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.loops D).map ((H).map f) ≫
        (DerivedSuspensionLoopAdjunction.loopsPathIso D Y).hom =
      (DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫ (H).map (originalPathMap D f) := by
  rw [DerivedSuspensionLoopAdjunction.loopsPathIso_hom,
    DerivedSuspensionLoopAdjunction.loopsPathIso_hom]
  change (PointedFramingAction.cotensorHo D DerivedSuspensionLoopAdjunction.circle).map ((H).map f) ≫ _ = _
  rw [PointedFramingAction.cotensorHo_map, ← (H).map_comp, ← (H).map_comp]
  apply (H).congr_map
  rw [← Category.assoc, ← DerivedSuspensionLoopAdjunction.pathCotensorIso_naturality,
    Category.assoc, originalPathIso_naturality]; simp only [Category.assoc]

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

/-- The full original J-loop comparison is natural on every original input arrow after the SAME original R replacement.
-/
theorem loopsIsoJ_naturality {X Y : C} (f : X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).map ((H).map f) ≫
        (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g Y).hom =
      (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g X).hom ≫
        (H).map ((loopFunctor g Z hZ).map ((GeneratedFunctorialReplacements.fromGeneration g).R.map f)) := by
  let D := GeneratedFunctorialReplacements.fromGeneration g
  let : IsFibrant (D.R.obj X) := D.r_fibrant X
  let : IsFibrant (D.R.obj Y) := D.r_fibrant Y
  have hZero := congrArg (fun q => (H).map q) (framePathFiberIsoOriginal_naturality Z hZ D f)
  simp only [Functor.map_comp] at hZero
  change (H).map (callerPathMap Z hZ D f) ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).hom =
    ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).hom ≫
      (H).map (originalPathMap D f) at hZero
  have hJ := loopHoIsoPathFiber_naturality g Z hZ
    (PointedFramingAction.rightPath D X) (PointedFramingAction.rightPath D Y) (D.R.map f)
    (((PointedFramingAction.rightFrame D).map f).app (op ⦋1⦌))
    (PointedFramingAction.rightPath_p₀_naturality D f)
    (PointedFramingAction.rightPath_p₁_naturality D f)
  have hZeroInv :
      (H).map (originalPathMap D f) ≫
          ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv =
        ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).inv ≫
          (H).map (callerPathMap Z hZ D f) := by
    apply (cancel_epi ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
      congrArg (fun q => q ≫ ((H).mapIso
        (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv) hZero.symm
  have hJInv :
      (H).map (callerPathMap Z hZ D f) ≫
          (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv =
        (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D X)).inv ≫
          (H).map ((loopFunctor g Z hZ).map (D.R.map f)) := by
    apply (cancel_epi
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D X)).hom).mp
    simpa only [callerPathMap, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
      congrArg (fun q => q ≫ (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ
        (PointedFramingAction.rightPath D Y)).inv) hJ.symm
  simp only [OriginalOrdinaryJLoopComparison.loopsIsoJ, Iso.trans_hom, Iso.symm_hom]
  change (DerivedSuspensionLoopAdjunction.loops D).map ((H).map f) ≫
      (DerivedSuspensionLoopAdjunction.loopsPathIso D Y).hom ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv =
    ((DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).inv ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D X)).inv) ≫
        (H).map ((loopFunctor g Z hZ).map (D.R.map f))
  calc
    _ = ((DerivedSuspensionLoopAdjunction.loops D).map ((H).map f) ≫
        (DerivedSuspensionLoopAdjunction.loopsPathIso D Y).hom) ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv := by
        simp only [Category.assoc]
    _ = ((DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫ (H).map (originalPathMap D f)) ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv := by
        rw [loopsPathIso_naturality]
    _ = (DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫
      ((H).map (originalPathMap D f) ≫
        ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D Y)).inv) ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv := by
        simp only [Category.assoc]
    _ = (DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫
      (((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).inv ≫
        (H).map (callerPathMap Z hZ D f)) ≫
      (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv := by
        rw [hZeroInv]
    _ = (DerivedSuspensionLoopAdjunction.loopsPathIso D X).hom ≫
      ((H).mapIso (OriginalOrdinaryJLoopComparison.framePathFiberIsoOriginal Z hZ D X)).inv ≫
      ((H).map (callerPathMap Z hZ D f) ≫
        (OriginalOrdinaryJLoopComparison.loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).inv) := by
        simp only [Category.assoc]
    _ = _ := by rw [hJInv]; simp only [Category.assoc]

/-- The complete original point-set J loop functor after the same actual original R replacement. -/
def afterR : C ⥤ C :=
  (GeneratedFunctorialReplacements.fromGeneration g).R ⋙ loopFunctor g Z hZ

/-- The whole original point-set loop comparison before localization is a natural isomorphism. -/
def originalIso :
    (H) ⋙ DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g) ≅
      afterR Z hZ g ⋙ (H) :=
  NatIso.ofComponents (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g)
    (fun {_ _} f => loopsIsoJ_naturality Z hZ g f)

/-- The complete original J-loop-after-R functor preserves every original weak equivalence by its earned natural
comparison. -/
theorem afterR_map_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((afterR Z hZ g).map f) := by
  let : IsIso ((H).map f) := Localization.inverts (H) (weakEquivalences C) f hf
  let L := DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)
  let e := originalIso Z hZ g
  have h : (H).map ((afterR Z hZ g).map f) =
      (e.app X).inv ≫ L.map ((H).map f) ≫ (e.app Y).hom := by
    have hn := e.hom.naturality f
    change L.map ((H).map f) ≫ (e.app Y).hom =
      (e.app X).hom ≫ (H).map ((afterR Z hZ g).map f) at hn
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      (congrArg (fun q => (e.app X).inv ≫ q) hn).symm
  apply (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mpr
  rw [h]
  infer_instance

/-- The actual full original J-loop functor descends through the same original weak-equivalence localization. -/
def hoFunctor : HomotopyCategory C ⥤ HomotopyCategory C :=
  Localization.Construction.lift (afterR Z hZ g ⋙ (H))
    (fun {_ _} f hf => Localization.inverts (H) (weakEquivalences C)
      ((afterR Z hZ g).map f) (afterR_map_weak Z hZ g f hf))

/-- The whole descent retains the entire original J-loop-after-R object and map functor. -/
theorem hoFunctor_projection : (H) ⋙ hoFunctor Z hZ g = afterR Z hZ g ⋙ (H) :=
  Localization.Construction.fac _ _

/-- Every original map retains its actual original J-loop-after-R image. -/
theorem hoFunctor_map {X Y : C} (f : X ⟶ Y) :
    (hoFunctor Z hZ g).map ((H).map f) = (H).map ((afterR Z hZ g).map f) :=
  Functor.congr_hom (hoFunctor_projection Z hZ g) f

/-- The original localization lift of the specified source functor. -/
local instance hoFunctorLifting :
    Localization.Lifting (H) (weakEquivalences C) (afterR Z hZ g ⋙ (H)) (hoFunctor Z hZ g) :=
  ⟨eqToIso (hoFunctor_projection Z hZ g)⟩

/-- The complete actual J loop descent is naturally isomorphic to derived ordinary loops on ALL Ho objects and arrows.
-/
def hoIso :
    DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g) ≅ hoFunctor Z hZ g := by
  let L := DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)
  letI : Localization.Lifting (H) (weakEquivalences C) ((H) ⋙ L) L := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (H) (weakEquivalences C) ((H) ⋙ L)
    (afterR Z hZ g ⋙ (H)) L (hoFunctor Z hZ g) (originalIso Z hZ g)

/-- Every original Ho object retains the same entire original loop-comparison word. -/
theorem hoIso_hom_original (X : C) :
    (hoIso Z hZ g).hom.app ((H).obj X) = (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g X).hom := by
  let L := DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)
  let : Localization.Lifting (H) (weakEquivalences C) ((H) ⋙ L) L := ⟨Iso.refl _⟩
  unfold hoIso
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g X).hom ≫ 𝟙 _ = _
  simp

/-- The full original J-loop descent is right adjoint to the actual derived ordinary suspension. -/
def adjunction :
    DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g) ⊣
      hoFunctor Z hZ g :=
  (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).ofNatIsoRight
    (hoIso Z hZ g)

/-- The whole original ordinary/J-loop Hom function retains its original ordinary Hom function and the earned loop Iso.
-/
theorem homEquiv_apply {X Y : HomotopyCategory C}
    (f : (DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).obj X ⟶ Y) :
    (adjunction Z hZ g).homEquiv X Y f =
      (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv X Y f ≫
        (hoIso Z hZ g).hom.app Y :=
  Adjunction.homEquiv_ofNatIsoRight_apply _ _ _

/-- The entire inverse Hom function retains the same original ordinary inverse and the earned loop Iso inverse. -/
theorem homEquiv_symm_apply {X Y : HomotopyCategory C} (f : X ⟶ (hoFunctor Z hZ g).obj Y) :
    ((adjunction Z hZ g).homEquiv X Y).symm f =
      ((DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv X
        Y).symm
        (f ≫ (hoIso Z hZ g).inv.app Y) :=
  Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ _

/-- The complete original ordinary unit retains its actual derived comparison into the original J loop descent. -/
theorem unit_app (X : HomotopyCategory C) :
    (adjunction Z hZ g).unit.app X =
      (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).unit.app X ≫
        (hoIso Z hZ g).hom.app
          ((DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).obj X) := rfl

/-- The complete original ordinary counit retains the inverse comparison from the original J loop descent. -/
theorem counit_app (Y : HomotopyCategory C) :
    (adjunction Z hZ g).counit.app Y =
      (DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).map
        ((hoIso Z hZ g).inv.app Y) ≫
          (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).counit.app Y
            := rfl

end HomotopicalAlgebra.OriginalOrdinaryJLoopFunctor
