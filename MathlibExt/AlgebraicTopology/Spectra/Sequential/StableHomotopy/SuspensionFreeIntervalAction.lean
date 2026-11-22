/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionCoefficientGeometry

/-!
# Ordinary based homotopies from original freely pointed interval actions

The actual free-point adjunction and the actual based internal Hom convert a
pointed smash action into an ordinary native interval action. Both endpoint
composites and the entire selected basepoint are retained. The arbitrary
pointed source and target carry no added regularity hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped MonoidalClosed CGWH.limits unitInterval

namespace PointedCGWH.SuspensionFreeIntervalGeometry

open CategoryTheory.MonoidalClosed.NativeEvaluationInterchange
open PointedCGWH.SuspensionCoefficientGeometry

/-- The original free-point functor applied to the complete native time object. -/
abbrev freePointed (D : CGWH.{u, v}) : PointedCGWH.{u, v} :=
  (Under.costar CGWH.point).obj D

/-- The actual free adjunction includes every original time point in the free summand. -/
def freeUnit (D : CGWH.{u, v}) : D ⟶ (freePointed D).right :=
  (Under.costarAdjForget CGWH.point).unit.app D

/-- The original free unit retains the complete naturality square on every time map. -/
theorem freeUnit_naturality {D E : CGWH.{u, v}} (i : D ⟶ E) :
    i ≫ freeUnit E = freeUnit D ≫ ((Under.costar CGWH.point).map i).right :=
  (Under.costarAdjForget CGWH.point).unit.naturality i

/-- The actual free point is the original coproduct's entire free summand. -/
theorem freeUnit_point :
    freeUnit CGWH.point.{u, v} =
      (coprod.inr : CGWH.point ⟶ (𝟙_ PointedCGWH).right) := by
  unfold freeUnit Under.costarAdjForget
  rw [Adjunction.comp_unit_app, Monad.adj_unit,
    Equivalence.toAdjunction_unit, coprodMonad_η_app]
  dsimp [algebraEquivUnder, Monad.forget, Monad.Algebra.isoMk]
  rfl

/-- Forgetting the based condition retains the actual raw native internal-Hom carrier. -/
def basedCarrier (K Y : PointedCGWH.{u, v}) :
    ((ihom K).obj Y).right ⟶ (ihom K.right).obj Y.right :=
  (CategoryTheory.Pointed.basedInternalHomToInternalHom
    CGWH.point CGWH.point_isTerminal K).app Y

/-- The actual selected based-Hom point is the entire constant target-basepoint map. -/
theorem basedCarrier_basepoint (K Y : PointedCGWH.{u, v}) :
    ((ihom K).obj Y).hom ≫ basedCarrier K Y =
      MonoidalClosed.curry (CartesianMonoidalCategory.snd K.right CGWH.point ≫ Y.hom) := by
  change pullback.lift (CategoryTheory.Pointed.constantMap CGWH.point K Y) (𝟙 _) _ ≫
    pullback.fst (CategoryTheory.Pointed.evaluationAtBasepoint
      CGWH.point CGWH.point_isTerminal K Y) Y.hom = _
  rw [pullback.lift_fst]
  rfl

/-- The original chosen tensor unit maps to the named native point by its terminal map. -/
def unitPoint : (𝟙_ CGWH.{u, v}) ⟶ CGWH.point :=
  CGWH.point_isTerminal.from _

private theorem terminalUnitPointMap :
    (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
      CGWH.point_isTerminal).hom = unitPoint.{u, v} :=
  CGWH.point_isTerminal.hom_ext _ _

/-- The free time evaluation is the entire original pointed unit-point evaluation. -/
theorem freeTimeEvaluation_carrier (D : CGWH.{u, v}) (Y : PointedCGWH.{u, v})
    (i : CGWH.point ⟶ D) :
    basedCarrier (freePointed D) Y ≫ (MonoidalClosed.pre (freeUnit D)).app Y.right ≫
        pointEvaluation D Y.right (unitPoint ≫ i) =
      (pointEvaluation (freePointed D) Y ((Under.costar CGWH.point).map i)).right := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  have hp : (MonoidalClosed.pre (freeUnit D)).app Y.right ≫
      pointEvaluation D Y.right (unitPoint ≫ i) =
      pointEvaluation (freePointed D).right Y.right ((unitPoint ≫ i) ≫ freeUnit D) := by
    unfold pointEvaluation
    have h := congr_app (MonoidalClosed.pre_map (unitPoint ≫ i) (freeUnit D)) Y.right
    simpa only [NatTrans.comp_app, Category.assoc] using
      congrArg (fun f => f ≫ (MonoidalClosed.unitIsoSelf (X := Y.right)).hom) h.symm
  have hu := CategoryTheory.Pointed.basedInternalHom_pre_unit_carrier
    CGWH.point CGWH.point_isTerminal (freePointed D) Y ((Under.costar CGWH.point).map i)
  change (pointEvaluation (freePointed D) Y ((Under.costar CGWH.point).map i)).right =
    basedCarrier (freePointed D) Y ≫
      (λ_ ((ihom (freePointed D).right).obj Y.right)).inv ≫
      ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
        CGWH.point_isTerminal).hom ▷ ((ihom (freePointed D).right).obj Y.right)) ≫
      ((coprod.inr ≫ ((Under.costar CGWH.point).map i).right) ▷
        ((ihom (freePointed D).right).obj Y.right)) ≫
      (ihom.ev (freePointed D).right).app Y.right at hu
  rw [terminalUnitPointMap, ← freeUnit_point, ← freeUnit_naturality,
    ← comp_whiskerRight_assoc] at hu
  have he := pointEvaluation_comp (freePointed D).right Y.right ((unitPoint ≫ i) ≫ freeUnit D)
    (𝟙 ((ihom (freePointed D).right).obj Y.right))
  rw [Category.id_comp, MonoidalClosed.uncurry_id_eq_ev] at he
  calc
    _ = basedCarrier (freePointed D) Y ≫
        pointEvaluation (freePointed D).right Y.right ((unitPoint ≫ i) ≫ freeUnit D) :=
      congrArg (fun f => basedCarrier (freePointed D) Y ≫ f) hp
    _ = _ := by
      rw [he]
      simpa only [Category.assoc] using hu.symm

/-- Restrict the entire pointed time transpose to the original free time summand. -/
def freeTimePath {D : CGWH.{u, v}} {X Y : PointedCGWH.{u, v}}
    (H : freePointed D ⊗ X ⟶ Y) : X.right ⟶ (ihom D).obj Y.right :=
  (MonoidalClosed.curry H).right ≫ basedCarrier (freePointed D) Y ≫
    (MonoidalClosed.pre (freeUnit D)).app Y.right

/-- The actual ordinary native time action is the full original restricted uncurry map. -/
def freeTimeAction {D : CGWH.{u, v}} {X Y : PointedCGWH.{u, v}}
    (H : freePointed D ⊗ X ⟶ Y) : D ⊗ X.right ⟶ Y.right :=
  MonoidalClosed.uncurry (freeTimePath H)

/-- Every original time endpoint retains the complete pointed smash endpoint composite. -/
theorem freeTimeAction_endpoint {D : CGWH.{u, v}} {X Y : PointedCGWH.{u, v}}
    (H : freePointed D ⊗ X ⟶ Y) (i : CGWH.point ⟶ D) :
    (λ_ X.right).inv ≫ (unitPoint ≫ i) ▷ X.right ≫ freeTimeAction H =
      ((λ_ X).inv ≫ ((Under.costar CGWH.point).map i) ▷ X ≫ H).right := by
  have hp := pointEvaluation_comp (freePointed D) Y ((Under.costar CGWH.point).map i)
    (MonoidalClosed.curry H)
  rw [MonoidalClosed.uncurry_curry] at hp
  have hr := pointEvaluation_comp D Y.right (unitPoint ≫ i) (freeTimePath H)
  calc
    _ = freeTimePath H ≫ pointEvaluation D Y.right (unitPoint ≫ i) := hr.symm
    _ = (MonoidalClosed.curry H).right ≫
        (pointEvaluation (freePointed D) Y ((Under.costar CGWH.point).map i)).right := by
      have he := congrArg (fun f => (MonoidalClosed.curry H).right ≫ f)
        (freeTimeEvaluation_carrier D Y i)
      simpa only [freeTimePath, Category.assoc] using he
    _ = _ := congrArg (fun f => f.right) hp

/-- The full restricted time transpose keeps the entire selected source point constant. -/
theorem freeTimePath_basepoint {D : CGWH.{u, v}} {X Y : PointedCGWH.{u, v}}
    (H : freePointed D ⊗ X ⟶ Y) :
    X.hom ≫ freeTimePath H =
      MonoidalClosed.curry (CartesianMonoidalCategory.snd D CGWH.point ≫ Y.hom) := by
  rw [freeTimePath, ← Category.assoc, Under.w (MonoidalClosed.curry H)]
  rw [← Category.assoc, basedCarrier_basepoint, MonoidalClosed.curry_pre_app]
  rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_snd]

/-- Every time in the actual native action fixes the whole original selected basepoint. -/
theorem freeTimeAction_basepoint {D : CGWH.{u, v}} {X Y : PointedCGWH.{u, v}}
    (H : freePointed D ⊗ X ⟶ Y) :
    D ◁ X.hom ≫ freeTimeAction H =
      CartesianMonoidalCategory.snd D CGWH.point ≫ Y.hom := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_left, freeTimeAction, MonoidalClosed.curry_uncurry]
  exact freeTimePath_basepoint H

private theorem basepoint_range (X : PointedCGWH.{u, v}) :
    Set.range (ConcreteCategory.hom (C := CGWH.{u, v}) X.hom) = {underlyingBasepoint X} := by
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, rfl⟩
    change X.hom p = X.hom PUnit.unit
    have hp : p = PUnit.unit := by
      change PUnit.{v + 1} at p
      cases p
      rfl
    exact congrArg X.hom hp
  · rintro rfl
    exact ⟨PUnit.unit, rfl⟩

/-- The freely pointed interval action gives an ordinary homotopy relative its basepoint. -/
def freeIntervalHomotopyRel {X Y : PointedCGWH.{u, v}} (f₀ f₁ : X ⟶ Y)
    (H : freePointed CGWH.interval ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫ ((Under.costar CGWH.point).map CGWH.intervalZero) ▷ X ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫ ((Under.costar CGWH.point).map CGWH.intervalOne) ▷ X ≫ H = f₁) :
    ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right) {underlyingBasepoint X} := by
  have ha₀ := (freeTimeAction_endpoint H CGWH.intervalZero).trans
    (congrArg (fun f => f.right) h₀)
  have ha₁ := (freeTimeAction_endpoint H CGWH.intervalOne).trans
    (congrArg (fun f => f.right) h₁)
  have hfix : (𝟙 CGWH.interval ⊗ₘ X.hom) ≫ freeTimeAction H =
      (CartesianMonoidalCategory.toUnit CGWH.interval ⊗ₘ 𝟙 CGWH.point) ≫
        (λ_ CGWH.point).hom ≫ Y.hom := by
    simpa only [id_tensorHom, tensorHom_id,
      CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom_assoc] using
      freeTimeAction_basepoint H
  have h := CGWH.intervalActionHomotopyRel f₀.right f₁.right (freeTimeAction H)
    ha₀ ha₁ X.hom Y.hom hfix
  simpa only [basepoint_range] using h

/-- The complete native interval coordinate sends the original zero point to zero. -/
theorem nativeIntervalHomeo_zero :
    nativeIntervalHomeo.{u, v} (CGWH.intervalZero.{u, v} PUnit.unit) = 0 := by
  have h := ConcreteCategory.congr_hom (C := TopCat.{v})
    CGWH.intervalToTopIso_zero.{u, v} PUnit.unit
  change CGWH.intervalToTopIso.{u, v}.hom (CGWH.intervalZero.{u, v} PUnit.unit) = 0 at h
  change TopCat.I.homeomorph.{v}
    (CGWH.intervalToTopIso.{u, v}.hom (CGWH.intervalZero.{u, v} PUnit.unit)) = 0
  rw [h]
  simp

/-- The complete native interval coordinate sends the original one point to one. -/
theorem nativeIntervalHomeo_one :
    nativeIntervalHomeo.{u, v} (CGWH.intervalOne.{u, v} PUnit.unit) = 1 := by
  have h := ConcreteCategory.congr_hom (C := TopCat.{v})
    CGWH.intervalToTopIso_one.{u, v} PUnit.unit
  change CGWH.intervalToTopIso.{u, v}.hom (CGWH.intervalOne.{u, v} PUnit.unit) = 1 at h
  change TopCat.I.homeomorph.{v}
    (CGWH.intervalToTopIso.{u, v}.hom (CGWH.intervalOne.{u, v} PUnit.unit)) = 1
  rw [h]
  simp

/-- The actual two-circle coefficient family uses the original interval and twice-curried
identity. -/
def coefficientPointedFamily : freePointed CGWH.interval.{u, v} ⟶
    PointedCGWH.loop.obj (PointedCGWH.loop.obj
      (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)) :=
  pointedTurnFamily (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v}) CGWH.interval.{u, v}
    (intervalPairHomeo CGWH.interval.{u, v} nativeIntervalHomeo.{u, v}) nativeIntervalHomeo.{u, v}
    (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) (doubleIdentityLoop PointedCGWH.sphereOne)

/-- The whole original zero endpoint is the complete reflected identity family. -/
theorem coefficientPointedFamily_zero :
    (Under.costar CGWH.point).map CGWH.intervalZero ≫ coefficientPointedFamily.{u, v} =
      doubleIdentityLoop PointedCGWH.sphereOne ≫ PointedCGWH.loop.map
        (loopReflection (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)) :=
  pointedTurnFamily_zero _ _ _ _ _ _ _ nativeIntervalHomeo_zero.{u, v}

/-- The whole original one endpoint is the complete interchanged identity family. -/
theorem coefficientPointedFamily_one :
    (Under.costar CGWH.point).map CGWH.intervalOne ≫ coefficientPointedFamily.{u, v} =
      doubleIdentityLoop PointedCGWH.sphereOne ≫
        PointedCGWH.DoubleLoopInterchangeGeometry.interchange
          (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) :=
  pointedTurnFamily_one _ _ _ _ _ _ _ nativeIntervalHomeo_one.{u, v}

/-- The actual original interval action on the entire two-circle pointed coefficient. -/
def coefficientPointedAction :
    freePointed CGWH.interval.{u, v} ⊗ (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) ⟶
      PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne :=
  doubleTransposeAction _ _ coefficientPointedFamily

/-- The full original zero action is reflection of the first circle coefficient. -/
theorem coefficientPointedAction_zero :
    (λ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      ((Under.costar CGWH.point).map CGWH.intervalZero) ▷
        (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) ≫ coefficientPointedAction =
      circleReflection ▷ PointedCGWH.sphereOne := by
  rw [coefficientPointedAction, doubleTransposeAction_endpoint, coefficientPointedFamily_zero]
  exact doubleIdentityLoop_reflection

/-- The full original one action is the actual inverse coefficient braiding. -/
theorem coefficientPointedAction_one :
    (λ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      ((Under.costar CGWH.point).map CGWH.intervalOne) ▷
        (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) ≫ coefficientPointedAction =
      (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv := by
  rw [coefficientPointedAction, doubleTransposeAction_endpoint, coefficientPointedFamily_one]
  exact doubleIdentityLoop_interchange

/-- The actual coefficient interchange is ordinarily based-homotopic to first-circle reflection. -/
def coefficientHomotopy : ContinuousMap.HomotopyRel
    (ConcreteCategory.hom (C := CGWH.{u, v})
      (circleReflection.{u, v} ▷ PointedCGWH.sphereOne).right)
    (ConcreteCategory.hom (C := CGWH.{u, v})
      (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv.right)
    {underlyingBasepoint (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)} :=
  freeIntervalHomotopyRel _ _ coefficientPointedAction
    coefficientPointedAction_zero coefficientPointedAction_one

end PointedCGWH.SuspensionFreeIntervalGeometry
