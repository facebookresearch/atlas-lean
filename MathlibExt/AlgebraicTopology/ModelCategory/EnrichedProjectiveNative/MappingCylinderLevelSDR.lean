/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderDeformation
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHFreeIntervalHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHSDRPushout

/-!
# Actual original mapping-cylinder level SDR and same original level weak maps

Every actual original native MC time action is evaluated at every original
index. Its original endpoint and fixed-target equations are proved from
the whole native action before ordinary landing. The exact existing native
free-point interval/source quotient and path landing then produce an ordinary
SDR, with the SAME original retraction and target section. All original
MC retractions and recursive telescope stage projections are level weak in
the SAME original caller-B projective model. No source cofibrancy, SDR,
weakness or stable-model law is an input.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedIntervalContraction
open PointedCGWH.EnrichedIntervalMappingCylinder
open scoped MonoidalClosed CGWH.modelCategory

namespace CGWH.StrictRetraction

/--
A genuine strict retraction and actual ordinary homotopy give the complete ordinary homotopy-
equivalence data before native MC fields.
-/
private def homotopyEquiv {A B : CGWH.{u, v}} (r : A ⟶ B) (s : B ⟶ A)
    (h : s ≫ r = 𝟙 B)
    (H : ContinuousMap.Homotopy (ContinuousMap.id A)
      ((ConcreteCategory.hom (C := CGWH.{u, v}) s).comp
        (ConcreteCategory.hom (C := CGWH.{u, v}) r))) :
    ContinuousMap.HomotopyEquiv A B where
  toFun := ConcreteCategory.hom (C := CGWH.{u, v}) r
  invFun := ConcreteCategory.hom (C := CGWH.{u, v}) s
  left_inv := ⟨H.symm⟩
  right_inv := by
    have hComp : (ConcreteCategory.hom (C := CGWH.{u, v}) r).comp
        (ConcreteCategory.hom (C := CGWH.{u, v}) s) = ContinuousMap.id B := by
      apply ContinuousMap.ext
      intro x
      exact ConcreteCategory.congr_hom h x
    rw [hComp]

/-- The SAME original generic retraction function is a native CGWH weak homotopy equivalence. -/
private theorem mem_weakHomotopyEquivalences {A B : CGWH.{u, v}} (r : A ⟶ B) (s : B ⟶ A)
    (h : s ≫ r = 𝟙 B)
    (H : ContinuousMap.Homotopy (ContinuousMap.id A)
      ((ConcreteCategory.hom (C := CGWH.{u, v}) s).comp
        (ConcreteCategory.hom (C := CGWH.{u, v}) r))) :
    CGWH.weakHomotopyEquivalences r := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage]
  change TopCat.weakHomotopyEquivalences (TopCat.ofHom (homotopyEquiv r s h H).toFun)
  exact TopCat.homotopyEquiv_toFun_mem (homotopyEquiv r s h H)

end CGWH.StrictRetraction

namespace PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- Evaluate the actual original full native time action at its SAME original index. -/
def componentTimeAction {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (H : timeObject X ⟶ Y) (a : I) :
    PointedCGWH.RealizedIntervalContraction.time.{u, v} ⊗ X.toEnrichedFunctor.obj a ⟶
      Y.toEnrichedFunctor.obj a := by
  simpa only [timeObject, tensorLeftObject_obj, EnrichedFunctor.tensorLeft_obj] using component H a

/--
The actual component time endpoint retains the SAME complete original native composition
before MC evaluation.
-/
theorem componentTimeAction_endpoint {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (H : timeObject X ⟶ Y) (t : unitInterval) (a : I) :
    (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
        (PointedCGWH.freePointIntervalEndpoint.{u, v} t ⊗ₘ 𝟙 _) ≫ componentTimeAction H a =
      component (timeInclusion t X ≫ H) a := by
  rw [component_comp, timeInclusion_component]
  simp only [componentTimeAction, tensorHom_id]
  exact (Category.assoc _ _ _).symm

/-- The actual original point at every MC level is retained. -/
abbrev levelObject (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    PointedCGWH.{u, v} := (object f).toEnrichedFunctor.obj a

/-- Every original level retraction is the SAME full native retraction component. -/
def levelRetraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    levelObject f a ⟶ f.right.toEnrichedFunctor.obj a := component (retraction f) a

/-- Every original target level section is the SAME full native target-leg component. -/
def levelSection (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    f.right.toEnrichedFunctor.obj a ⟶ levelObject f a := component (targetLeg f) a

/-- Every original level deformation is the SAME evaluated full native MC action. -/
def levelDeformation (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    PointedCGWH.RealizedIntervalContraction.time.{u, v} ⊗ levelObject f a ⟶ levelObject f a :=
  componentTimeAction (PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy f) a

/-- The full original target section is a strict retraction at every SAME original level. -/
theorem levelSection_retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    levelSection f a ≫ levelRetraction f a = 𝟙 (f.right.toEnrichedFunctor.obj a) := by
  have h := congrArg (fun g : f.right ⟶ f.right => component g a) (targetLeg_retraction f)
  rw [component_comp, component_id] at h
  exact h

/-- Time zero of every evaluated original MC action is the SAME original level identity. -/
theorem levelDeformation_zero (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    (λ_ (levelObject f a)).inv ≫ (PointedCGWH.freePointIntervalEndpoint.{u, v} 0 ⊗ₘ 𝟙 _) ≫
      levelDeformation f a = 𝟙 (levelObject f a) := by
  rw [levelDeformation, componentTimeAction_endpoint,
    PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy_zero, component_id]

/--
Time one of every original evaluated MC action is its SAME original level retraction followed
by its SAME original section.
-/
theorem levelDeformation_one (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    (λ_ (levelObject f a)).inv ≫ (PointedCGWH.freePointIntervalEndpoint.{u, v} 1 ⊗ₘ 𝟙 _) ≫
      levelDeformation f a = levelRetraction f a ≫ levelSection f a := by
  rw [levelDeformation, componentTimeAction_endpoint,
    PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy_one, component_comp]
  rfl

/--
The complete original target level section is fixed by the SAME original level action
throughout native time.
-/
theorem levelDeformation_fixed (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    (𝟙 PointedCGWH.RealizedIntervalContraction.time.{u, v} ⊗ₘ levelSection f a) ≫
        levelDeformation f a =
      (PointedCGWH.freePointIntervalCollapse.{u, v} ⊗ₘ 𝟙 _) ≫
        (λ_ (f.right.toEnrichedFunctor.obj a)).hom ≫ levelSection f a := by
  have h := congrArg (fun g : timeObject f.right ⟶ object f => component g a)
    (PointedCGWH.EnrichedIntervalMappingCylinderDeformation.timeTargetLeg_homotopy f)
  rw [component_comp, tensorLeftMap_component, component_comp, timeProjection_component] at h
  simpa only [levelObject, levelDeformation, componentTimeAction, levelSection, timeObject,
    tensorLeftObject_obj, EnrichedFunctor.tensorLeft_obj,
    id_tensorHom, tensorHom_id, Category.assoc] using h

/--
The SAME original level action and its proved endpoint data land as an ordinary jointly
continuous homotopy.
-/
def homotopy (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (levelObject f a).right)
      ((ConcreteCategory.hom (C := CGWH.{u, v}) (levelSection f a).right).comp
        (ConcreteCategory.hom (C := CGWH.{u, v}) (levelRetraction f a).right)) :=
  PointedCGWH.freePointIntervalActionHomotopy.{u, v}
    (𝟙 (levelObject f a)) (levelRetraction f a ≫ levelSection f a) (levelDeformation f a)
    (levelDeformation_zero f a) (levelDeformation_one f a)

/--
Every actual target level point is fixed at EVERY ordinary homotopy time under the SAME
original target section.
-/
theorem homotopy_fixed (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I)
    (t : unitInterval) (y : (f.right.toEnrichedFunctor.obj a).right) :
    homotopy f a (t, (levelSection f a).right y) = (levelSection f a).right y :=
  PointedCGWH.freePointIntervalActionHomotopy_fixed.{u, v}
    (𝟙 (levelObject f a)) (levelRetraction f a ≫ levelSection f a) (levelDeformation f a)
    (levelDeformation_zero f a) (levelDeformation_one f a)
    (levelSection f a) (levelSection f a) (levelDeformation_fixed f a) t y

/--
The SAME original MC level retraction and target section form an ordinary homotopy
equivalence, with no source cofibrancy.
-/
def homotopyEquiv (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    ContinuousMap.HomotopyEquiv (levelObject f a).right (f.right.toEnrichedFunctor.obj a).right
      :=
  CGWH.StrictRetraction.homotopyEquiv
    (levelRetraction f a).right (levelSection f a).right
    (congrArg (fun g : f.right.toEnrichedFunctor.obj a ⟶ f.right.toEnrichedFunctor.obj a => g.right)
      (levelSection_retraction f a)) (homotopy f a)

/-- The full forward ordinary homotopy-equivalence map is the SAME original retraction function. -/
theorem homotopyEquiv_toFun (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    (homotopyEquiv f a).toFun = ConcreteCategory.hom (C := CGWH.{u, v}) (levelRetraction f
      a).right := rfl

/--
The full inverse ordinary homotopy-equivalence map is the SAME original target-section
function.
-/
theorem homotopyEquiv_invFun (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    (homotopyEquiv f a).invFun = ConcreteCategory.hom (C := CGWH.{u, v}) (levelSection f
      a).right := rfl

/--
Every SAME original MC retraction component is weak in the actual selected native pointed
model, with arbitrary original sources.
-/
theorem levelRetraction_weakEquivalence
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    WeakEquivalence (levelRetraction f a) := by
  apply (PointedCGWH.weakEquivalence_iff _).mpr
  apply (CGWH.modelCategory.weakEquivalence_iff _).mpr
  exact CGWH.StrictRetraction.mem_weakHomotopyEquivalences
    (levelRetraction f a).right (levelSection f a).right
    (congrArg (fun g : f.right.toEnrichedFunctor.obj a ⟶ f.right.toEnrichedFunctor.obj a => g.right)
      (levelSection_retraction f a)) (homotopy f a)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/--
The SAME original full MC retraction is level weak in the actual original caller-B native
projective model, without source cofibrancy.
-/
theorem retraction_weakEquivalence (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    WeakEquivalence (retraction f) := by
  apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : I => evaluation a) (weakEquivalences PointedCGWH.{u, v}) _).mpr
  intro a
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp (levelRetraction_weakEquivalence f a)

end PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every full SAME original next-stage projection is level weak in the original caller-B model. -/
theorem nextStageProjection_weakEquivalence {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) : WeakEquivalence ((nextStage d).projection.app
      X) := by
  rw [nextStageProjection_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence _

/--
The actual next-stage level retraction has its SAME original ordinary level SDR and inverse
target section.
-/
def nextStageLevelHomotopyEquiv {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    ContinuousMap.HomotopyEquiv
      (PointedCGWH.SequentialSpectrum.level ((nextStage d).functor.obj X) m).right
      (PointedCGWH.SequentialSpectrum.level
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X) m).right :=
  PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.homotopyEquiv (stageArrows d |>.obj X) ⟨m⟩

omit B in
/--
Every complete actual next-stage level homotopy-equivalence function is the SAME original
projection level function.
-/
theorem nextStageLevelHomotopyEquiv_toFun {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    (nextStageLevelHomotopyEquiv d X m).toFun = ConcreteCategory.hom (C := CGWH.{u, v})
      (PointedCGWH.SequentialSpectrum.levelMap ((nextStage d).projection.app X) m).right := by
  rw [nextStageProjection_app]
  rfl

omit B in
/--
Every complete inverse actual next-stage level homotopy-equivalence function is the SAME
original target-section level function.
-/
theorem nextStageLevelHomotopyEquiv_invFun {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    (nextStageLevelHomotopyEquiv d X m).invFun = ConcreteCategory.hom (C := CGWH.{u, v})
      (PointedCGWH.SequentialSpectrum.levelMap ((nextStageSection d).app X) m).right := by
  rw [nextStageSection_app]
  rfl

/--
ALL original full stage projections are weak in the SAME original caller-B level model,
including the original identity stage.
-/
theorem projection_weakEquivalence (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    WeakEquivalence ((projection n).app X) := by
  cases n with
  | zero => change WeakEquivalence (𝟙 X); infer_instance
  | succ n => exact nextStageProjection_weakEquivalence (stage n) X

/--
Every actual original telescope successor has the SAME ordinary level homotopy equivalence and
original inverse section.
-/
def stageLevelHomotopyEquiv (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    ContinuousMap.HomotopyEquiv
      (PointedCGWH.SequentialSpectrum.level ((stage (n + 1)).functor.obj X) m).right
      (PointedCGWH.SequentialSpectrum.level
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X) m).right :=
  nextStageLevelHomotopyEquiv (stage n) X m

omit B in
/--
The full forward function at EVERY original stage and level is the actual original stage
projection level function.
-/
theorem stageLevelHomotopyEquiv_toFun (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    (stageLevelHomotopyEquiv n X m).toFun = ConcreteCategory.hom (C := CGWH.{u, v})
      (PointedCGWH.SequentialSpectrum.levelMap ((projection (n + 1)).app X) m).right :=
  nextStageLevelHomotopyEquiv_toFun (stage n) X m

omit B in
/--
The full inverse function at EVERY original stage and level is the actual original stage
target-section level function.
-/
theorem stageLevelHomotopyEquiv_invFun (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    (stageLevelHomotopyEquiv n X m).invFun = ConcreteCategory.hom (C := CGWH.{u, v})
      (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m).right :=
  nextStageLevelHomotopyEquiv_invFun (stage n) X m

end PointedCGWH.SequentialSpectrum.MappingTelescope
