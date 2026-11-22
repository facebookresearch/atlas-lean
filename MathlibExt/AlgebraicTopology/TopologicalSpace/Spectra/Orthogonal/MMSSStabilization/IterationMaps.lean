/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.Delooping
import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.LoopPowerAtPoints

/-!
# The original-input iteration of the native orthogonal shifted loop

The original native right shift and scalar loop give the evaluated functor
`X ↦ Ωⁿ X(m + n)`, with a comparison built from their actual component maps.
Both comparison maps retain the original index arithmetic transports. The
coaugmentation sequence uses the actual images of the original input delta;
it does not substitute delta at the iterated object.

This is an additive prerequisite for the function-spectrum identification in
MMSS Proposition 8.8. The function object, its original free-sphere source
map and the telescope homotopy calculation are separate results.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.IterationMaps

open FunctionSpectrum

/-- The unchanged continuous enriched orthogonal carrier. -/
abbrev Carrier := RightShift.Carrier.{u, v}

/-- Evaluation at the actual original operator index. -/
abbrev level (m : ℕ) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  evaluation (OrthogonalOperatorIndex.ofIndex.{u, v} m)

/-- The genuine first right shift followed by the original native scalar loop. -/
abbrev shiftedLoop : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Delooping.firstDeloopingLoop.{u, v}

/-- The complete original shifted-loop power, including all enriched arrows. -/
abbrev power (n : ℕ) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Functor.Iteration.iterate shiftedLoop n

/-- Its source comparison is the original delta on the original input. -/
abbrev inputTransition (n : ℕ) : power.{u, v} n ⟶ power (n + 1) :=
  Functor.Iteration.inputTransition Delooping.delta n

/-- The whole one-step evaluation uses the original right-shift and cotensor maps. -/
def stepEvaluation (m : ℕ) :
    shiftedLoop.{u, v} ⋙ level m ≅ level (m + 1) ⋙ PointedCGWH.loop :=
  NatIso.ofComponents
    (fun X => Iso.refl ((ihom PointedCGWH.sphereOne).obj
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1)))))
    (by
      intro X Y f
      change component (shiftedLoop.map f) (OrthogonalOperatorIndex.ofIndex.{u, v} m) ≫
          𝟙 _ = 𝟙 _ ≫ PointedCGWH.loop.map
            (component f (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1)))
      rw [Category.comp_id, Category.id_comp]
      exact (cotensorMap_component PointedCGWH.sphereOne _ _).trans
        (congrArg (ihom PointedCGWH.sphereOne).map
          (RightShift.shift_map_component 1 m f)))

/-- Both directions of the actual single-step comparison are the level identity. -/
theorem stepEvaluation_hom_app (m : ℕ) (X : Carrier.{u, v}) :
    (stepEvaluation m).hom.app X =
      𝟙 ((ihom PointedCGWH.sphereOne).obj
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1)))) := rfl

/-- The inverse retains the same complete original level identity. -/
theorem stepEvaluation_inv_app (m : ℕ) (X : Carrier.{u, v}) :
    (stepEvaluation m).inv.app X =
      𝟙 ((ihom PointedCGWH.sphereOne).obj
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1)))) := rfl

/-- Every evaluated iterate is compared with the actual native loop power at the shifted level. -/
def evaluationComparison (n : ℕ) : ∀ m : ℕ,
    power.{u, v} n ⋙ level m ≅ level (m + n) ⋙ LoopPowerAtPoints.power n :=
  Nat.rec
    (fun m => (level m).leftUnitor ≪≫ (level m).rightUnitor.symm)
    (fun n previous m =>
      Functor.associator (power n) shiftedLoop (level m) ≪≫
        Functor.isoWhiskerLeft (power n) (stepEvaluation m) ≪≫
        (Functor.associator (power n) (level (m + 1)) PointedCGWH.loop).symm ≪≫
        Functor.isoWhiskerRight (previous (m + 1)) PointedCGWH.loop ≪≫
        Functor.associator (level (m + 1 + n)) (LoopPowerAtPoints.power n)
          PointedCGWH.loop ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (fun k => level.{u, v} k)
            ((Nat.add_right_comm m 1 n).trans (Nat.add_assoc m n 1))))
          (LoopPowerAtPoints.power n ⋙ PointedCGWH.loop)) n

/-- The forward comparison is natural for every original spectrum arrow. -/
theorem evaluationComparison_hom_naturality (n m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (level m).map ((power n).map f) ≫ (evaluationComparison n m).hom.app Y =
      (evaluationComparison n m).hom.app X ≫
        (LoopPowerAtPoints.power n).map ((level (m + n)).map f) :=
  (evaluationComparison n m).hom.naturality f

/-- The inverse comparison is natural for the same whole original arrow. -/
theorem evaluationComparison_inv_naturality (n m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (LoopPowerAtPoints.power n).map ((level (m + n)).map f) ≫
        (evaluationComparison n m).inv.app Y =
      (evaluationComparison n m).inv.app X ≫ (level m).map ((power n).map f) :=
  (evaluationComparison n m).inv.naturality f

/-- The actual identity-component step identifies the complete evaluated functor. -/
theorem stepEvaluation_eq (m : ℕ) :
    shiftedLoop.{u, v} ⋙ level m = level (m + 1) ⋙ PointedCGWH.loop :=
  Functor.ext_of_iso (stepEvaluation m) (fun _ => rfl) (fun _ => rfl)

/-- The complete evaluated iterate has the same original objects and maps as the loop power. -/
theorem evaluation_eq (n m : ℕ) :
    power.{u, v} n ⋙ level m = level (m + n) ⋙ LoopPowerAtPoints.power n := by
  induction n generalizing m with
  | zero => rfl
  | succ n hn =>
    change (power n ⋙ shiftedLoop) ⋙ level m = _
    rw [Functor.assoc, stepEvaluation_eq,
      ← Functor.assoc, hn (m + 1), Functor.assoc]
    exact congrArg (fun k => level.{u, v} k ⋙ LoopPowerAtPoints.power (n + 1))
      ((Nat.add_right_comm m 1 n).trans (Nat.add_assoc m n 1))

/-- The actual first-step comparison is its whole-functor equality transport. -/
theorem stepEvaluation_eqToIso (m : ℕ) :
    stepEvaluation.{u, v} m = eqToIso (stepEvaluation_eq m) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change 𝟙 _ = (eqToHom (stepEvaluation_eq m)).app X
  exact (eqToHom_app (stepEvaluation_eq m) X).symm

private theorem eqIsoWhiskerLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : C ⥤ D) {F G : D ⥤ E} (h : F = G) :
    Functor.isoWhiskerLeft H (eqToIso h) =
      eqToIso (congrArg (fun K => H ⋙ K) h) := by
  cases h
  rfl

private theorem eqIsoWhiskerRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : D ⥤ E) {F G : C ⥤ D} (h : F = G) :
    Functor.isoWhiskerRight (eqToIso h) H =
      eqToIso (congrArg (fun K => K ⋙ H) h) := by
  cases h
  exact Functor.isoWhiskerRight_refl F H

private theorem eqIsoSymm {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm := rfl

private theorem associatorEqIso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : C ⥤ D) (Q : D ⥤ E) (R : E ⥤ F) :
    Functor.associator P Q R = eqToIso (Functor.assoc P Q R) := rfl

/-- Both constructed iteration maps are the transports of the same complete functor equality. -/
theorem evaluationComparison_eqToIso (n m : ℕ) :
    evaluationComparison.{u, v} n m = eqToIso (evaluation_eq n m) := by
  induction n generalizing m with
  | zero =>
    apply Iso.ext
    apply NatTrans.ext
    funext X
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  | succ n hn =>
    change Functor.associator (power n) shiftedLoop (level m) ≪≫
      Functor.isoWhiskerLeft (power n) (stepEvaluation m) ≪≫
      (Functor.associator (power n) (level (m + 1)) PointedCGWH.loop).symm ≪≫
      Functor.isoWhiskerRight (evaluationComparison n (m + 1)) PointedCGWH.loop ≪≫
      Functor.associator (level (m + 1 + n)) (LoopPowerAtPoints.power n)
        PointedCGWH.loop ≪≫
      Functor.isoWhiskerRight
        (eqToIso (congrArg (fun k => level.{u, v} k)
          ((Nat.add_right_comm m 1 n).trans (Nat.add_assoc m n 1))))
        (LoopPowerAtPoints.power n ⋙ PointedCGWH.loop) = _
    rw [hn (m + 1), stepEvaluation_eqToIso, eqIsoWhiskerLeft]
    simp only [associatorEqIso, eqIsoWhiskerRight, eqIsoSymm]
    rw [eqToIso_trans, eqToIso_trans, eqToIso_trans, eqToIso_trans, eqToIso_trans]
    rfl

/-- The actual prefix target retains the loop-power and level arithmetic transports. -/
def prefixEvaluation (n m : ℕ) :
    shiftedLoop.{u, v} ⋙ level (m + n) ⋙ LoopPowerAtPoints.power n ≅
      level (m + (n + 1)) ⋙ LoopPowerAtPoints.power (n + 1) :=
  eqToIso ((congrArg (fun H => H ⋙ LoopPowerAtPoints.power n)
      (stepEvaluation_eq (m + n))).trans
    ((congrArg (fun H => level (m + n + 1) ⋙ H)
      (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm).trans
        (congrArg (fun k => level k ⋙ LoopPowerAtPoints.power (n + 1))
          (Nat.add_assoc m n 1))))

/-- Both full original evaluation comparisons agree across the actual prefix reassociation. -/
theorem evaluationComparison_prefix (n m : ℕ) :
    Functor.isoWhiskerRight (Functor.Iteration.iteratePrefixIso shiftedLoop n).symm
        (level m) ≪≫ evaluationComparison (n + 1) m =
      Functor.isoWhiskerLeft shiftedLoop (evaluationComparison n m) ≪≫
        prefixEvaluation.{u, v} n m := by
  rw [evaluationComparison_eqToIso, evaluationComparison_eqToIso]
  change Functor.isoWhiskerRight
      (eqToIso (Functor.Iteration.iterate_succ_prefix shiftedLoop n).symm) (level m) ≪≫
      eqToIso (evaluation_eq (n + 1) m) =
    Functor.isoWhiskerLeft shiftedLoop (eqToIso (evaluation_eq n m)) ≪≫
      prefixEvaluation n m
  rw [eqIsoWhiskerRight, eqIsoWhiskerLeft, eqToIso_trans]
  unfold prefixEvaluation
  rw [eqToIso_trans]

/-- The original evaluated transition retains the actual iterated input delta and reassociation. -/
theorem inputTransition_component (n m : ℕ) (X : Carrier.{u, v}) :
    (level m).map ((inputTransition n).app X) =
      (level m).map ((power n).map (Delooping.delta.app X)) ≫
        (level m).map
          (eqToHom (Functor.congr_obj
            (Functor.Iteration.iterate_succ_prefix shiftedLoop n).symm X)) := by
  rw [inputTransition, Functor.Iteration.inputTransition_app, Functor.map_comp]

/-- The original input delta has its actual full evaluated transition square at every power. -/
theorem inputTransition_evaluation (n m : ℕ) (X : Carrier.{u, v}) :
    (level m).map ((inputTransition n).app X) ≫
        (evaluationComparison (n + 1) m).hom.app X =
      (evaluationComparison n m).hom.app X ≫
        (LoopPowerAtPoints.power n).map ((level (m + n)).map (Delooping.delta.app X)) ≫
          (prefixEvaluation n m).hom.app X := by
  have hPrefix := congrArg (fun e => e.hom.app X) (evaluationComparison_prefix n m)
  have hNatural := evaluationComparison_hom_naturality n m (Delooping.delta.app X)
  rw [inputTransition_component, Category.assoc]
  change (level m).map ((Functor.Iteration.iteratePrefixIso shiftedLoop n).inv.app X) ≫
      (evaluationComparison (n + 1) m).hom.app X =
    (evaluationComparison n m).hom.app (shiftedLoop.obj X) ≫
      (prefixEvaluation n m).hom.app X at hPrefix
  rw [← Functor.Iteration.iteratePrefixIso_inv_app]
  rw [hPrefix, ← Category.assoc, hNatural, Category.assoc]
  rfl

/-- The whole native iteration diagram keeps every actual original input arrow. -/
abbrev diagram (X : Carrier.{u, v}) : ℕ ⥤ Carrier.{u, v} :=
  Functor.Iteration.inputDiagram Delooping.delta X

/-- Every original native arrow acts on all actual original input stages. -/
abbrev diagramMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) : diagram X ⟶ diagram Y :=
  Functor.Iteration.inputDiagramMap Delooping.delta f

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.IterationMaps
