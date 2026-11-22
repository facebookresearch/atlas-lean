/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Association

/-!
# Whole original evaluation and prefix association of the same loop iteration

The actual one-step and iterated evaluation Isos are precisely the equality
Isos of their complete original functors. All original map functions are
retained. This identifies the existing original evaluation across the
same one-step prefix association, with the exact level arithmetic and
both whole component maps. The original input-unit naturality therefore
gives the exact original point-set unit square across different iterates.
-/

set_option autoImplicit false
noncomputable section
universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

private theorem originalWholeEvaluationEquality
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (R : C ⥤ C) (L : D ⥤ D) (F : ℕ → (C ⥤ C)) (P : ℕ → (D ⥤ D))
    (E : ℕ → (C ⥤ D)) (hF0 : F 0 = 𝟭 C) (hP0 : P 0 = 𝟭 D)
    (hFSucc : ∀ n, F (n + 1) = F n ⋙ R) (hPSucc : ∀ n, P (n + 1) = P n ⋙ L)
    (hEval : ∀ m, R ⋙ E m = E (m + 1) ⋙ L) (n m : ℕ) :
    F n ⋙ E m = E (m + n) ⋙ P n := by
  induction n generalizing m with
  | zero =>
    exact (congrArg (fun G : C ⥤ C => G ⋙ E m) hF0).trans
      (congrArg (fun G : D ⥤ D => E m ⋙ G) hP0).symm
  | succ n hn =>
    exact (congrArg (fun G : C ⥤ C => G ⋙ E m) (hFSucc n)).trans
      ((congrArg (fun G : C ⥤ D => F n ⋙ G) (hEval m)).trans
        ((congrArg (fun G : C ⥤ D => G ⋙ L) (hn (m + 1))).trans
          ((congrArg (fun j : ℕ => E j ⋙ (P n ⋙ L))
            (show m + 1 + n = m + (n + 1) by omega)).trans
              (congrArg (fun G : D ⥤ D => E (m + (n + 1)) ⋙ G) (hPSucc n)).symm)))

private theorem originalWholePrefixEvaluationEquality
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (R : C ⥤ C) (L P Q : D ⥤ D) (E E' E'' : C ⥤ D)
    (hE : R ⋙ E = E' ⋙ L) (hP : L ⋙ P = Q) (hIndex : E' = E'') :
    R ⋙ E ⋙ P = E'' ⋙ Q :=
  (congrArg (fun G : C ⥤ D => G ⋙ P) hE).trans
    ((congrArg (fun G : D ⥤ D => E' ⋙ G) hP).trans
      (congrArg (fun G : C ⥤ D => G ⋙ Q) hIndex))

private theorem originalEqIsoWhiskerLeft
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (H : C ⥤ D) {F G : D ⥤ E} (h : F = G) :
    Functor.isoWhiskerLeft H (eqToIso h) =
      eqToIso (congrArg (fun K : D ⥤ E => H ⋙ K) h) := by
  cases h
  rfl

private theorem originalEqIsoWhiskerRight
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (H : D ⥤ E) {F G : C ⥤ D} (h : F = G) :
    Functor.isoWhiskerRight (eqToIso h) H =
      eqToIso (congrArg (fun K : C ⥤ D => K ⋙ H) h) := by
  cases h
  simpa only [eqToIso_refl] using Functor.isoWhiskerRight_refl F H

private theorem originalAssociatorEqIso
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    (P : C ⥤ D) (Q : D ⥤ E) (R : E ⥤ F) :
    Functor.associator P Q R = eqToIso (Functor.assoc P Q R) := rfl

private theorem originalEqIsoSymm
    {C : Type u₁} [Category.{v₁} C] {A B : C} (h : A = B) :
    (eqToIso h).symm = eqToIso h.symm := rfl

private theorem originalWholeUnitEvaluationSquare
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (E : C ⥤ D) {A B C' : C} {P Q : D}
    (u : A ⟶ C') (a : A ⟶ B) (b : B ⟶ C')
    (t : E.obj C' ⟶ Q) (d : E.obj B ⟶ P) (c : E.obj A ⟶ P) (j : P ⟶ Q)
    (hUnit : u = a ≫ b) (hPrefix : E.map b ≫ t = d ≫ j)
    (hOriginal : E.map a ≫ d = c) : E.map u ≫ t = c ≫ j := by
  rw [hUnit, E.map_comp, Category.assoc, hPrefix, ← Category.assoc, hOriginal]

namespace PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry
open CategoryTheory.Spectra.Sequential (evaluation)

/-- The literal original one-step evaluation Iso gives equality of the complete original
functors. -/
theorem levelEvaluationFunctorEq (m : ℕ) :
    functor.{u, v} ⋙ (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m =
      (
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + 1) ⋙ (ihom
          PointedCGWH.sphereOne) :=
  Functor.ext_of_iso (levelEvaluationIso m) (fun _ => rfl) (fun _ => rfl)

/-- Every original one-step evaluation Iso is the exact equality Iso of the original whole
functor. -/
theorem levelEvaluationIso_eq_eqToIso (m : ℕ) :
    levelEvaluationIso.{u, v} m = eqToIso (levelEvaluationFunctorEq m) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change 𝟙 _ = (eqToHom (levelEvaluationFunctorEq m)).app X
  rw [eqToHom_app]
  rfl

/-- Both original full defining functions give the exact evaluated-iteration functor equality. -/
theorem iterationEvaluationFunctorEq (n m : ℕ) :
    iterate.{u, v} n ⋙ (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m =
      (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + n) ⋙ loopPower n :=
  originalWholeEvaluationEquality functor (ihom PointedCGWH.sphereOne) iterate loopPower
    (
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) rfl rfl (fun _ => rfl)
        (fun _ => rfl)
    levelEvaluationFunctorEq n m

/-- The entire original successor evaluation clause is retained before component specialization. -/
theorem iterationEvaluationIso_succ_clause (n m : ℕ) :
    iterationEvaluationIso.{u, v} (n + 1) m =
      Functor.associator (iterate n) functor ((
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m) ≪≫
        Functor.isoWhiskerLeft (iterate n) (levelEvaluationIso m) ≪≫
        (Functor.associator (iterate n) ((
          CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + 1))
          (ihom PointedCGWH.sphereOne)).symm ≪≫
        Functor.isoWhiskerRight (iterationEvaluationIso n (m + 1)) (ihom PointedCGWH.sphereOne) ≪≫
        Functor.associator ((
          CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + 1 + n))
          (loopPower n) (ihom PointedCGWH.sphereOne) ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
            (show m + 1 + n = m + (n + 1) by omega)))
          (loopPower n ⋙ (ihom PointedCGWH.sphereOne)) := rfl

/-- The SAME original whole evaluation Iso is the equality Iso of its complete original functors. -/
theorem iterationEvaluationIso_eq_eqToIso (n m : ℕ) :
    iterationEvaluationIso.{u, v} n m = eqToIso (iterationEvaluationFunctorEq n m) := by
  induction n generalizing m with
  | zero =>
    apply Iso.ext
    apply NatTrans.ext
    funext X
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  | succ n hn =>
    rw [iterationEvaluationIso_succ_clause, hn (m + 1), levelEvaluationIso_eq_eqToIso]
    have hWhiskerLeft := originalEqIsoWhiskerLeft (iterate n) (levelEvaluationFunctorEq m)
    rw [hWhiskerLeft]
    simp only [originalAssociatorEqIso, originalEqIsoSymm,
      originalEqIsoWhiskerRight, eqToIso_trans]
    rfl

/-- The complete forward original iteration evaluation map retains its exact full object
transport. -/
theorem iterationEvaluationIso_hom_app_eqToHom (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIso n m).hom.app X =
      eqToHom (Functor.congr_obj (iterationEvaluationFunctorEq n m) X) :=
  (congrArg (fun e => e.hom.app X) (iterationEvaluationIso_eq_eqToIso n m)).trans
    (eqToHom_app (iterationEvaluationFunctorEq n m) X)

/-- The complete inverse original iteration evaluation map retains the same full object
transport. -/
theorem iterationEvaluationIso_inv_app_eqToHom (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIso n m).inv.app X =
      eqToHom (Functor.congr_obj (iterationEvaluationFunctorEq n m).symm X) :=
  (congrArg (fun e => e.inv.app X) (iterationEvaluationIso_eq_eqToIso n m)).trans
    (eqToHom_app (iterationEvaluationFunctorEq n m).symm X)

/-- The original one-step prefix target retains the precise original level arithmetic. -/
theorem evaluationPrefixTargetFunctorEq (n m : ℕ) :
    functor.{u, v} ⋙ (
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + n) ⋙ loopPower n =
      (
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + (n + 1)) ⋙
          loopPower (n + 1) :=
  originalWholePrefixEvaluationEquality functor (ihom PointedCGWH.sphereOne) (loopPower n)
    (loopPower (n + 1)) ((
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + n))
    ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + n + 1))
    ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + (n + 1)))
    (levelEvaluationFunctorEq (m + n)) (loopPower_succ_prefix n).symm
    (congrArg (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
      (show m + n + 1 = m + (n + 1) by omega))

/-- The complete original prefix target comparison uses the exact original equality functors. -/
def evaluationPrefixTargetNatIso (n m : ℕ) :
    functor.{u, v} ⋙ (
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + n) ⋙ loopPower n ≅
      (
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) (m + (n + 1)) ⋙
          loopPower (n + 1) :=
  eqToIso (evaluationPrefixTargetFunctorEq n m)

/-- Both entire existing original evaluation Isos agree across the same original iteration
prefix. -/
theorem iterationEvaluationIso_prefix_whole (n m : ℕ) :
    Functor.isoWhiskerRight (iteratePrefixNatIso n).symm
        ((
          CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m) ≪≫
            iterationEvaluationIso (n + 1) m =
      Functor.isoWhiskerLeft functor (iterationEvaluationIso n m) ≪≫
        evaluationPrefixTargetNatIso.{u, v} n m := by
  rw [iterationEvaluationIso_eq_eqToIso (n + 1), iterationEvaluationIso_eq_eqToIso n]
  change Functor.isoWhiskerRight (eqToIso (iterate_succ_prefix n).symm)
        ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m) ≪≫
        eqToIso (iterationEvaluationFunctorEq (n + 1) m) =
      Functor.isoWhiskerLeft functor (eqToIso (iterationEvaluationFunctorEq n m)) ≪≫
        eqToIso (evaluationPrefixTargetFunctorEq n m)
  rw [originalEqIsoWhiskerRight, originalEqIsoWhiskerLeft,
    eqToIso_trans, eqToIso_trans]

/-- The whole forward prefix comparison retains the complete original evaluated spectrum map. -/
theorem iterationEvaluationIso_prefix_hom (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ((
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m).map
        ((iteratePrefixNatIso n).inv.app X) ≫
        (iterationEvaluationIso (n + 1) m).hom.app X =
      (iterationEvaluationIso n m).hom.app (functor.obj X) ≫
        (evaluationPrefixTargetNatIso n m).hom.app X :=
  congrArg (fun e => e.hom.app X) (iterationEvaluationIso_prefix_whole n m)

/-- The whole inverse prefix comparison retains all complete original evaluated maps. -/
theorem iterationEvaluationIso_prefix_inv (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIso (n + 1) m).inv.app X ≫
        ((
          CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m).map
            ((iteratePrefixNatIso n).hom.app X) =
      (evaluationPrefixTargetNatIso n m).inv.app X ≫
        (iterationEvaluationIso n m).inv.app (functor.obj X) :=
  congrArg (fun e => e.inv.app X) (iterationEvaluationIso_prefix_whole n m)

/-- The SAME original input unit has its full original evaluation naturality at every actual
iterate. -/
theorem iterationEvaluationIso_original_unit_naturality (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    PointedCGWH.SequentialSpectrum.levelMap ((iterate n).map (unit.app X)) m ≫
        (iterationEvaluationIso n m).hom.app (functor.obj X) =
      (iterationEvaluationIso n m).hom.app X ≫
        (loopPower n).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + n)) :=
  ((iterationEvaluationIso n m).hom.naturality (unit.app X)).trans
    (congrArg (fun f => (iterationEvaluationIso n m).hom.app X ≫ (loopPower n).map f)
      (unit_levelMap X (m + n)))

/-- Different original iterate units retain the exact complete original point-set evaluation
square. -/
theorem iterateUnit_evaluation_prefix_square (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m ≫
        (iterationEvaluationIso (n + 1) m).hom.app X =
      ((iterationEvaluationIso n m).hom.app X ≫
        (loopPower n).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + n))) ≫
          (evaluationPrefixTargetNatIso n m).hom.app X := by
  have hUnit : (iterateUnit n).app X =
      (iterate n).map (unit.app X) ≫ (iteratePrefixNatIso n).inv.app X :=
    congrArg (fun t => t.app X) (iterateUnit_eq_originalInputUnit n)
  exact originalWholeUnitEvaluationSquare ((
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne) m)
    ((iterateUnit n).app X) ((iterate n).map (unit.app X)) ((iteratePrefixNatIso n).inv.app X)
    ((iterationEvaluationIso (n + 1) m).hom.app X)
    ((iterationEvaluationIso n m).hom.app (functor.obj X))
    (((iterationEvaluationIso n m).hom.app X) ≫
      (loopPower n).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + n)))
    ((evaluationPrefixTargetNatIso n m).hom.app X) hUnit
    (iterationEvaluationIso_prefix_hom n m X)
    (iterationEvaluationIso_original_unit_naturality n m X)

end PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry
