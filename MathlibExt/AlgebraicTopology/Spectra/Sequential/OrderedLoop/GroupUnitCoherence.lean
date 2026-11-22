/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.GroupShiftAssociation

/-!
# Complete original group evaluation coherence across the same iterate units

The same original loop-power group shifts associate with a one-loop prefix.
Their full evaluation comparison identifies every original unit transition
with the actual original base-spectrum group structure map. Both full maps,
the simultaneous original level/degree arithmetic transports and all
original spectrum-map naturalities are retained. No second iteration or
stable-pi construction is introduced.
-/

set_option autoImplicit false
noncomputable section
universe u v u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

private theorem originalShiftOneIso
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ C) (Q Q' : C ⥤ D) (s : L ⋙ Q ≅ Q') :
    Functor.associator (𝟭 C) L Q ≪≫ Functor.isoWhiskerLeft (𝟭 C) s ≪≫
      Q'.leftUnitor ≪≫ eqToIso rfl = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change 𝟙 _ ≫ s.hom.app X ≫ 𝟙 _ ≫ 𝟙 _ = s.hom.app X
  simp only [Category.id_comp, Category.comp_id]

private theorem originalCountReindexHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n)) (k : ℕ) {a b : ℕ} (h : a = b) (X : C) :
    (Q k).map (eqToHom (congrArg (fun j => (P j).obj X) h)) ≫ (H b k).hom.app X =
      (H a k).hom.app X ≫ eqToHom (congrArg (fun j => (Q (k + j)).obj X) h) := by
  cases h
  rw [eqToHom_refl, (Q k).map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

private theorem originalCoefficientCastPath
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : ℕ → (C ⥤ D)) {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (X : C) :
    (eqToIso (congrArg Q h₁)).hom.app X ≫
        eqToHom (congrArg (fun j => (Q j).obj X) h₂) =
      (eqToIso (congrArg Q h₃)).hom.app X := by
  have hA : (eqToIso (congrArg Q h₁)).hom.app X =
      eqToHom (congrArg (fun j => (Q j).obj X) h₁) := eqToHom_app (congrArg Q h₁) X
  have hC : (eqToIso (congrArg Q h₃)).hom.app X =
      eqToHom (congrArg (fun j => (Q j).obj X) h₃) := eqToHom_app (congrArg Q h₃) X
  have hPath : eqToHom (congrArg (fun j => (Q j).obj X) h₁) ≫
      eqToHom (congrArg (fun j => (Q j).obj X) h₂) =
        eqToHom (congrArg (fun j => (Q j).obj X) h₃) := by
    rw [eqToHom_trans]
  exact (congrArg (fun f => f ≫ eqToHom (congrArg (fun j => (Q j).obj X) h₂)) hA).trans
    (hPath.trans hC.symm)

private theorem originalFunctorCastDecomposition
    {C : Type u₁} [Category.{v₁} C] (P : C ⥤ C) {A B D : C}
    (h₀ : A = P.obj D) (h₁ : A = P.obj B) (h₂ : B = D) :
    eqToHom h₀ = eqToHom h₁ ≫ P.map (eqToHom h₂) := by
  rw [eqToHom_map, eqToHom_trans]

private theorem originalPointedCastPath
    {C : Type u₁} [Category.{v₁} C] {A B D : C}
    (h₀ : A = D) (h₁ : A = B) (h₂ : B = D) :
    eqToHom h₀ = eqToHom h₁ ≫ eqToHom h₂ := by
  rw [eqToHom_trans]

private theorem originalCompositionMatrix
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) {A B C' : C} {Y Z : D}
    (u : A ⟶ B) (a : A ⟶ C') (b : C' ⟶ B)
    (t : F.obj B ⟶ Z) (t' : F.obj C' ⟶ Y) (e : Y ⟶ Z) (c : F.obj A ⟶ Y)
    (h₀ : u = a ≫ b) (h₁ : F.map b ≫ t = t' ≫ e) (h₂ : F.map a ≫ t' = c) :
    F.map u ≫ t = c ≫ e := by
  rw [h₀, F.map_comp, Category.assoc, h₁, ← Category.assoc, h₂]

private theorem originalMappedComparisonIsoHom
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F₀ : C ⥤ D} (F : C ⥤ D) (P : D ⥤ D) (Q : D ⥤ E) {Q' : D ⥤ E}
    (e : F₀ ≅ F ⋙ P) (h : P ⋙ Q ≅ Q') (X : C) :
    (Functor.isoWhiskerRight e Q ≪≫ Functor.associator F P Q ≪≫
      Functor.isoWhiskerLeft F h).hom.app X = Q.map (e.hom.app X) ≫ h.hom.app (F.obj X) := by
  change Q.map (e.hom.app X) ≫ 𝟙 _ ≫ h.hom.app (F.obj X) = _
  exact congrArg (fun f => Q.map (e.hom.app X) ≫ f) (Category.id_comp _)

private theorem originalNatIsoWordReplacement
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F G : C ⥤ D} (i j : F ≅ G) (h : i = j) (X : C)
    {A B : D} (a : A ⟶ F.obj X) (b : G.obj X ⟶ B) :
    a ≫ i.hom.app X ≫ b = a ≫ j.hom.app X ≫ b := by
  cases h
  rfl

private theorem originalGroupUnitJoining
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q Q' : C ⥤ D) (P : C ⥤ C)
    {A B X Y Z : C} {T U : D}
    (a : A ⟶ B) (e : A ⟶ P.obj X) (f : B ⟶ Z) (b : X ⟶ Y) (t : P.obj Y ⟶ Z)
    (hX : Q.obj (P.obj X) ⟶ Q'.obj X) (hY : Q.obj (P.obj Y) ⟶ Q'.obj Y)
    (hZ : Q.obj Z ⟶ U) (s : Q'.obj Y ⟶ T) (i : T ⟶ U)
    (hPoint : a ≫ f = (e ≫ P.map b) ≫ t)
    (hTail : Q.map t ≫ hZ = hY ≫ s ≫ i)
    (hNatural : Q.map (P.map b) ≫ hY = hX ≫ Q'.map b) :
    Q.map a ≫ (Q.map f ≫ hZ) = (Q.map e ≫ hX) ≫ (Q'.map b ≫ s) ≫ i := by
  rw [← Category.assoc, ← Q.map_comp, hPoint, Q.map_comp, Q.map_comp]
  simp only [Category.assoc]
  rw [hTail]
  rw [← Category.assoc (Q.map (P.map b)) hY (s ≫ i), hNatural]
  simp only [Category.assoc]

private theorem originalInverseUnitSquare
    {C : Type u₁} [Category.{v₁} C] {A B D E : C}
    (c : A ≅ D) (d : B ≅ E) (u : A ⟶ B) (v : D ⟶ E)
    (h : u ≫ d.hom = c.hom ≫ v) : c.inv ≫ u = v ≫ d.inv := by
  apply (cancel_mono d.hom).mp
  rw [Category.assoc, h, ← Category.assoc, c.inv_hom_id, Category.id_comp,
    Category.assoc, d.inv_hom_id, Category.comp_id]

namespace PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open CategoryTheory.Spectra.Sequential (evaluation)
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyAssociationGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry

/-- The entire original one-loop group-shift value is the SAME original native one-step shift. -/
theorem loopPowerGroupShiftNatIso_one (k : ℕ) :
    loopPowerGroupShiftNatIso.{u, v} 1 k = nativeLoopGroupShiftNatIso k := by
  change Functor.associator (𝟭 PointedCGWH.{u, v}) PointedCGWH.loop
      (PointedCGWH.piNPositiveFunctor k) ≪≫
    Functor.isoWhiskerLeft (𝟭 PointedCGWH.{u, v}) (nativeLoopGroupShiftNatIso k) ≪≫
      (PointedCGWH.piNPositiveFunctor (k + 1)).leftUnitor ≪≫ eqToIso rfl = _
  exact originalShiftOneIso PointedCGWH.loop (PointedCGWH.piNPositiveFunctor k)
    (PointedCGWH.piNPositiveFunctor (k + 1)) (nativeLoopGroupShiftNatIso k)

/-- The complete original one-loop prefix comparison uses the same original loop-power equality. -/
def loopPowerPrefixNatIso (n : ℕ) :
    loopPower.{u, v} (n + 1) ≅ PointedCGWH.loop ⋙ loopPower n :=
  eqToIso (loopPower_succ_prefix n)

/-- The exact original group-degree reassociation preserves both complete comparison maps. -/
def groupPrefixIndexNatIso (n k : ℕ) :
    PointedCGWH.piNPositiveFunctor.{u, v} (k + n + 1) ≅
      PointedCGWH.piNPositiveFunctor (k + (n + 1)) :=
  eqToIso (congrArg PointedCGWH.piNPositiveFunctor
    (show k + n + 1 = k + (n + 1) by omega))

/-- All original group shifts retain the full prefix/tail association with exact arithmetic maps. -/
theorem loopPowerGroupShift_prefix_hom (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).map ((loopPowerPrefixNatIso n).inv.app X) ≫
        (loopPowerGroupShiftNatIso (n + 1) k).hom.app X =
      ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj X) ≫
        (nativeLoopGroupShiftNatIso (k + n)).hom.app X) ≫
          (groupPrefixIndexNatIso n k).hom.app X := by
  let a := (loopPowerAddNatIso 1 n).inv.app X
  have hCount : 1 + n = n + 1 := by omega
  let b := eqToHom (congrArg (fun j => (loopPower j).obj X) hCount)
  let e := eqToHom (congrArg (fun j =>
    (PointedCGWH.piNPositiveFunctor (k + j)).obj X) hCount)
  have hCast : (loopPowerPrefixNatIso n).inv.app X = a ≫ b := by
    have hPrefix := eqToHom_app (loopPower_succ_prefix n).symm X
    have hAdd : a = eqToHom (Functor.congr_obj (loopPower_add 1 n).symm X) :=
      loopPowerAddNatIso_inv_app 1 n X
    have hPath := originalPointedCastPath
      (Functor.congr_obj (loopPower_succ_prefix n).symm X)
      (Functor.congr_obj (loopPower_add 1 n).symm X)
      (congrArg (fun j => (loopPower j).obj X) hCount)
    exact hPrefix.trans (hPath.trans (congrArg (fun f => f ≫ b) hAdd.symm))
  have hReindex : (PointedCGWH.piNPositiveFunctor k).map b ≫
        (loopPowerGroupShiftNatIso (n + 1) k).hom.app X =
      (loopPowerGroupShiftNatIso (1 + n) k).hom.app X ≫ e :=
    originalCountReindexHom loopPower PointedCGWH.piNPositiveFunctor
      loopPowerGroupShiftNatIso k hCount X
  have hWord : (PointedCGWH.piNPositiveFunctor k).map a ≫
        (loopPowerGroupShiftNatIso (1 + n) k).hom.app X =
      ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj X) ≫
        (nativeLoopGroupShiftNatIso (k + n)).hom.app X) ≫
          (groupAssociationIndexNatIso 1 n k).hom.app X := by
    have h := (loopPowerGroupAssociation_hom 1 n k X).trans
      (originalNatIsoWordReplacement (loopPowerGroupShiftNatIso 1 (k + n))
        (nativeLoopGroupShiftNatIso (k + n)) (loopPowerGroupShiftNatIso_one (k + n)) X
        ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj X))
        ((groupAssociationIndexNatIso 1 n k).hom.app X))
    exact h.trans (Category.assoc _ _ _).symm
  have hIndices : (groupAssociationIndexNatIso 1 n k).hom.app X ≫ e =
      (groupPrefixIndexNatIso n k).hom.app X :=
    originalCoefficientCastPath PointedCGWH.piNPositiveFunctor
      (show k + n + 1 = k + (1 + n) by omega)
      (show k + (1 + n) = k + (n + 1) by omega)
      (show k + n + 1 = k + (n + 1) by omega) X
  have h := originalCompositionMatrix (PointedCGWH.piNPositiveFunctor k)
    ((loopPowerPrefixNatIso n).inv.app X) a b
    ((loopPowerGroupShiftNatIso (n + 1) k).hom.app X)
    ((loopPowerGroupShiftNatIso (1 + n) k).hom.app X) e
    (((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj X) ≫
      (nativeLoopGroupShiftNatIso (k + n)).hom.app X) ≫
        (groupAssociationIndexNatIso 1 n k).hom.app X) hCast hReindex hWord
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (fun f => ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj X) ≫
      (nativeLoopGroupShiftNatIso (k + n)).hom.app X) ≫ f) hIndices))

/-- The exact original successor level arithmetic keeps the same original evaluation functors. -/
def levelUnitIndexNatIso (n m : ℕ) :
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} (m + n + 1) ≅
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + (n + 1)) :=
  eqToIso (congrArg (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
    (show m + n + 1 = m + (n + 1) by omega))

/-- Both original level and group-degree arithmetic transports form the full actual target Iso. -/
def groupUnitIndexNatIso (n m k : ℕ) :
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} (m + n + 1) ⋙
        PointedCGWH.piNPositiveFunctor (k + n + 1) ≅
        CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + (n + 1)) ⋙
          PointedCGWH.piNPositiveFunctor (k + (n + 1)) :=
  Functor.isoWhiskerLeft (
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + n + 1))
      (groupPrefixIndexNatIso n k) ≪≫
    Functor.isoWhiskerRight (levelUnitIndexNatIso n m)
      (PointedCGWH.piNPositiveFunctor (k + (n + 1)))

/-- The entire target comparison has the literal original degree map and original level map. -/
theorem groupUnitIndexNatIso_hom_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupUnitIndexNatIso n m k).hom.app X =
      (groupPrefixIndexNatIso n k).hom.app (X.level (m + n + 1)) ≫
        (PointedCGWH.piNPositiveFunctor (k + (n + 1))).map
          ((levelUnitIndexNatIso n m).hom.app X) := rfl

/-- The entire inverse target comparison keeps both same original inverse arithmetic maps. -/
theorem groupUnitIndexNatIso_inv_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupUnitIndexNatIso n m k).inv.app X =
      (PointedCGWH.piNPositiveFunctor (k + (n + 1))).map
          ((levelUnitIndexNatIso n m).inv.app X) ≫
        (groupPrefixIndexNatIso n k).inv.app (X.level (m + n + 1)) := rfl

/-- The SAME original evaluation prefix target decomposes through both original point-set maps. -/
theorem evaluationPrefixTargetNatIso_hom_decomposition (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (evaluationPrefixTargetNatIso n m).hom.app X =
      (loopPowerPrefixNatIso n).inv.app (X.level (m + n + 1)) ≫
        (loopPower (n + 1)).map ((levelUnitIndexNatIso n m).hom.app X) := by
  have h₀ := eqToHom_app (evaluationPrefixTargetFunctorEq n m) X
  have h₁ := eqToHom_app (loopPower_succ_prefix n).symm (X.level (m + n + 1))
  have h₂ := eqToHom_app (congrArg (
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
    (show m + n + 1 = m + (n + 1) by omega)) X
  have hCast := originalFunctorCastDecomposition (loopPower (n + 1))
    (Functor.congr_obj (evaluationPrefixTargetFunctorEq n m) X)
    (Functor.congr_obj (loopPower_succ_prefix n).symm (X.level (m + n + 1)))
    (Functor.congr_obj (congrArg (
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
      (show m + n + 1 = m + (n + 1) by omega)) X)
  exact h₀.trans (hCast.trans
    (congrArg₂ (fun f g => f ≫ (loopPower (n + 1)).map g) h₁.symm h₂.symm))

/-- The full original prefix group evaluation joins the same original iterated and native shifts. -/
theorem evaluationPrefixTarget_group_hom (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).map ((evaluationPrefixTargetNatIso n m).hom.app X) ≫
        (loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + (n + 1))) =
      ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj (X.level (m + n + 1))) ≫
        (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n + 1))) ≫
          (groupUnitIndexNatIso n m k).hom.app X := by
  let j := (levelUnitIndexNatIso n m).hom.app X
  let a := (loopPowerPrefixNatIso n).inv.app (X.level (m + n + 1))
  let i := (PointedCGWH.piNPositiveFunctor (k + (n + 1))).map j
  have hOriginal := loopPowerGroupShift_prefix_hom n k (X.level (m + n + 1))
  have hNatural : (PointedCGWH.piNPositiveFunctor k).map ((loopPower (n + 1)).map j) ≫
        (loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + (n + 1))) =
      (loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + n + 1)) ≫ i :=
    loopPowerGroupShiftNatIso_hom_naturality (n + 1) k j
  have h := originalCompositionMatrix (PointedCGWH.piNPositiveFunctor k)
    ((evaluationPrefixTargetNatIso n m).hom.app X) a ((loopPower (n + 1)).map j)
    ((loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + (n + 1))))
    ((loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + n + 1))) i
    (((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj (X.level (m + n + 1))) ≫
      (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n + 1))) ≫
        (groupPrefixIndexNatIso n k).hom.app (X.level (m + n + 1)))
    (evaluationPrefixTargetNatIso_hom_decomposition n m X) hNatural hOriginal
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (fun f => ((loopPowerGroupShiftNatIso n k).hom.app
      (PointedCGWH.loop.obj (X.level (m + n + 1))) ≫
        (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n + 1))) ≫ f)
          (groupUnitIndexNatIso_hom_app n m k X).symm))

/-- The entire actual original group evaluation component keeps both original forward maps. -/
theorem iterationGroupEvaluationNatIso_hom_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationNatIso n m k).hom.app X =
      (PointedCGWH.piNPositiveFunctor k).map ((iterationEvaluationIso n m).hom.app X) ≫
        (loopPowerGroupShiftNatIso n k).hom.app (X.level (m + n)) :=
  originalMappedComparisonIsoHom (
    CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + n)) (loopPower n)
    (PointedCGWH.piNPositiveFunctor k) (iterationEvaluationIso n m)
    (loopPowerGroupShiftNatIso n k) X

/-- Every original iterate unit transition is the actual original base-spectrum group structure
map. -/
theorem iterationGroupEvaluation_unit_transition_hom (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) ≫
          (iterationGroupEvaluationNatIso (n + 1) m k).hom.app X =
      (iterationGroupEvaluationNatIso n m k).hom.app X ≫
        (groupStructureNatTrans (m + n) (k + n)).app X ≫
          (groupUnitIndexNatIso n m k).hom.app X := by
  let b := PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + n)
  have hPoint := iterateUnit_evaluation_prefix_square n m X
  have hTail := evaluationPrefixTarget_group_hom n m k X
  have hNatural := loopPowerGroupShiftNatIso_hom_naturality n k b
  have h := originalGroupUnitJoining (PointedCGWH.piNPositiveFunctor k)
    (PointedCGWH.piNPositiveFunctor (k + n)) (loopPower n)
    (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m)
    ((iterationEvaluationIso n m).hom.app X) ((iterationEvaluationIso (n + 1) m).hom.app X)
    b ((evaluationPrefixTargetNatIso n m).hom.app X)
    ((loopPowerGroupShiftNatIso n k).hom.app (X.level (m + n)))
    ((loopPowerGroupShiftNatIso n k).hom.app (PointedCGWH.loop.obj (X.level (m + n + 1))))
    ((loopPowerGroupShiftNatIso (n + 1) k).hom.app (X.level (m + (n + 1))))
    ((nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n + 1)))
    ((groupUnitIndexNatIso n m k).hom.app X) hPoint hTail hNatural
  have hPlus := iterationGroupEvaluationNatIso_hom_app (n + 1) m k X
  have hCurrent := iterationGroupEvaluationNatIso_hom_app n m k X
  have hStructure : (groupStructureNatTrans (m + n) (k + n)).app X =
      (PointedCGWH.piNPositiveFunctor (k + n)).map b ≫
        (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n + 1)) := rfl
  exact (congrArg (fun f => (PointedCGWH.piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) ≫ f) hPlus).trans
    (h.trans (congrArg₂ (fun f g => f ≫ g ≫ (groupUnitIndexNatIso n m k).hom.app X)
      hCurrent.symm hStructure.symm))

/-- The WHOLE original natural unit transition and group comparison commute across all spectra. -/
theorem iterationGroupEvaluation_unit_transition_whole (n m k : ℕ) :
    Functor.whiskerRight
        (Functor.whiskerRight (iterateUnit n) (
          CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m))
          (PointedCGWH.piNPositiveFunctor k) ≫
            (iterationGroupEvaluationNatIso (n + 1) m k).hom =
      (iterationGroupEvaluationNatIso n m k).hom ≫ groupStructureNatTrans (m + n) (k + n) ≫
        (groupUnitIndexNatIso.{u, v} n m k).hom := by
  apply NatTrans.ext
  funext X
  exact iterationGroupEvaluation_unit_transition_hom n m k X

/-- The complete inverse group comparison retains the SAME original transition and structure map. -/
theorem iterationGroupEvaluation_unit_transition_inv (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationNatIso n m k).inv.app X ≫
        (PointedCGWH.piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) =
      ((groupStructureNatTrans (m + n) (k + n)).app X ≫
        (groupUnitIndexNatIso n m k).hom.app X) ≫
          (iterationGroupEvaluationNatIso (n + 1) m k).inv.app X :=
  originalInverseUnitSquare ((iterationGroupEvaluationNatIso n m k).app X)
    ((iterationGroupEvaluationNatIso (n + 1) m k).app X)
    ((PointedCGWH.piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m))
    ((groupStructureNatTrans (m + n) (k + n)).app X ≫ (groupUnitIndexNatIso n m k).hom.app X)
    (iterationGroupEvaluation_unit_transition_hom n m k X)

/-- All original spectrum-map squares retain the full actual target arithmetic comparison. -/
theorem groupUnitIndexNatIso_hom_naturality (n m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (k + n + 1)).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + n + 1)) ≫
          (groupUnitIndexNatIso n m k).hom.app Y =
      (groupUnitIndexNatIso n m k).hom.app X ≫
        (PointedCGWH.piNPositiveFunctor (k + (n + 1))).map
          (PointedCGWH.SequentialSpectrum.levelMap f (m + (n + 1))) :=
  (groupUnitIndexNatIso n m k).hom.naturality f

/-- All original spectrum-map squares retain the full inverse actual target comparison. -/
theorem groupUnitIndexNatIso_inv_naturality (n m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (k + (n + 1))).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + (n + 1))) ≫
          (groupUnitIndexNatIso n m k).inv.app Y =
      (groupUnitIndexNatIso n m k).inv.app X ≫
        (PointedCGWH.piNPositiveFunctor (k + n + 1)).map
          (PointedCGWH.SequentialSpectrum.levelMap f (m + n + 1)) :=
  (groupUnitIndexNatIso n m k).inv.naturality f

end PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
