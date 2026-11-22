/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.EvaluationAssociation

/-!
# Whole association of the same original iterated native group shift

The complete original group-shift defining clauses associate over arbitrary
categories before specialization. Every power, shift, group object, map
and arithmetic equality is the SAME original one. Both complete maps and
all original pointed-map naturalities are retained. This is composition
of the same loop powers and does not assert an interchange structure on
the original sequential index.
-/

set_option autoImplicit false
noncomputable section
universe u v u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

private theorem originalWhiskeredCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : C ⥤ D) {P R : C ⥤ C} (h : P = R) (X : C) :
    (Functor.isoWhiskerRight (eqToIso h) Q).hom.app X =
      Q.map (eqToHom (Functor.congr_obj h X)) := by
  change Q.map ((eqToHom h).app X) = _
  exact congrArg Q.map (eqToHom_app h X)

private theorem originalWhiskeredInverseCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : C ⥤ D) {P R : C ⥤ C} (h : P = R) (X : C) :
    (Functor.isoWhiskerRight (eqToIso h).symm Q).hom.app X =
      Q.map (eqToHom (Functor.congr_obj h.symm X)) :=
  originalWhiskeredCastHom Q h.symm X

private theorem originalCoefficientCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : ℕ → (C ⥤ D)) {a b : ℕ} (h : a = b) (X : C) :
    (eqToIso (congrArg Q h)).hom.app X =
      eqToHom (congrArg (fun j => (Q j).obj X) h) :=
  eqToHom_app (congrArg Q h) X

private theorem originalGradedShiftZeroHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n)) (hP0 : P 0 = 𝟭 C)
    (hZero : ∀ k, H 0 k =
      Functor.isoWhiskerRight (eqToIso hP0) (Q k) ≪≫ (Q k).leftUnitor)
    (k : ℕ) (X : C) :
    (H 0 k).hom.app X = (Q k).map (eqToHom (Functor.congr_obj hP0 X)) := by
  exact (congrArg (fun e => e.hom.app X) (hZero k)).trans
    ((congrArg (fun f => f ≫ 𝟙 ((Q k).obj X)) (originalWhiskeredCastHom (Q k) hP0 X)).trans
      (Category.comp_id _))

private theorem originalGradedShiftSuccessorHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ C) (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (S : ∀ k, L ⋙ Q k ≅ Q (k + 1))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n))
    (hPSucc : ∀ n, P (n + 1) = P n ⋙ L)
    (hSucc : ∀ n k, H (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (hPSucc n)) (Q k) ≪≫
        Functor.associator (P n) L (Q k) ≪≫
        Functor.isoWhiskerLeft (P n) (S k) ≪≫ H n (k + 1) ≪≫
        eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega)))
    (n k : ℕ) (X : C) :
    (H (n + 1) k).hom.app X =
      (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
        (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫
          eqToHom (congrArg (fun j => (Q j).obj X)
            (show k + 1 + n = k + (n + 1) by omega)) := by
  have h := congrArg (fun e => e.hom.app X) (hSucc n k)
  have hBody : (H (n + 1) k).hom.app X =
      (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
        (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫
          (eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega))).hom.app X := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, originalWhiskeredCastHom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] using h
  exact hBody.trans (congrArg (fun f =>
    (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
      (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫ f)
        (originalCoefficientCastHom Q
          (show k + 1 + n = k + (n + 1) by omega) X))

private theorem originalAssociatedShiftHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P R : C ⥤ C) (Q : C ⥤ D) {A B B' : C ⥤ D}
    (h : R ⋙ Q ≅ A) (j : P ⋙ A ≅ B) (e : B = B') (X : C) :
    (Functor.associator P R Q ≪≫ Functor.isoWhiskerLeft P h ≪≫ j ≪≫ eqToIso e).hom.app X =
      h.hom.app (P.obj X) ≫ j.hom.app X ≫ eqToHom (Functor.congr_obj e X) := by
  change 𝟙 _ ≫ h.hom.app (P.obj X) ≫ j.hom.app X ≫ (eqToHom e).app X = _
  exact (Category.id_comp _).trans (congrArg
    (fun f => h.hom.app (P.obj X) ≫ j.hom.app X ≫ f) (eqToHom_app e X))

private theorem originalGradedShiftReindexHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n)) (n : ℕ) {a b : ℕ} (h : a = b) (X : C) :
    eqToHom (congrArg (fun j => (Q j).obj ((P n).obj X)) h) ≫ (H n b).hom.app X =
      (H n a).hom.app X ≫ eqToHom (congrArg (fun j => (Q (j + n)).obj X) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

private theorem originalWholeGradedShiftAssociationHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ C) (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (S : ∀ k, L ⋙ Q k ≅ Q (k + 1))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n))
    (hP0 : P 0 = 𝟭 C) (hPSucc : ∀ n, P (n + 1) = P n ⋙ L)
    (hPAdd : ∀ n m, P (n + m) = P n ⋙ P m)
    (hZero : ∀ k, H 0 k =
      Functor.isoWhiskerRight (eqToIso hP0) (Q k) ≪≫ (Q k).leftUnitor)
    (hSucc : ∀ n k, H (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (hPSucc n)) (Q k) ≪≫
        Functor.associator (P n) L (Q k) ≪≫
        Functor.isoWhiskerLeft (P n) (S k) ≪≫ H n (k + 1) ≪≫
        eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega)))
    (n m k : ℕ) (X : C) :
    (Q k).map (eqToHom (Functor.congr_obj (hPAdd n m).symm X)) ≫
        (H (n + m) k).hom.app X =
      (H m k).hom.app ((P n).obj X) ≫ (H n (k + m)).hom.app X ≫
        eqToHom (congrArg (fun j => (Q j).obj X)
          (show k + m + n = k + (n + m) by omega)) := by
  induction m generalizing k X with
  | zero =>
    have hCast : eqToHom (Functor.congr_obj (hPAdd n 0).symm X) =
        eqToHom (Functor.congr_obj hP0 ((P n).obj X)) := rfl
    have hZeroHom := originalGradedShiftZeroHom P Q H hP0 hZero k ((P n).obj X)
    change (Q k).map _ ≫ (H n k).hom.app X =
      (H 0 k).hom.app ((P n).obj X) ≫ (H n k).hom.app X ≫ 𝟙 _
    rw [hCast, ← hZeroHom, Category.comp_id]
  | succ m hm =>
    let c : (P m).obj ((P n).obj X) ⟶ (P (n + m)).obj X :=
      eqToHom (Functor.congr_obj (hPAdd n m).symm X)
    let e : (P ((n + m) + 1)).obj X ⟶ L.obj ((P (n + m)).obj X) :=
      eqToHom (Functor.congr_obj (hPSucc (n + m)) X)
    let d : (P (m + 1)).obj ((P n).obj X) ⟶ L.obj ((P m).obj ((P n).obj X)) :=
      eqToHom (Functor.congr_obj (hPSucc m) ((P n).obj X))
    let cNext : (P (m + 1)).obj ((P n).obj X) ⟶ (P (n + (m + 1))).obj X :=
      eqToHom (Functor.congr_obj (hPAdd n (m + 1)).symm X)
    have hCast : cNext ≫ e = d ≫ L.map c := by
      change eqToHom _ ≫ eqToHom _ = eqToHom _ ≫ L.map (eqToHom _)
      rw [eqToHom_map, eqToHom_trans, eqToHom_trans]
    have hCastQ : (Q k).map cNext ≫ (Q k).map e =
        (Q k).map d ≫ (Q k).map (L.map c) :=
      ((Q k).map_comp cNext e).symm.trans
        ((congrArg (Q k).map hCast).trans ((Q k).map_comp d (L.map c)))
    have hNatural : (Q k).map (L.map c) ≫ (S k).hom.app ((P (n + m)).obj X) =
        (S k).hom.app ((P m).obj ((P n).obj X)) ≫ (Q (k + 1)).map c :=
      (S k).hom.naturality c
    let cIH := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + 1 + m + n = k + 1 + (n + m) by omega))
    let cSum := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + 1 + (n + m) = k + ((n + m) + 1) by omega))
    have hDegree : k + 1 + m = k + (m + 1) := by omega
    let cM := eqToHom (congrArg (fun j => (Q j).obj ((P n).obj X)) hDegree)
    let cN := eqToHom (congrArg (fun j => (Q (j + n)).obj X) hDegree)
    let cTotal := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + (m + 1) + n = k + (n + (m + 1)) by omega))
    have hPaths : cIH ≫ cSum = cN ≫ cTotal := by
      change eqToHom _ ≫ eqToHom _ = eqToHom _ ≫ eqToHom _
      rw [eqToHom_trans, eqToHom_trans]
    have hReindex : cM ≫ (H n (k + (m + 1))).hom.app X =
        (H n (k + 1 + m)).hom.app X ≫ cN :=
      originalGradedShiftReindexHom P Q H n hDegree X
    have hIH : (Q (k + 1)).map c ≫ (H (n + m) (k + 1)).hom.app X =
        (H m (k + 1)).hom.app ((P n).obj X) ≫
          (H n (k + 1 + m)).hom.app X ≫ cIH := hm (k + 1) X
    have hSum : (H ((n + m) + 1) k).hom.app X =
        (Q k).map e ≫ (S k).hom.app ((P (n + m)).obj X) ≫
          (H (n + m) (k + 1)).hom.app X ≫ cSum :=
      originalGradedShiftSuccessorHom L P Q S H hPSucc hSucc (n + m) k X
    have hM : (H (m + 1) k).hom.app ((P n).obj X) =
        (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫ cM :=
      originalGradedShiftSuccessorHom L P Q S H hPSucc hSucc m k ((P n).obj X)
    calc
      (Q k).map cNext ≫ (H ((n + m) + 1) k).hom.app X =
          (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            ((Q (k + 1)).map c ≫ (H (n + m) (k + 1)).hom.app X) ≫ cSum := by
        rw [hSum]
        rw [← Category.assoc ((Q k).map cNext) ((Q k).map e)
          ((S k).hom.app ((P (n + m)).obj X) ≫
            (H (n + m) (k + 1)).hom.app X ≫ cSum), hCastQ, Category.assoc]
        rw [← Category.assoc ((Q k).map (L.map c)) ((S k).hom.app ((P (n + m)).obj X))
          ((H (n + m) (k + 1)).hom.app X ≫ cSum), hNatural]
        simp only [Category.assoc]
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            (H n (k + 1 + m)).hom.app X ≫ cIH ≫ cSum := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫ a ≫ cSum) hIH
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            (H n (k + 1 + m)).hom.app X ≫ cN ≫ cTotal := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            (H m (k + 1)).hom.app ((P n).obj X) ≫ (H n (k + 1 + m)).hom.app X ≫ a) hPaths
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            cM ≫ (H n (k + (m + 1))).hom.app X ≫ cTotal := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            (H m (k + 1)).hom.app ((P n).obj X) ≫ a ≫ cTotal) hReindex.symm
      _ = (H (m + 1) k).hom.app ((P n).obj X) ≫
          (H n (k + (m + 1))).hom.app X ≫ cTotal := by
        simpa only [Category.assoc] using
          congrArg (fun a => a ≫ (H n (k + (m + 1))).hom.app X ≫ cTotal) hM.symm

namespace PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyAssociationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry

/-- The whole actual original zero loop-power defining clause is retained. -/
theorem loopPowerZeroFunctorEq : loopPower.{u, v} 0 = 𝟭 PointedCGWH.{u, v} := rfl

/-- The whole actual original successor loop-power defining clause is retained. -/
theorem loopPowerSuccessorFunctorEq (n : ℕ) :
    loopPower.{u, v} (n + 1) = loopPower n ⋙ PointedCGWH.loop := rfl

/-- The entire original zero group-shift defining clause is transported before specialization. -/
theorem loopPowerGroupShiftNatIso_zero_clause (k : ℕ) :
    loopPowerGroupShiftNatIso.{u, v} 0 k =
      Functor.isoWhiskerRight (eqToIso loopPowerZeroFunctorEq)
        (PointedCGWH.piNPositiveFunctor k) ≪≫
          (PointedCGWH.piNPositiveFunctor k).leftUnitor := by
  change (PointedCGWH.piNPositiveFunctor k).leftUnitor =
    Functor.isoWhiskerRight (Iso.refl (𝟭 PointedCGWH.{u, v}))
      (PointedCGWH.piNPositiveFunctor k) ≪≫ (PointedCGWH.piNPositiveFunctor k).leftUnitor
  rw [Functor.isoWhiskerRight_refl, Iso.refl_trans]

/-- The full original successor group-shift value is retained, including both degree transports. -/
theorem loopPowerGroupShiftNatIso_succ_clause (n k : ℕ) :
    loopPowerGroupShiftNatIso.{u, v} (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (loopPowerSuccessorFunctorEq n))
        (PointedCGWH.piNPositiveFunctor k) ≪≫
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNPositiveFunctor k) ≪≫
      Functor.isoWhiskerLeft (loopPower n) (nativeLoopGroupShiftNatIso k) ≪≫
      loopPowerGroupShiftNatIso n (k + 1) ≪≫
      eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega)) := by
  have hCast : Functor.isoWhiskerRight (eqToIso (loopPowerSuccessorFunctorEq n))
      (PointedCGWH.piNPositiveFunctor k) =
      Iso.refl ((loopPower n ⋙ PointedCGWH.loop) ⋙ PointedCGWH.piNPositiveFunctor k) := by
    change Functor.isoWhiskerRight (Iso.refl (loopPower n ⋙ PointedCGWH.loop))
      (PointedCGWH.piNPositiveFunctor k) = _
    exact Functor.isoWhiskerRight_refl _ _
  let b : (loopPower n ⋙ PointedCGWH.loop) ⋙ PointedCGWH.piNPositiveFunctor k ≅
      PointedCGWH.piNPositiveFunctor (k + (n + 1)) :=
    Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNPositiveFunctor k) ≪≫
      Functor.isoWhiskerLeft (loopPower n) (nativeLoopGroupShiftNatIso k) ≪≫
        loopPowerGroupShiftNatIso n (k + 1) ≪≫
          eqToIso (congrArg PointedCGWH.piNPositiveFunctor
            (show k + 1 + n = k + (n + 1) by omega))
  have hOriginal : loopPowerGroupShiftNatIso (n + 1) k = b := rfl
  have hPrefix : Functor.isoWhiskerRight (eqToIso (loopPowerSuccessorFunctorEq n))
      (PointedCGWH.piNPositiveFunctor k) ≪≫ b = b :=
    (congrArg (fun e => e ≪≫ b) hCast).trans (Iso.refl_trans b)
  exact hOriginal.trans hPrefix.symm

/-- Full original loop-power association followed by the SAME entire original group shift. -/
def loopPowerGroupAssociationNatIso (n m k : ℕ) :
    (loopPower.{u, v} n ⋙ loopPower m) ⋙ PointedCGWH.piNPositiveFunctor k ≅
      PointedCGWH.piNPositiveFunctor (k + (n + m)) :=
  Functor.isoWhiskerRight (loopPowerAddNatIso n m).symm (PointedCGWH.piNPositiveFunctor k) ≪≫
    loopPowerGroupShiftNatIso (n + m) k

/-- All complete original group comparison maps associate with the exact original index
transport. -/
theorem loopPowerGroupAssociationNatIso_eq (n m k : ℕ) :
    loopPowerGroupAssociationNatIso.{u, v} n m k =
      Functor.associator (loopPower n) (loopPower m) (PointedCGWH.piNPositiveFunctor k) ≪≫
        Functor.isoWhiskerLeft (loopPower n) (loopPowerGroupShiftNatIso m k) ≪≫
        loopPowerGroupShiftNatIso n (k + m) ≪≫
        eqToIso (congrArg PointedCGWH.piNPositiveFunctor
          (show k + m + n = k + (n + m) by omega)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have h := originalWholeGradedShiftAssociationHom PointedCGWH.loop loopPower
    PointedCGWH.piNPositiveFunctor nativeLoopGroupShiftNatIso loopPowerGroupShiftNatIso
    loopPowerZeroFunctorEq loopPowerSuccessorFunctorEq loopPower_add
    loopPowerGroupShiftNatIso_zero_clause loopPowerGroupShiftNatIso_succ_clause n m k X
  have hLeft : (loopPowerGroupAssociationNatIso n m k).hom.app X =
      (PointedCGWH.piNPositiveFunctor k).map
          (eqToHom (Functor.congr_obj (loopPower_add n m).symm X)) ≫
        (loopPowerGroupShiftNatIso (n + m) k).hom.app X :=
    congrArg (fun f => f ≫ (loopPowerGroupShiftNatIso (n + m) k).hom.app X)
      (originalWhiskeredInverseCastHom (PointedCGWH.piNPositiveFunctor k) (loopPower_add n m) X)
  have hRight := originalAssociatedShiftHom (loopPower n) (loopPower m)
    (PointedCGWH.piNPositiveFunctor k) (loopPowerGroupShiftNatIso m k)
    (loopPowerGroupShiftNatIso n (k + m))
    (congrArg PointedCGWH.piNPositiveFunctor
      (show k + m + n = k + (n + m) by omega)) X
  exact hLeft.trans (h.trans hRight.symm)

/-- The full source/target positive-group index comparison is the original exact equality Iso. -/
def groupAssociationIndexNatIso (n m k : ℕ) :
    PointedCGWH.piNPositiveFunctor.{u, v} (k + m + n) ≅
      PointedCGWH.piNPositiveFunctor (k + (n + m)) :=
  eqToIso (congrArg PointedCGWH.piNPositiveFunctor
    (show k + m + n = k + (n + m) by omega))

/-- Every actual original forward group comparison map retains the entire associated function. -/
theorem loopPowerGroupAssociation_hom (n m k : ℕ) (X : PointedCGWH.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).map ((loopPowerAddNatIso n m).inv.app X) ≫
        (loopPowerGroupShiftNatIso (n + m) k).hom.app X =
      (loopPowerGroupShiftNatIso m k).hom.app ((loopPower n).obj X) ≫
        (loopPowerGroupShiftNatIso n (k + m)).hom.app X ≫
          (groupAssociationIndexNatIso n m k).hom.app X :=
  congrArg (fun e => e.hom.app X) (loopPowerGroupAssociationNatIso_eq n m k)

/-- Every actual original inverse group comparison map retains the entire associated function. -/
theorem loopPowerGroupAssociation_inv (n m k : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerGroupShiftNatIso (n + m) k).inv.app X ≫
        (PointedCGWH.piNPositiveFunctor k).map ((loopPowerAddNatIso n m).hom.app X) =
      (groupAssociationIndexNatIso n m k).inv.app X ≫
        (loopPowerGroupShiftNatIso n (k + m)).inv.app X ≫
          (loopPowerGroupShiftNatIso m k).inv.app ((loopPower n).obj X) :=
  congrArg (fun e => e.inv.app X) (loopPowerGroupAssociationNatIso_eq n m k)

/-- All whole original pointed maps retain the full forward associated group naturality. -/
theorem loopPowerGroupAssociation_hom_naturality (n m k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor k).map ((loopPower m).map ((loopPower n).map f)) ≫
        (loopPowerGroupAssociationNatIso n m k).hom.app Y =
      (loopPowerGroupAssociationNatIso n m k).hom.app X ≫
        (PointedCGWH.piNPositiveFunctor (k + (n + m))).map f :=
  (loopPowerGroupAssociationNatIso n m k).hom.naturality f

/-- All whole original pointed maps retain the full inverse associated group naturality. -/
theorem loopPowerGroupAssociation_inv_naturality (n m k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (k + (n + m))).map f ≫
        (loopPowerGroupAssociationNatIso n m k).inv.app Y =
      (loopPowerGroupAssociationNatIso n m k).inv.app X ≫
        (PointedCGWH.piNPositiveFunctor k).map ((loopPower m).map ((loopPower n).map f)) :=
  (loopPowerGroupAssociationNatIso n m k).inv.naturality f

end PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyAssociationGeometry
