/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates

/-!
# Comparison refinement normalization in integral frames

This module proves that a modification of `G`-bundles read in integral frames
is left multiplication by its comparison element.

Source: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicHeckeCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates
open AnalyticTorsorPullbacks
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

private theorem leftInv_mul (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (T : Site p E Q.puncture.space)
    (a b : (pointGroups p E G).obj (op T.left)) :
    (left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) (a * b)
      = ((bundleActions p E G H X).obj M.left).action.app
          (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X))
          ((left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)))
              a, b) := by
  have hreg : (regularAction p E G H Q.space).action.app
      (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)) (a, b) = a * b := rfl
  have hprop := left.inv.property (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)) a b
  rw [hreg] at hprop
  exact hprop
private theorem groupTransportL (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space)
    (g : (pointGroups p E G).obj (op T.left)) :
    (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op g = g := by
  have hforget : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q
      T).symm) = 𝟙 T.left := by
    rw [eqToHom_map]
    simp
  have h1 : (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op g
      = ((groupSheaf p E G X (H X)).obj.map (eqToHom (refined_puncture_test_equality p E d U Q
          T).symm).op).hom g := rfl
  rw [h1]
  have hgm : (groupSheaf p E G X (H X)).obj.map (eqToHom (refined_puncture_test_equality p E d
      U Q T).symm).op
      = (pointGroups p E G).map (((Over.forget X).map (eqToHom (refined_puncture_test_equality
          p E d U Q T).symm)).op) := rfl
  rw [hgm, hforget]
  simp
  rfl
private theorem transportLeft_action (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (y : ((bundleActions p E G H X).obj M.left).sheaf.obj.obj
      (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)))
    (g : (pointGroups p E G).obj (op T.left)) :
    ((forgetBundles p E G H X).obj M.left).obj.map
        (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
        (((bundleActions p E G H X).obj M.left).action.app
          (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)) (y, g))
      = ((bundleActions p E G H X).obj M.left).action.app
          (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X))
          (((forgetBundles p E G H X).obj M.left).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op y, g) := by
  have hnat := ((bundleActions p E G H X).obj M.left).action.naturality
    (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
  have hcongr := congrArg (fun (h : (pairs (((bundleActions p E G H X).obj M.left).sheaf.obj)
      (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj).obj
        (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)) ⟶
      (((bundleActions p E G H X).obj M.left).sheaf.obj.obj
        (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)))) => h (y, g)) hnat
  have hcongr2 : ((bundleActions p E G H X).obj M.left).action.app
          (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X))
          (((forgetBundles p E G H X).obj M.left).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op y,
          (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op g)
      = ((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
          (((bundleActions p E G H X).obj M.left).action.app
            (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)) (y, g)) := hcongr
  have hgroup := groupTransportL p E G H d U Q T g
  rw [hgroup] at hcongr2
  exact hcongr2.symm
private theorem modPreserves_action (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (z : ((bundleActions p E G H X).obj M.left).sheaf.obj.obj
      (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)))
    (g : (pointGroups p E G).obj (op T.left)) :
    ((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
        (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space))
        (((bundleActions p E G H X).obj M.left).action.app
          (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)) (z, g))
      = ((bundleActions p E G H X).obj M.right).action.app
          (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X))
          (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
            (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space)) z, g) := by
  have hprop := ((bundleActions p E G H U.space).map M.punctured.hom).property
    (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space)) z g
  exact hprop
private theorem groupTransportR (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space)
    (g : (pointGroups p E G).obj (op T.left)) :
    (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T)).op g = g := by
  have hforget : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q T)) =
      𝟙 T.left := by
    rw [eqToHom_map]
    simp
  have h1 : (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T)).op g
      = ((groupSheaf p E G X (H X)).obj.map (eqToHom (refined_puncture_test_equality p E d U Q
          T)).op).hom g := rfl
  rw [h1]
  have hgm : (groupSheaf p E G X (H X)).obj.map (eqToHom (refined_puncture_test_equality p E d
      U Q T)).op
      = (pointGroups p E G).map (((Over.forget X).map (eqToHom (refined_puncture_test_equality
          p E d U Q T))).op) := rfl
  rw [hgm, hforget]
  simp
  rfl
private theorem transportRight_action (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (w : ((bundleActions p E G H X).obj M.right).sheaf.obj.obj
      (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)))
    (g : (pointGroups p E G).obj (op T.left)) :
    ((forgetBundles p E G H X).obj M.right).obj.map
        (eqToHom (refined_puncture_test_equality p E d U Q T)).op
        (((bundleActions p E G H X).obj M.right).action.app
          (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)) (w, g))
      = ((bundleActions p E G H X).obj M.right).action.app
          (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X))
          (((forgetBundles p E G H X).obj M.right).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T)).op w, g) := by
  have hnat := ((bundleActions p E G H X).obj M.right).action.naturality
    (eqToHom (refined_puncture_test_equality p E d U Q T)).op
  have hcongr := congrArg (fun (h : (pairs (((bundleActions p E G H X).obj M.right).sheaf.obj)
      (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj).obj
        (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)) ⟶
      (((bundleActions p E G H X).obj M.right).sheaf.obj.obj
        (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)))) => h (w, g)) hnat
  have hcongr2 : ((bundleActions p E G H X).obj M.right).action.app
          (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X))
          (((forgetBundles p E G H X).obj M.right).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T)).op w,
          (groupSets (topology p E X) (groupSheaf p E G X (H X))).obj.map
            (eqToHom (refined_puncture_test_equality p E d U Q T)).op g)
      = ((forgetBundles p E G H X).obj M.right).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T)).op
          (((bundleActions p E G H X).obj M.right).action.app
            (op (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X)) (w, g)) := hcongr
  have hgroup := groupTransportR p E G H d U Q T g
  rw [hgroup] at hcongr2
  exact hcongr2.symm
private theorem rightHom_mul (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space)
    (v : ((bundleActions p E G H X).obj M.right).sheaf.obj.obj
      (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)))
    (g : (pointGroups p E G).obj (op T.left)) :
    let localTest : Site p E Q.space := Over.mk (T.hom ≫ Q.puncture.map)
    let leftTest : Site p E X := Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map)
    let x : (pointGroups p E G).obj (op T.left) :=
      (right.hom.val.hom.app (op localTest)) v
    let z : (pointGroups p E G).obj (op T.left) :=
      (right.hom.val.hom.app (op localTest))
        (((bundleActions p E G H X).obj M.right).action.app (op leftTest) (v, g))
    z = x * g := by
  intro localTest leftTest x z
  have hprop := right.hom.property (op localTest) v g
  have hreg : (regularAction p E G H Q.space).action.app (op localTest)
      ((right.hom.val.hom.app (op localTest)) v, g) = x * g := rfl
  exact hprop.trans hreg
private theorem comparisonValue_mul (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space)
    (a b : (pointGroups p E G).obj (op T.left)) :
    comparisonValue p E G H P d U Q M left right T (a * b)
      = comparisonValue p E G H P d U Q M left right T a * b := by
  unfold comparisonValue
  dsimp
  rw [leftInv_mul p E G H P d U Q M left T a b]
  rw [transportLeft_action p E G H P d U Q M T
    ((left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) a) b]
  rw [modPreserves_action p E G H P d U Q M T
    (((forgetBundles p E G H X).obj M.left).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
      ((left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) a)) b]
  rw [transportRight_action p E G H P d U Q M T
    (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
      (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space))
      (((forgetBundles p E G H X).obj M.left).obj.map
        (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
        ((left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) a))) b]
  have h5 := rightHom_mul p E G H P d U Q M right T
    (((forgetBundles p E G H X).obj M.right).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q T)).op
      (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
        (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space))
        (((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
          ((left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) a)))) b
  exact h5
private noncomputable def localMor (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space) ⟶
      Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) :=
  Over.homMk T.hom (by simp)
private noncomputable def originalMor (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space) ⟶
      Over.mk (𝟙 Q.puncture.space ≫ Q.punctureToOriginal) :=
  Over.homMk T.hom (by simp)
private noncomputable def leftMor (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X) ⟶
      Over.mk ((𝟙 Q.puncture.space ≫ Q.puncture.map) ≫ Q.map) :=
  Over.homMk T.hom (by simp)
private noncomputable def rightMor (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X) ⟶
      Over.mk ((𝟙 Q.puncture.space ≫ Q.punctureToOriginal) ≫ U.map) :=
  Over.homMk T.hom (by simp)
private theorem leftInv_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (T : Site p E Q.puncture.space)
    (a : (pointGroups p E G).obj (op Q.puncture.space)) :
    (left.inv.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)))
        (((pointGroups p E G).map T.hom.op).hom a)
      = ((forgetBundles p E G H X).obj M.left).obj.map
          (leftMor p E d U Q T).op
          ((left.inv.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
              Q.space))) a) := by
  have hnat := (left.inv.val.hom.naturality (localMor p E d U Q T).op)
  have hcongr := congrArg (fun (h : (regularAction p E G H Q.space).sheaf.obj.obj
      (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E Q.space)) ⟶
      (((actionPullback p E G Q.map (H X) (H Q.space)).obj
        ((bundleActions p E G H X).obj M.left)).sheaf.obj.obj
        (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)))) => h a) hnat
  exact hcongr
private theorem overCommLeft (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    rightMor p E d U Q T ≫ eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
        Q.puncture.space))).symm
      = eqToHom (refined_puncture_test_equality p E d U Q T).symm ≫ leftMor p E d U Q T := by
  apply Over.OverMorphism.ext
  have hforgetT : Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q T).symm) =
      𝟙 T.left := by
    have h : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q T).symm) =
        𝟙 T.left := by
      rw [eqToHom_map]
      simp
    exact h
  have hforgetId : Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk
      (𝟙 Q.puncture.space))).symm) = 𝟙 Q.puncture.space := by
    have h : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk
        (𝟙 Q.puncture.space))).symm) = 𝟙 Q.puncture.space := by
      rw [eqToHom_map]
      simp
    exact h
  have hleft : Over.Hom.left (leftMor p E d U Q T) = T.hom := rfl
  have hright : Over.Hom.left (rightMor p E d U Q T) = T.hom := rfl
  change Over.Hom.left (rightMor p E d U Q T) ≫ Over.Hom.left (eqToHom
      (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space))).symm)
    = Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q T).symm) ≫
        Over.Hom.left (leftMor p E d U Q T)
  rw [hright, hforgetId, hforgetT, hleft]
  simp
private theorem overCommRight (p : ℕ) (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (T : Site p E Q.puncture.space) :
    leftMor p E d U Q T ≫ eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
        Q.puncture.space)))
      = eqToHom (refined_puncture_test_equality p E d U Q T) ≫ rightMor p E d U Q T := by
  apply Over.OverMorphism.ext
  have hforgetT : Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q T)) = 𝟙
      T.left := by
    have h : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q T)) = 𝟙
        T.left := by
      rw [eqToHom_map]
      simp
    exact h
  have hforgetId : Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk
      (𝟙 Q.puncture.space)))) = 𝟙 Q.puncture.space := by
    have h : (Over.forget X).map (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk
        (𝟙 Q.puncture.space)))) = 𝟙 Q.puncture.space := by
      rw [eqToHom_map]
      simp
    exact h
  have hleft : Over.Hom.left (leftMor p E d U Q T) = T.hom := rfl
  have hright : Over.Hom.left (rightMor p E d U Q T) = T.hom := rfl
  change Over.Hom.left (leftMor p E d U Q T) ≫ Over.Hom.left (eqToHom
      (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space))))
    = Over.Hom.left (eqToHom (refined_puncture_test_equality p E d U Q T)) ≫ Over.Hom.left
        (rightMor p E d U Q T)
  rw [hleft, hforgetId, hforgetT, hright]
  simp
private theorem trL_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (y : ((bundleActions p E G H X).obj M.left).sheaf.obj.obj
      (op (Over.mk ((𝟙 Q.puncture.space ≫ Q.puncture.map) ≫ Q.map) : Site p E X))) :
    ((forgetBundles p E G H X).obj M.left).obj.map
        (rightMor p E d U Q T).op
        (((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
              Q.puncture.space))).symm).op y)
      = ((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
          (((forgetBundles p E G H X).obj M.left).obj.map (leftMor p E d U Q T).op y) := by
  have hover := overCommLeft p E d U Q T
  have hop : (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
      Q.puncture.space))).symm).op ≫ (rightMor p E d U Q T).op
      = (leftMor p E d U Q T).op ≫ (eqToHom (refined_puncture_test_equality p E d U Q
          T).symm).op := by
    have h := congrArg (fun (f : (Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) : Site p E
        X) ⟶ Over.mk ((𝟙 Q.puncture.space ≫ Q.puncture.map) ≫ Q.map)) => f.op) hover
    simpa [op_comp] using h
  have hLHS : ((forgetBundles p E G H X).obj M.left).obj.map
        (rightMor p E d U Q T).op
        (((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
              Q.puncture.space))).symm).op y)
      = ((forgetBundles p E G H X).obj M.left).obj.map
          ((eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
              Q.puncture.space))).symm).op ≫ (rightMor p E d U Q T).op) y := by
    rw [Functor.map_comp]
    rfl
  have hRHS : ((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T).symm).op
          (((forgetBundles p E G H X).obj M.left).obj.map (leftMor p E d U Q T).op y)
      = ((forgetBundles p E G H X).obj M.left).obj.map
          ((leftMor p E d U Q T).op ≫ (eqToHom (refined_puncture_test_equality p E d U Q
              T).symm).op) y := by
    rw [Functor.map_comp]
    rfl
  rw [hLHS, hRHS, hop]
private theorem trR_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (w : ((bundleActions p E G H X).obj M.right).sheaf.obj.obj
      (op (Over.mk ((𝟙 Q.puncture.space ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X))) :
    ((forgetBundles p E G H X).obj M.right).obj.map
        (leftMor p E d U Q T).op
        (((forgetBundles p E G H X).obj M.right).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space)))).op w)
      = ((forgetBundles p E G H X).obj M.right).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T)).op
          (((forgetBundles p E G H X).obj M.right).obj.map (rightMor p E d U Q T).op w) := by
  have hover := overCommRight p E d U Q T
  have hop : (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
      Q.puncture.space)))).op ≫ (leftMor p E d U Q T).op
      = (rightMor p E d U Q T).op ≫ (eqToHom (refined_puncture_test_equality p E d U Q T)).op := by
    have h := congrArg (fun (f : (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X) ⟶
        Over.mk ((𝟙 Q.puncture.space ≫ Q.punctureToOriginal) ≫ U.map)) => f.op) hover
    simpa [op_comp] using h
  have hLHS : ((forgetBundles p E G H X).obj M.right).obj.map
        (leftMor p E d U Q T).op
        (((forgetBundles p E G H X).obj M.right).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space)))).op w)
      = ((forgetBundles p E G H X).obj M.right).obj.map
          ((eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
              Q.puncture.space)))).op ≫ (leftMor p E d U Q T).op) w := by
    rw [Functor.map_comp]
    rfl
  have hRHS : ((forgetBundles p E G H X).obj M.right).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q T)).op
          (((forgetBundles p E G H X).obj M.right).obj.map (rightMor p E d U Q T).op w)
      = ((forgetBundles p E G H X).obj M.right).obj.map
          ((rightMor p E d U Q T).op ≫ (eqToHom (refined_puncture_test_equality p E d U Q
              T)).op) w := by
    rw [Functor.map_comp]
    rfl
  rw [hLHS, hRHS, hop]
private theorem mod_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (T : Site p E Q.puncture.space)
    (z : ((bundleActions p E G H X).obj M.left).sheaf.obj.obj
      (op (Over.mk ((𝟙 Q.puncture.space ≫ Q.punctureToOriginal) ≫ U.map) : Site p E X))) :
    ((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
        (op (Over.mk (T.hom ≫ Q.punctureToOriginal) : Site p E U.space))
        (((forgetBundles p E G H X).obj M.left).obj.map (rightMor p E d U Q T).op z)
      = ((forgetBundles p E G H X).obj M.right).obj.map (rightMor p E d U Q T).op
          (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
            (op (Over.mk (𝟙 Q.puncture.space ≫ Q.punctureToOriginal) : Site p E U.space)) z) := by
  have hnat := ((forgetBundles p E G H U.space).map M.punctured.hom).hom.naturality
    (originalMor p E d U Q T).op
  have hcongr := congrArg (fun h => h z) hnat
  exact hcongr
private theorem rightHom_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space)
    (v : ((bundleActions p E G H X).obj M.right).sheaf.obj.obj
      (op (Over.mk ((𝟙 Q.puncture.space ≫ Q.puncture.map) ≫ Q.map) : Site p E X))) :
    let x_id : (pointGroups p E G).obj (op Q.puncture.space) :=
      (right.hom.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
          Q.space))) v
    let v_T : ((bundleActions p E G H X).obj M.right).sheaf.obj.obj
        (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X)) :=
      ((forgetBundles p E G H X).obj M.right).obj.map (leftMor p E d U Q T).op v
    let x_T : (pointGroups p E G).obj (op T.left) :=
      (right.hom.val.hom.app (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space))) v_T
    x_T = ((pointGroups p E G).map T.hom.op).hom x_id := by
  intro x_id v_T x_T
  have hnat := (right.hom.val.hom.naturality (localMor p E d U Q T).op)
  have hcongr := congrArg (fun (h : (((actionPullback p E G Q.map (H X) (H Q.space)).obj
        ((bundleActions p E G H X).obj M.right)).sheaf.obj.obj
        (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E Q.space)) ⟶
      (regularAction p E G H Q.space).sheaf.obj.obj
        (op (Over.mk (T.hom ≫ Q.puncture.map) : Site p E Q.space)))) => h v) hnat
  exact hcongr
private theorem comparisonValue_one_natural (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space) :
    comparisonValue p E G H P d U Q M left right T 1
      = ((pointGroups p E G).map T.hom.op).hom
          (comparisonElement p E G H P d U Q M left right) := by
  have hElem : comparisonElement p E G H P d U Q M left right
      = comparisonValue p E G H P d U Q M left right (Over.mk (𝟙 Q.puncture.space)) 1 := rfl
  rw [hElem]
  unfold comparisonValue
  dsimp
  have hone : (1 : (pointGroups p E G).obj (op T.left))
      = ((pointGroups p E G).map T.hom.op).hom 1 := by simp
  rw [hone]
  rw [leftInv_natural p E G H P d U Q M left T 1]
  rw [← trL_natural p E G H P d U Q M T
    ((left.inv.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
        Q.space))) (1 : (pointGroups p E G).obj (op Q.puncture.space)))]
  rw [mod_natural p E G H P d U Q M T
    (((forgetBundles p E G H X).obj M.left).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space))).symm).op
      ((left.inv.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
          Q.space))) (1 : (pointGroups p E G).obj (op Q.puncture.space))))]
  rw [← trR_natural p E G H P d U Q M T
    (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
      (op (Over.mk (𝟙 Q.puncture.space ≫ Q.punctureToOriginal) : Site p E U.space))
      (((forgetBundles p E G H X).obj M.left).obj.map
        (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space))).symm).op
        ((left.inv.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
            Q.space))) (1 : (pointGroups p E G).obj (op Q.puncture.space)))))]
  have h5 := rightHom_natural p E G H P d U Q M right T
    (((forgetBundles p E G H X).obj M.right).obj.map
      (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙 Q.puncture.space)))).op
      (((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
        (op (Over.mk (𝟙 Q.puncture.space ≫ Q.punctureToOriginal) : Site p E U.space))
        (((forgetBundles p E G H X).obj M.left).obj.map
          (eqToHom (refined_puncture_test_equality p E d U Q (Over.mk (𝟙
              Q.puncture.space))).symm).op
          ((left.inv.val.hom.app (op (Over.mk (𝟙 Q.puncture.space ≫ Q.puncture.map) : Site p E
              Q.space))) (1 : (pointGroups p E G).obj (op Q.puncture.space))))))
  exact h5
private theorem comparisonValue_one_mul (p : ℕ) (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space)
    (a : (pointGroups p E G).obj (op T.left)) :
    comparisonValue p E G H P d U Q M left right T a
      = comparisonValue p E G H P d U Q M left right T 1 * a := by
  have h1 : comparisonValue p E G H P d U Q M left right T a
      = comparisonValue p E G H P d U Q M left right T (1 * a) := by rw [one_mul]
  rw [h1]
  exact comparisonValue_mul p E G H P d U Q M left right T 1 a
/-- In integral frames, a modification of $G$-bundles is left multiplication by its comparison
element: let $p$ be a prime, $E$ a field and $G$ a group scheme over $E$ (with the given
torsor-descent data `H` and pullback preservation `P`), $d : D \to X$ a map of analytic spaces over
$E$ with puncture $U$ (the open complement of its image), $Q$ a pole chart of $d$, $M$ a
modification of $G$-bundles along $d$ (an isomorphism over $U$ between two $G$-bundles on $X$), and
integral frames of the two bundles of $M$ on $Q$. Then on every test object $T$ over the punctured
chart, the isomorphism of $M$ read in the two frames sends each $a \in G(T)$ to $g|_T \cdot a$,
where $g$ is the comparison element (`comparisonElement`). -/
public theorem comparison_refinement_normalization
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space) (a : (pointGroups p E G).obj (op T.left)) :
    comparisonValue p E G H P d U Q M left right T a =
      ((pointGroups p E G).map T.hom.op).hom
        (comparisonElement p E G H P d U Q M left right) * a := by
  have h1 := comparisonValue_one_mul p E G H P d U Q M left right T a
  have h2 := comparisonValue_one_natural p E G H P d U Q M left right T
  rw [h1, h2]
end WantedExt.AlgebraicGeometry.MeromorphicHeckeCoordinates
