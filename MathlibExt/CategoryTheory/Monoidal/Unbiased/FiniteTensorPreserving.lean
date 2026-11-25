/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor

/-!
# Functors preserving unbiased finite tensors

A strong finite-tensor-preserving functor carries the tensor of a finite family to the tensor of
its image, compatibly with singleton families and flattening. These coherences induce functors on
operad objects.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.FiniteTensor

open CategoryTheory
open CategoryTheory.FiniteFamily

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [FiniteTensor V] [FiniteTensor W]

/-- Strong finite-tensor-preserving functor.

The comparison is oriented as
`map F ⋙ tensor_W ≅ tensor_V ⋙ F`, i.e. the tensor of `F`-images is
identified with `F` of the tensor. The two coherences are the
pseudoalgebra morphism laws for the finite-family monad, expressed
with the existing `singletonMapIso`, `flattenMapIso`, `mapIso`,
`mapCompIso` as the explicit functor-composition coherence,
`isoWhiskerLeft` and `isoWhiskerRight` APIs. -/
structure Preserving (F : V ⥤ W) where
  /-- Comparison iso `map F ⋙ tensor_W ≅ tensor_V ⋙ F`. -/
  comparisonIso :
    FiniteFamily.map F ⋙
        _root_.CategoryTheory.FiniteTensor.tensor (V := W) ≅
      _root_.CategoryTheory.FiniteTensor.tensor (V := V) ⋙ F
  /-- Compatibility with `singletonIso`. -/
  singleton_compat :
    Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft F
        (_root_.CategoryTheory.FiniteTensor.singletonIso (V := W)) ≪≫
      Functor.rightUnitor F =
    Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
        comparisonIso ≪≫
      Functor.isoWhiskerRight
        (_root_.CategoryTheory.FiniteTensor.singletonIso (V := V)) F ≪≫
      Functor.leftUnitor F
  /-- Compatibility with `flattenIso`. -/
  flatten_compat :
    Functor.isoWhiskerLeft (FiniteFamily.flatten (C := V))
        comparisonIso ≪≫
      Functor.isoWhiskerRight
        (_root_.CategoryTheory.FiniteTensor.flattenIso (V := V)) F =
    Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
        (_root_.CategoryTheory.FiniteTensor.flattenIso (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso (FiniteFamily.map F)
          (_root_.CategoryTheory.FiniteTensor.tensor (V := W))).symm
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso comparisonIso)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso
          (_root_.CategoryTheory.FiniteTensor.tensor (V := V)) F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft
        (FiniteFamily.map
          (_root_.CategoryTheory.FiniteTensor.tensor (V := V)))
        comparisonIso

namespace Preserving

/-- Finite-tensor-preserving structures are determined by their comparison isomorphisms. -/
@[ext]
theorem ext {F : V ⥤ W} {p q : Preserving F}
    (h : p.comparisonIso = q.comparisonIso) : p = q := by
  cases p
  cases q
  cases h
  rfl

variable {F : V ⥤ W} (p : Preserving F)

/-- Component form of `singleton_compat` at an object. -/
lemma singleton_compat_hom_app (X : V) :
    (Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft F
        (_root_.CategoryTheory.FiniteTensor.singletonIso (V := W)) ≪≫
      Functor.rightUnitor F).hom.app X =
    (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
        p.comparisonIso ≪≫
      Functor.isoWhiskerRight
        (_root_.CategoryTheory.FiniteTensor.singletonIso (V := V)) F ≪≫
      Functor.leftUnitor F).hom.app X := by
  have h := p.singleton_compat
  exact congrArg (fun iso : _ => iso.hom.app X) h

/-- Component form of `flatten_compat` at a double family. -/
lemma flatten_compat_hom_app (X : FiniteFamily (FiniteFamily V)) :
    (Functor.isoWhiskerLeft (FiniteFamily.flatten (C := V))
        p.comparisonIso ≪≫
      Functor.isoWhiskerRight
        (_root_.CategoryTheory.FiniteTensor.flattenIso (V := V)) F).hom.app X =
    (Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
        (_root_.CategoryTheory.FiniteTensor.flattenIso (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso (FiniteFamily.map F)
          (_root_.CategoryTheory.FiniteTensor.tensor (V := W))).symm
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso p.comparisonIso)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso
          (_root_.CategoryTheory.FiniteTensor.tensor (V := V)) F)
        (_root_.CategoryTheory.FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft
        (FiniteFamily.map
          (_root_.CategoryTheory.FiniteTensor.tensor (V := V)))
        p.comparisonIso).hom.app X := by
  have h := p.flatten_compat
  exact congrArg (fun iso : _ => iso.hom.app X) h

omit [FiniteTensor V] in
private theorem singleton_compat_left_reduced {F : V ⥤ W} (X : V) :
    (Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
          (FiniteTensor.tensor (V := W)) ≪≫
        Functor.isoWhiskerLeft F
          (FiniteTensor.singletonIso (V := W)) ≪≫
        Functor.rightUnitor F).hom.app X =
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
  let singletonW :=
    (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X)
  have hMap :
      (Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
        (FiniteTensor.tensor (V := W))).hom.app X = 𝟙 _ := by
    change (FiniteTensor.tensor (V := W)).map
      ((FiniteFamily.singletonMapIso F).hom.app X) = 𝟙 _
    have hSingleton : (FiniteFamily.singletonMapIso F).hom.app X = 𝟙 _ := by
      with_unfolding_all rfl
    rw [hSingleton]
    exact (FiniteTensor.tensor (V := W)).map_id _
  have hSingleton :
      (Functor.isoWhiskerLeft F
        (FiniteTensor.singletonIso (V := W))).hom.app X = singletonW := rfl
  have hUnitor : (Functor.rightUnitor F).hom.app X = 𝟙 _ := rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, hMap, hSingleton, hUnitor]
  calc
    𝟙 _ ≫ singletonW ≫ 𝟙 _ = 𝟙 _ ≫ singletonW := by
      simp only [Category.comp_id]
    _ = singletonW := by
      simp only [Category.id_comp]

private theorem singleton_compat_right_reduced {F : V ⥤ W}
    (comparisonIso :
      FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W) ≅
        FiniteTensor.tensor (V := V) ⋙ F)
    (X : V) :
    (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
          comparisonIso ≪≫
        Functor.isoWhiskerRight
          (FiniteTensor.singletonIso (V := V)) F ≪≫
        Functor.leftUnitor F).hom.app X =
      comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) := by
  let comparison :=
    comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X)
  let singletonV := F.map ((FiniteTensor.singletonIso (V := V)).hom.app X)
  have hComparison :
      (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
        comparisonIso).hom.app X = comparison := rfl
  have hSingleton :
      (Functor.isoWhiskerRight
        (FiniteTensor.singletonIso (V := V)) F).hom.app X = singletonV := rfl
  have hUnitor : (Functor.leftUnitor F).hom.app X = 𝟙 _ := rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, hComparison, hSingleton, hUnitor]
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id]
  with_unfolding_all rfl

private theorem flatten_compat_left_reduced {F : V ⥤ W}
    (comparisonIso :
      FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W) ≅
        FiniteTensor.tensor (V := V) ⋙ F)
    (X : FiniteFamily (FiniteFamily V)) :
    (Functor.isoWhiskerLeft (FiniteFamily.flatten (C := V))
          comparisonIso ≪≫
        Functor.isoWhiskerRight
          (FiniteTensor.flattenIso (V := V)) F).hom.app X =
      comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
        F.map ((FiniteTensor.flattenIso (V := V)).hom.app X) := by
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]

private theorem flatten_compat_right_reduced {F : V ⥤ W}
    (comparisonIso :
      FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W) ≅
        FiniteTensor.tensor (V := V) ⋙ F)
    (X : FiniteFamily (FiniteFamily V)) :
    (Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
          (FiniteTensor.tensor (V := W)) ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
          (FiniteTensor.flattenIso (V := W)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.mapCompIso (FiniteFamily.map F)
            (FiniteTensor.tensor (V := W))).symm
          (FiniteTensor.tensor (V := W)) ≪≫
        Functor.isoWhiskerRight (FiniteFamily.mapIso comparisonIso)
          (FiniteTensor.tensor (V := W)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.mapCompIso
            (FiniteTensor.tensor (V := V)) F)
          (FiniteTensor.tensor (V := W)) ≪≫
        Functor.isoWhiskerLeft
          (FiniteFamily.map (FiniteTensor.tensor (V := V)))
          comparisonIso).hom.app X =
      (FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
        (FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.mapIso comparisonIso).hom.app X) ≫
        comparisonIso.hom.app
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) := by
  have hLead :
      (Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
        (FiniteTensor.tensor (V := W))).hom.app X =
        𝟙 (((FiniteFamily.map (FiniteFamily.map F) ⋙
              FiniteFamily.flatten (C := W)) ⋙
            FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hBridge1 :
      (Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso (FiniteFamily.map F)
          (FiniteTensor.tensor (V := W))).symm
        (FiniteTensor.tensor (V := W))).hom.app X =
        𝟙 ((FiniteFamily.map
              (FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)) ⋙
            FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hBridge2 :
      (Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso
          (FiniteTensor.tensor (V := V)) F)
        (FiniteTensor.tensor (V := W))).hom.app X =
        𝟙 ((FiniteFamily.map (FiniteTensor.tensor (V := V)) ⋙
            FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hFlatten :
      (Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
        (FiniteTensor.flattenIso (V := W))).hom.app X =
        (FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj X) := by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hMapComparison :
      (Functor.isoWhiskerRight (FiniteFamily.mapIso comparisonIso)
        (FiniteTensor.tensor (V := W))).hom.app X =
        (FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.mapIso comparisonIso).hom.app X) := by
    simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have hComparison :
      (Functor.isoWhiskerLeft
        (FiniteFamily.map (FiniteTensor.tensor (V := V)))
        comparisonIso).hom.app X =
        comparisonIso.hom.app
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) := by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  erw [hLead, hFlatten, hBridge1, hMapComparison, hBridge2, hComparison]
  with_unfolding_all
    erw [← Category.assoc]
    erw [← Category.assoc]
    erw [← Category.assoc]
    erw [← Category.assoc]
    change ((((𝟙 (((FiniteFamily.map (FiniteFamily.map F) ⋙
              FiniteFamily.flatten (C := W)) ⋙
            FiniteTensor.tensor (V := W)).obj X) ≫
            (FiniteTensor.flattenIso (V := W)).hom.app
              ((FiniteFamily.map (FiniteFamily.map F)).obj X)) ≫
            𝟙 ((FiniteFamily.map (FiniteTensor.tensor (V := W)) ⋙
                FiniteTensor.tensor (V := W)).obj
              ((FiniteFamily.map (FiniteFamily.map F)).obj X))) ≫
            (FiniteTensor.tensor (V := W)).map
              ((FiniteFamily.mapIso comparisonIso).hom.app X)) ≫
            𝟙 ((FiniteTensor.tensor (V := W)).obj
              ((FiniteFamily.map
                (FiniteTensor.tensor (V := V) ⋙ F)).obj X))) ≫
            comparisonIso.hom.app
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
          (FiniteTensor.flattenIso (V := W)).hom.app
              ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
            (FiniteTensor.tensor (V := W)).map
              ((FiniteFamily.mapIso comparisonIso).hom.app X) ≫
            comparisonIso.hom.app
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X)
    simp only [Category.id_comp, Category.comp_id]
    exact Category.assoc
      ((FiniteTensor.flattenIso (V := W)).hom.app
        ((FiniteFamily.map (FiniteFamily.map F)).obj X))
      ((FiniteTensor.tensor (V := W)).map
        ((FiniteFamily.mapIso comparisonIso).hom.app X))
      (comparisonIso.hom.app
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X))

/-- Build a finite-tensor-preserving functor from componentwise singleton and flattening laws. -/
def mkOfComponents {F : V ⥤ W}
    (comparisonIso :
      FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W) ≅
        FiniteTensor.tensor (V := V) ⋙ F)
    (singleton_hom : ∀ X : V,
      comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X))
    (flatten_hom : ∀ X : FiniteFamily (FiniteFamily V),
      (FiniteTensor.flattenIso (V := W)).hom.app
            ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
          (FiniteTensor.tensor (V := W)).map
            ((FiniteFamily.mapIso comparisonIso).hom.app X) ≫
          comparisonIso.hom.app
            ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
        comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
          F.map ((FiniteTensor.flattenIso (V := V)).hom.app X)) :
    Preserving F where
  comparisonIso := comparisonIso
  singleton_compat := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    have hLeft := singleton_compat_left_reduced (F := F) X
    have hRight := singleton_compat_right_reduced comparisonIso X
    exact hLeft.trans ((singleton_hom X).symm.trans hRight.symm)
  flatten_compat := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    have hLeft := flatten_compat_left_reduced comparisonIso X
    have hRight := flatten_compat_right_reduced comparisonIso X
    exact hLeft.trans ((flatten_hom X).symm.trans hRight.symm)

/-- The comparison at a singleton, followed by the mapped singleton comparison. -/
theorem comparisonIso_hom_app_singleton_comp (X : V) :
    p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
  have hCompat := p.singleton_compat_hom_app X
  have hLeft := singleton_compat_left_reduced (F := F) X
  have hRight := singleton_compat_right_reduced p.comparisonIso X
  exact hRight.symm.trans (hCompat.symm.trans hLeft)

/-- Componentwise flattening coherence with all definitional bridge isomorphisms removed. -/
theorem flatten_compat_reduced_hom_app (X : FiniteFamily (FiniteFamily V)) :
    (FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
        (FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.mapIso p.comparisonIso).hom.app X) ≫
        p.comparisonIso.hom.app
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
      p.comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
        F.map ((FiniteTensor.flattenIso (V := V)).hom.app X) := by
  have hCompat := p.flatten_compat_hom_app X
  have hLeft := flatten_compat_left_reduced p.comparisonIso X
  have hRight := flatten_compat_right_reduced p.comparisonIso X
  exact hRight.symm.trans (hCompat.symm.trans hLeft)

/-- The canonical finite-tensor comparison carried by the identity functor. -/
noncomputable def identityComparisonIso (V : Type u₁) [Category.{v₁} V]
    [FiniteTensor V] :
    FiniteFamily.map (𝟭 V) ⋙ FiniteTensor.tensor ≅
      FiniteTensor.tensor ⋙ 𝟭 V :=
  Functor.isoWhiskerRight (FiniteFamily.mapIdIso V) FiniteTensor.tensor ≪≫
    Functor.leftUnitor FiniteTensor.tensor ≪≫
    (Functor.rightUnitor FiniteTensor.tensor).symm

/-- The identity comparison has identity forward components. -/
@[simp]
theorem identityComparisonIso_hom_app (X : FiniteFamily V) :
    (identityComparisonIso V).hom.app X = 𝟙 _ := by
  have hBridge :
      (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).hom.app X) = 𝟙 _ := by
    rw [FiniteFamily.mapIdIso_hom_app]
    exact (FiniteTensor.tensor (V := V)).map_id X
  unfold identityComparisonIso
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Iso.symm_hom,
    Functor.rightUnitor_inv_app]
  have hReduced :
      ((FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).hom.app X) ≫
        𝟙 ((FiniteTensor.tensor (V := V)).obj X)) ≫
          𝟙 ((FiniteTensor.tensor (V := V)).obj X) =
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).hom.app X) := by
    exact (Category.comp_id _).trans (Category.comp_id _)
  exact (Category.assoc _ _ _).symm.trans (hReduced.trans hBridge)

/-- The identity comparison has identity inverse components. -/
@[simp]
theorem identityComparisonIso_inv_app (X : FiniteFamily V) :
    (identityComparisonIso V).inv.app X = 𝟙 _ := by
  have hBridge :
      (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).inv.app X) = 𝟙 _ := by
    rw [FiniteFamily.mapIdIso_inv_app]
    exact (FiniteTensor.tensor (V := V)).map_id X
  unfold identityComparisonIso
  simp only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app]
  have hReduced :
      (𝟙 ((FiniteTensor.tensor (V := V)).obj X) ≫
        𝟙 ((FiniteTensor.tensor (V := V)).obj X)) ≫
          (FiniteTensor.tensor (V := V)).map
            ((FiniteFamily.mapIdIso V).inv.app X) =
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).inv.app X) := by
    exact
      (congrArg
        (· ≫ (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIdIso V).inv.app X))
        (Category.id_comp (𝟙 ((FiniteTensor.tensor (V := V)).obj X)))).trans
      (Category.id_comp _)
  exact hReduced.trans hBridge

/-- The identity functor strongly preserves any fixed finite-tensor structure. -/
noncomputable def id (V : Type u₁) [Category.{v₁} V] [FiniteTensor V] :
    Preserving (𝟭 V) :=
  mkOfComponents (identityComparisonIso V)
    (fun X => by
      let singletonHom :=
        (FiniteTensor.singletonIso (V := V)).hom.app X
      have hMap : (𝟭 V).map singletonHom = singletonHom := rfl
      rw [identityComparisonIso_hom_app, hMap]
      exact Category.id_comp _)
    (fun X => by
      let flattenHom :=
        (FiniteTensor.flattenIso (V := V)).hom.app X
      let lhs0 := (FiniteTensor.flattenIso (V := V)).hom.app
        ((FiniteFamily.map (FiniteFamily.map (𝟭 V))).obj X)
      let lhs1 := (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.mapIso (identityComparisonIso V)).hom.app X)
      let lhs2 := (identityComparisonIso V).hom.app
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X)
      let rhs0 := (identityComparisonIso V).hom.app
        ((FiniteFamily.flatten (C := V)).obj X)
      let rhs1 := (𝟭 V).map flattenHom
      have hMapIso :
          (FiniteFamily.mapIso (identityComparisonIso V)).hom.app X = 𝟙 _ := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro i
          exact heq_of_eq (identityComparisonIso_hom_app (X.obj i))
      have hTensorMap :
          lhs1 = 𝟙 _ := by
        have h := congrArg (FiniteTensor.tensor (V := V)).map hMapIso
        exact h.trans ((FiniteTensor.tensor (V := V)).map_id _)
      have hFlatten :
          lhs0 = flattenHom := by
        with_unfolding_all rfl
      have hComparisonMapped : lhs2 = 𝟙 _ :=
        identityComparisonIso_hom_app _
      have hComparisonFlat : rhs0 = 𝟙 _ :=
        identityComparisonIso_hom_app _
      have hMap : rhs1 = flattenHom := rfl
      have h12 : lhs1 ≫ lhs2 = 𝟙 _ := by
        rw [hTensorMap, hComparisonMapped]
        with_unfolding_all
          exact Category.id_comp _
      have hLhs : lhs0 ≫ lhs1 ≫ lhs2 = flattenHom := by
        have h12' := congrArg (lhs0 ≫ ·) h12
        exact h12'.trans ((Category.comp_id lhs0).trans hFlatten)
      have hRhs : rhs0 ≫ rhs1 = flattenHom := by
        rw [hComparisonFlat, hMap]
        exact Category.id_comp _
      with_unfolding_all
        exact hLhs.trans hRhs.symm)

/-- The identity-preserving value uses the canonical identity comparison. -/
@[simp]
theorem id_comparisonIso (V : Type u₁) [Category.{v₁} V] [FiniteTensor V] :
    (id V).comparisonIso = identityComparisonIso V :=
  rfl

/-- The identity-preserving comparison has identity forward components. -/
@[simp]
theorem id_comparisonIso_hom_app (X : FiniteFamily V) :
    (id V).comparisonIso.hom.app X = 𝟙 _ :=
  identityComparisonIso_hom_app X

/-- The identity-preserving comparison has identity inverse components. -/
@[simp]
theorem id_comparisonIso_inv_app (X : FiniteFamily V) :
    (id V).comparisonIso.inv.app X = 𝟙 _ :=
  identityComparisonIso_inv_app X

/-- The comparison isomorphism for a composite of finite-tensor-preserving functors. -/
noncomputable def compComparisonIso
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G) :
    FiniteFamily.map (F ⋙ G) ⋙ FiniteTensor.tensor (V := U) ≅
      FiniteTensor.tensor (V := V) ⋙ F ⋙ G :=
  Functor.isoWhiskerRight (FiniteFamily.mapCompIso F G)
      (FiniteTensor.tensor (V := U)) ≪≫
    Functor.isoWhiskerLeft (FiniteFamily.map F) q.comparisonIso ≪≫
    Functor.isoWhiskerRight p.comparisonIso G

/-- Forward components of the composite comparison are the pasted comparisons. -/
@[simp]
theorem compComparisonIso_hom_app
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G)
    (X : FiniteFamily V) :
    (compComparisonIso p q).hom.app X =
      q.comparisonIso.hom.app ((FiniteFamily.map F).obj X) ≫
        G.map (p.comparisonIso.hom.app X) := by
  let bridge := (Functor.isoWhiskerRight (FiniteFamily.mapCompIso F G)
    (FiniteTensor.tensor (V := U))).hom.app X
  let qHom := q.comparisonIso.hom.app ((FiniteFamily.map F).obj X)
  let pHom := G.map (p.comparisonIso.hom.app X)
  have hBridge :
      bridge = 𝟙 _ := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := U)).map_id _
  have hDef : (compComparisonIso p q).hom.app X =
      bridge ≫ qHom ≫ pHom := by
    with_unfolding_all rfl
  let tail := qHom ≫ pHom
  have hCancel : bridge ≫ tail = tail := by
    rw [hBridge]
    with_unfolding_all
      exact Category.id_comp tail
  exact hDef.trans hCancel

/-- Inverse components of the composite comparison are the inverse pasted comparisons. -/
@[simp]
theorem compComparisonIso_inv_app
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G)
    (X : FiniteFamily V) :
    (compComparisonIso p q).inv.app X =
      G.map (p.comparisonIso.inv.app X) ≫
        q.comparisonIso.inv.app ((FiniteFamily.map F).obj X) := by
  let pInv := G.map (p.comparisonIso.inv.app X)
  let qInv := q.comparisonIso.inv.app ((FiniteFamily.map F).obj X)
  let bridge := (Functor.isoWhiskerRight (FiniteFamily.mapCompIso F G)
    (FiniteTensor.tensor (V := U))).inv.app X
  have hBridge :
      bridge = 𝟙 _ := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := U)).map_id _
  have hDef : (compComparisonIso p q).inv.app X =
      (pInv ≫ qInv) ≫ bridge := by
    with_unfolding_all rfl
  let head := pInv ≫ qInv
  have hCancel : head ≫ bridge = head := by
    rw [hBridge]
    with_unfolding_all
      exact Category.comp_id head
  exact hDef.trans hCancel

/-- Composition of strong finite-tensor-preserving functors. -/
noncomputable def comp
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G) :
    Preserving (F ⋙ G) :=
  mkOfComponents (compComparisonIso p q)
    (fun X => by
      let singletonV :=
        (FiniteTensor.singletonIso (V := V)).hom.app X
      let singletonW :=
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X)
      let singletonU :=
        (FiniteTensor.singletonIso (V := U)).hom.app (G.obj (F.obj X))
      let pSingleton :=
        p.comparisonIso.hom.app
          ((FiniteFamily.singleton (C := V)).obj X)
      let qSingleton :=
        q.comparisonIso.hom.app
          ((FiniteFamily.singleton (C := W)).obj (F.obj X))
      have hComposite :
          (compComparisonIso p q).hom.app
              ((FiniteFamily.singleton (C := V)).obj X) =
            qSingleton ≫ G.map pSingleton := by
        with_unfolding_all
          exact compComparisonIso_hom_app p q
            ((FiniteFamily.singleton (C := V)).obj X)
      have hMap :
          (F ⋙ G).map singletonV = G.map (F.map singletonV) := rfl
      have hP : pSingleton ≫ F.map singletonV = singletonW := by
        exact p.comparisonIso_hom_app_singleton_comp X
      have hQ : qSingleton ≫ G.map singletonW = singletonU := by
        exact q.comparisonIso_hom_app_singleton_comp (F.obj X)
      have h0 :
          (compComparisonIso p q).hom.app
                ((FiniteFamily.singleton (C := V)).obj X) ≫
              (F ⋙ G).map singletonV =
            (qSingleton ≫ G.map pSingleton) ≫
              G.map (F.map singletonV) := by
        rw [hComposite, hMap]
        rfl
      have h1 :
          (qSingleton ≫ G.map pSingleton) ≫ G.map (F.map singletonV) =
            qSingleton ≫ (G.map pSingleton ≫ G.map (F.map singletonV)) :=
        Category.assoc _ _ _
      have h2 :
          qSingleton ≫ (G.map pSingleton ≫ G.map (F.map singletonV)) =
            qSingleton ≫ G.map (pSingleton ≫ F.map singletonV) := by
        exact congrArg (qSingleton ≫ ·)
          (G.map_comp pSingleton (F.map singletonV)).symm
      have h3 : qSingleton ≫ G.map (pSingleton ≫ F.map singletonV) =
          qSingleton ≫ G.map singletonW :=
        congrArg (qSingleton ≫ ·) (congrArg G.map hP)
      exact h0.trans (h1.trans (h2.trans (h3.trans hQ))))
    (fun X => by
      let tV : FiniteFamily V ⥤ V := FiniteTensor.tensor (V := V)
      let tW : FiniteFamily W ⥤ W := FiniteTensor.tensor (V := W)
      let tU : FiniteFamily U ⥤ U := FiniteTensor.tensor (V := U)
      let mapF : FiniteFamily V ⥤ FiniteFamily W := FiniteFamily.map F
      let mapG : FiniteFamily W ⥤ FiniteFamily U := FiniteFamily.map G
      let XX : FiniteFamily (FiniteFamily W) :=
        (FiniteFamily.map (FiniteFamily.map F)).obj X
      let flatV : FiniteFamily V := (FiniteFamily.flatten (C := V)).obj X
      let flatW : FiniteFamily W := (FiniteFamily.flatten (C := W)).obj XX
      let tensorVFamily : FiniteFamily V := (FiniteFamily.map tV).obj X
      let tensorWFamily : FiniteFamily W := (FiniteFamily.map tW).obj XX
      let mappedTensorV : FiniteFamily W := mapF.obj tensorVFamily
      let mappedTensorW : FiniteFamily U := mapG.obj tensorWFamily
      let mapMapGXX : FiniteFamily (FiniteFamily U) :=
        (FiniteFamily.map (FiniteFamily.map G)).obj XX
      let mapMapFGX : FiniteFamily (FiniteFamily U) :=
        (FiniteFamily.map (FiniteFamily.map (F ⋙ G))).obj X
      let mappedTensorFG : FiniteFamily U :=
        (FiniteFamily.map (F ⋙ G)).obj tensorVFamily
      let pFamily : tensorWFamily ⟶ mappedTensorV := by
        with_unfolding_all
          exact (FiniteFamily.mapIso p.comparisonIso).hom.app X
      let qFamily : (FiniteFamily.map tU).obj mapMapGXX ⟶
          mappedTensorW := by
        with_unfolding_all
          exact (FiniteFamily.mapIso q.comparisonIso).hom.app XX
      let gMapP : mappedTensorW ⟶
          (FiniteFamily.map G).obj mappedTensorV :=
        (FiniteFamily.map G).map pFamily
      let rFamily : (FiniteFamily.map tU).obj mapMapFGX ⟶
          mappedTensorFG := by
        with_unfolding_all
          exact
            (FiniteFamily.mapIso (compComparisonIso p q)).hom.app X
      let flatUComp :=
        (FiniteTensor.flattenIso (V := U)).hom.app mapMapFGX
      let flatUQ :=
        (FiniteTensor.flattenIso (V := U)).hom.app mapMapGXX
      let flatWHom := (FiniteTensor.flattenIso (V := W)).hom.app XX
      let flatVHom := (FiniteTensor.flattenIso (V := V)).hom.app X
      let pTensor := p.comparisonIso.hom.app tensorVFamily
      let pFlat := p.comparisonIso.hom.app flatV
      let qTensor := q.comparisonIso.hom.app mappedTensorV
      let qSource := q.comparisonIso.hom.app tensorWFamily
      let qFlat := q.comparisonIso.hom.app flatW
      let rTensor :=
        (compComparisonIso p q).hom.app tensorVFamily
      let rFlat := (compComparisonIso p q).hom.app flatV
      have hRFamily : rFamily = qFamily ≫ gMapP := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro i
          exact heq_of_eq (by
            with_unfolding_all
              exact compComparisonIso_hom_app p q (X.obj i))
      have hMapRFamily :
          tU.map rFamily = tU.map qFamily ≫ tU.map gMapP := by
        rw [hRFamily]
        exact tU.map_comp qFamily gMapP
      have hFlatU : flatUComp = flatUQ := by
        with_unfolding_all rfl
      have hRTensor : rTensor = qTensor ≫ G.map pTensor := by
        with_unfolding_all
          exact compComparisonIso_hom_app p q tensorVFamily
      have hRFlat : rFlat = qFlat ≫ G.map pFlat := by
        with_unfolding_all
          exact compComparisonIso_hom_app p q flatV
      have hQNat :
          tU.map gMapP ≫ qTensor =
            qSource ≫ G.map (tW.map pFamily) := by
        have h := q.comparisonIso.hom.naturality pFamily
        with_unfolding_all exact h
      have hQ :
          flatUQ ≫ tU.map qFamily ≫ qSource =
            qFlat ≫ G.map flatWHom := by
        with_unfolding_all
          exact q.flatten_compat_reduced_hom_app XX
      have hP :
          flatWHom ≫ tW.map pFamily ≫ pTensor =
            pFlat ≫ F.map flatVHom := by
        with_unfolding_all
          exact p.flatten_compat_reduced_hom_app X
      with_unfolding_all
        change flatUComp ≫ tU.map rFamily ≫ rTensor =
          rFlat ≫ (F ⋙ G).map flatVHom
      have h0 : flatUComp ≫ tU.map rFamily ≫ rTensor =
          flatUQ ≫ (tU.map qFamily ≫ tU.map gMapP) ≫
            (qTensor ≫ G.map pTensor) := by
        rw [hFlatU, hMapRFamily, hRTensor]
        rfl
      have h1 : flatUQ ≫ (tU.map qFamily ≫ tU.map gMapP) ≫
            (qTensor ≫ G.map pTensor) =
          flatUQ ≫ tU.map qFamily ≫
            (tU.map gMapP ≫ qTensor) ≫ G.map pTensor := by
        simp only [Category.assoc]
      have h2 : flatUQ ≫ tU.map qFamily ≫
            (tU.map gMapP ≫ qTensor) ≫ G.map pTensor =
          flatUQ ≫ tU.map qFamily ≫
            (qSource ≫ G.map (tW.map pFamily)) ≫ G.map pTensor :=
        congrArg (fun k => flatUQ ≫ tU.map qFamily ≫ k ≫ G.map pTensor) hQNat
      have h3 : flatUQ ≫ tU.map qFamily ≫
            (qSource ≫ G.map (tW.map pFamily)) ≫ G.map pTensor =
          (flatUQ ≫ tU.map qFamily ≫ qSource) ≫
            G.map (tW.map pFamily) ≫ G.map pTensor := by
        simp only [Category.assoc]
      have h4 : (flatUQ ≫ tU.map qFamily ≫ qSource) ≫
            G.map (tW.map pFamily) ≫ G.map pTensor =
          (qFlat ≫ G.map flatWHom) ≫
            G.map (tW.map pFamily) ≫ G.map pTensor :=
        congrArg (fun k => k ≫ G.map (tW.map pFamily) ≫ G.map pTensor) hQ
      have h5 : (qFlat ≫ G.map flatWHom) ≫
            G.map (tW.map pFamily) ≫ G.map pTensor =
          qFlat ≫ (G.map flatWHom ≫
            G.map (tW.map pFamily) ≫ G.map pTensor) := by
        simp only [Category.assoc]
      have hMapTriple : G.map flatWHom ≫
            G.map (tW.map pFamily) ≫ G.map pTensor =
          G.map (flatWHom ≫ tW.map pFamily ≫ pTensor) := by
        rw [G.map_comp, G.map_comp]
      have h6 : qFlat ≫ (G.map flatWHom ≫
            G.map (tW.map pFamily) ≫ G.map pTensor) =
          qFlat ≫ G.map (flatWHom ≫ tW.map pFamily ≫ pTensor) :=
        congrArg (qFlat ≫ ·) hMapTriple
      have h7 : qFlat ≫ G.map (flatWHom ≫ tW.map pFamily ≫ pTensor) =
          qFlat ≫ G.map (pFlat ≫ F.map flatVHom) :=
        congrArg (qFlat ≫ ·) (congrArg G.map hP)
      have h8 : qFlat ≫ G.map (pFlat ≫ F.map flatVHom) =
          qFlat ≫ (G.map pFlat ≫ G.map (F.map flatVHom)) := by
        with_unfolding_all
          exact congrArg (qFlat ≫ ·) (G.map_comp pFlat (F.map flatVHom))
      have h9 : qFlat ≫ (G.map pFlat ≫ G.map (F.map flatVHom)) =
          (qFlat ≫ G.map pFlat) ≫ G.map (F.map flatVHom) :=
        (Category.assoc _ _ _).symm
      have h10 : (qFlat ≫ G.map pFlat) ≫ G.map (F.map flatVHom) =
          rFlat ≫ (F ⋙ G).map flatVHom := by
        rw [← hRFlat]
        rfl
      have h01 := h0.trans h1
      have h02 := h01.trans h2
      have h03 := h02.trans h3
      have h04 := h03.trans h4
      have h05 := h04.trans h5
      have h06 := h05.trans h6
      have h07 := h06.trans h7
      have h08 := h07.trans h8
      have h09 := h08.trans h9
      exact h09.trans h10)

/-- The comparison of a composite preserving value is the pasted comparison. -/
@[simp]
theorem comp_comparisonIso
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G) :
    (p.comp q).comparisonIso = compComparisonIso p q :=
  rfl

/-- Forward comparison components for composite preserving values. -/
@[simp]
theorem comp_comparisonIso_hom_app
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G)
    (X : FiniteFamily V) :
    (p.comp q).comparisonIso.hom.app X =
      q.comparisonIso.hom.app ((FiniteFamily.map F).obj X) ≫
        G.map (p.comparisonIso.hom.app X) :=
  compComparisonIso_hom_app p q X

/-- Inverse comparison components for composite preserving values. -/
@[simp]
theorem comp_comparisonIso_inv_app
    {U : Type u₃} [Category.{v₃} U] [FiniteTensor U]
    {F : V ⥤ W} {G : W ⥤ U} (p : Preserving F) (q : Preserving G)
    (X : FiniteFamily V) :
    (p.comp q).comparisonIso.inv.app X =
      G.map (p.comparisonIso.inv.app X) ≫
        q.comparisonIso.inv.app ((FiniteFamily.map F).obj X) :=
  compComparisonIso_inv_app p q X

end Preserving

end CategoryTheory.FiniteTensor
