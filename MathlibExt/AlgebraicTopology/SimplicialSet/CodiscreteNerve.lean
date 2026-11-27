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

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Codiscrete nerve

The functor from types to simplicial sets given by the nerve of the codiscrete category.
It preserves binary products.
-/

@[expose] public section

namespace CategoryTheory.Codiscrete

universe u

open CategoryTheory
open CategoryTheory.Limits

/-- The functor from types to simplicial sets given by the codiscrete nerve. -/
def functorToSSet : Type u ⥤ SSet.{u} := functorToCat ⋙ nerveFunctor

/-- The object part of `functorToSSet` is the nerve of the codiscrete category. -/
@[simp]
theorem functorToSSet_obj (X : Type u) : functorToSSet.obj X = nerve (Codiscrete X) := rfl

/-- Canonical product isomorphism for the codiscrete nerve. -/
noncomputable def prodIso (X Y : Type u) :
    functorToSSet.obj (X × Y) ≅ functorToSSet.obj X ⨯ functorToSSet.obj Y :=
  let toExplicit : functorToSSet.obj (X × Y) ⟶
      FunctorToTypes.prod (functorToSSet.obj X) (functorToSSet.obj Y) :=
    { app Δ := ↾fun c =>
        (Codiscrete.functor (fun i : Fin (Δ.unop.len + 1) => (c.obj i |>.as).1),
         Codiscrete.functor (fun i : Fin (Δ.unop.len + 1) => (c.obj i |>.as).2)) }
  let fromExplicit : FunctorToTypes.prod (functorToSSet.obj X) (functorToSSet.obj Y) ⟶
      functorToSSet.obj (X × Y) :=
    { app Δ := ↾fun p =>
        Codiscrete.functor (fun i : Fin (Δ.unop.len + 1) => ((p.1.obj i).as, (p.2.obj i).as)) }
  let toFrom : toExplicit ≫ fromExplicit = 𝟙 (functorToSSet.obj (X × Y)) := by
    ext Δ c
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · rfl
  let fromTo : fromExplicit ≫ toExplicit = 𝟙 _ := by
    ext Δ p
    · refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
      · rfl
      · rfl
    · refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
      · rfl
      · rfl
  let explicitIso : functorToSSet.obj (X × Y) ≅
      FunctorToTypes.prod (functorToSSet.obj X) (functorToSSet.obj Y) :=
    { hom := toExplicit
      inv := fromExplicit
      hom_inv_id := toFrom
      inv_hom_id := fromTo }
  explicitIso.trans (FunctorToTypes.binaryProductIso _ _).symm

/-- The forward codiscrete-nerve product isomorphism followed by the first projection is induced by
the ordinary first projection. -/
@[reassoc (attr := simp)]
lemma prodIso_hom_comp_fst (X Y : Type u) :
    (prodIso X Y).hom ≫ prod.fst =
      functorToSSet.map (↾_root_.Prod.fst : X × Y ⟶ X) := by
  simp only [prodIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, FunctorToTypes.binaryProductIso_inv_comp_fst]
  ext Δ c
  refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
  · rfl
  · rfl

/-- The forward codiscrete-nerve product isomorphism followed by the second projection is induced by
the ordinary second projection. -/
@[reassoc (attr := simp)]
lemma prodIso_hom_comp_snd (X Y : Type u) :
    (prodIso X Y).hom ≫ prod.snd =
      functorToSSet.map (↾_root_.Prod.snd : X × Y ⟶ Y) := by
  simp only [prodIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, FunctorToTypes.binaryProductIso_inv_comp_snd]
  ext Δ c
  refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
  · rfl
  · rfl

private theorem prodComparison_eq (X Y : Type u) :
    Limits.prodComparison functorToSSet X Y =
      (functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫ (prodIso X Y).hom := by
  apply prod.hom_ext
  · calc
      Limits.prodComparison functorToSSet X Y ≫ prod.fst = functorToSSet.map prod.fst :=
        prodComparison_fst _ _ _
      _ = functorToSSet.map ((Types.binaryProductIso X Y).hom ≫
            (↾_root_.Prod.fst : X × Y ⟶ X)) := by
          rw [Types.binaryProductIso_hom_comp_fst]
      _ = functorToSSet.map (Types.binaryProductIso X Y).hom ≫
            functorToSSet.map (↾_root_.Prod.fst : X × Y ⟶ X) := by
          rw [Functor.map_comp]
      _ = (functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            functorToSSet.map (↾_root_.Prod.fst : X × Y ⟶ X) := rfl
      _ = (functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            ((prodIso X Y).hom ≫ prod.fst) := by rw [prodIso_hom_comp_fst]
      _ = ((functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            (prodIso X Y).hom) ≫ prod.fst := by rw [Category.assoc]
  · calc
      Limits.prodComparison functorToSSet X Y ≫ prod.snd = functorToSSet.map prod.snd :=
        prodComparison_snd _ _ _
      _ = functorToSSet.map ((Types.binaryProductIso X Y).hom ≫
            (↾_root_.Prod.snd : X × Y ⟶ Y)) := by
          rw [Types.binaryProductIso_hom_comp_snd]
      _ = functorToSSet.map (Types.binaryProductIso X Y).hom ≫
            functorToSSet.map (↾_root_.Prod.snd : X × Y ⟶ Y) := by
          rw [Functor.map_comp]
      _ = (functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            functorToSSet.map (↾_root_.Prod.snd : X × Y ⟶ Y) := rfl
      _ = (functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            ((prodIso X Y).hom ≫ prod.snd) := by rw [prodIso_hom_comp_snd]
      _ = ((functorToSSet.mapIso (Types.binaryProductIso X Y)).hom ≫
            (prodIso X Y).hom) ≫ prod.snd := by rw [Category.assoc]

instance isIso_prodComparison (X Y : Type u) :
    IsIso (Limits.prodComparison functorToSSet X Y) := by
  rw [prodComparison_eq X Y]
  infer_instance

instance : PreservesLimitsOfShape (Discrete WalkingPair)
    (functorToSSet : Type u ⥤ SSet.{u}) :=
  preservesBinaryProducts_of_isIso_prodComparison
    (functorToSSet : Type u ⥤ SSet.{u})

end CategoryTheory.Codiscrete
