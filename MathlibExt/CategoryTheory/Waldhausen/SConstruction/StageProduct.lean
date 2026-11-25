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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.Product
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Finite-stage product functors (no equivalence yet)

Under the locally scoped product Waldhausen structure `prodWaldhausen C D`,
project finite stages over `C × D` to component stages via `Prod.fst`/`Prod.snd`,
and pair component stages via `Functor.prod'`. The stage predicates follow from
the two-direction `isCofibrationSequence_prod_iff` correspondence and
componentwise zero objects. Categories `C` and `D` live in independent universes.

Proves no categorical equivalence, unit/counit, weak-stage comparison,
simplicial object, realization, additivity, K/G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] (n : ℕ)

/-- Local product Waldhausen structure on `C × D`, explicitly scoped. -/
local instance prodWaldhausenLocal : WaldhausenCategoryWithoutGluing (C × D) := prodWaldhausen

/-- Projected diagram to `C` satisfies `IsStage` via componentwise data. -/
theorem isStage_projectFst (X : Stage (C × D) n) :
    IsStage n (X.obj ⋙ Prod.fst C D) where
  diag_isZero i :=
    ((isZero_prod_iff (C := C) (D := D)).mp (X.property.diag_isZero i)).1
  cofiber_triple hij hjk :=
    ((isCofibrationSequence_prod_iff _ _).mp (X.property.cofiber_triple hij hjk)).1

/-- Projected diagram to `D` satisfies `IsStage` via componentwise data. -/
theorem isStage_projectSnd (X : Stage (C × D) n) :
    IsStage n (X.obj ⋙ Prod.snd C D) where
  diag_isZero i :=
    ((isZero_prod_iff (C := C) (D := D)).mp (X.property.diag_isZero i)).2
  cofiber_triple hij hjk :=
    ((isCofibrationSequence_prod_iff _ _).mp (X.property.cofiber_triple hij hjk)).2

/-- Paired diagram satisfies `IsStage` via the converse correspondence. -/
theorem isStage_pair (p : Stage C n × Stage D n) :
    IsStage n (p.1.obj.prod' p.2.obj) where
  diag_isZero i :=
    (isZero_prod_iff (C := C) (D := D)).mpr
      ⟨(p.1.property.diag_isZero i), (p.2.property.diag_isZero i)⟩
  cofiber_triple hij hjk :=
    (isCofibrationSequence_prod_iff _ _).mpr
      ⟨p.1.property.cofiber_triple hij hjk, p.2.property.cofiber_triple hij hjk⟩

/-- Projection to `Stage C n` through the full-subcategory lift. -/
noncomputable def stageProjectFst : Stage (C × D) n ⥤ Stage C n :=
  (stageProperty C n).lift
    { obj X := X.obj ⋙ Prod.fst C D
      map f := Functor.whiskerRight f.hom (Prod.fst C D)
      map_id X := by ext a; rfl
      map_comp f g := by ext a; rfl }
    (fun X => isStage_projectFst C D n X)

/-- Projection to `Stage D n` through the full-subcategory lift. -/
noncomputable def stageProjectSnd : Stage (C × D) n ⥤ Stage D n :=
  (stageProperty D n).lift
    { obj X := X.obj ⋙ Prod.snd C D
      map f := Functor.whiskerRight f.hom (Prod.snd C D)
      map_id X := by ext a; rfl
      map_comp f g := by ext a; rfl }
    (fun X => isStage_projectSnd C D n X)

/-- Projection functor to the product of stages via `Prod.fst`/`Prod.snd`. -/
noncomputable def stageProject :
    Stage (C × D) n ⥤ Stage C n × Stage D n :=
  (stageProjectFst C D n).prod' (stageProjectSnd C D n)

/-- Pairing functor from product stages via `Functor.prod'`. -/
noncomputable def stagePair :
    (Stage C n × Stage D n) ⥤ Stage (C × D) n :=
  (stageProperty (C × D) n).lift
    { obj p := p.1.obj.prod' p.2.obj
      map f := NatTrans.prod' f.1.hom f.2.hom
      map_id _ := rfl
      map_comp _ _ := rfl }
    (fun p => isStage_pair C D n p)

/-- Projected object to `C` computes componentwise. -/
@[simp]
theorem stageProjectFst_obj_obj (X : Stage (C × D) n) (a : Ar n) :
    ((stageProjectFst C D n).obj X).obj.obj a = (X.obj.obj a).1 := rfl

/-- Projected map to `C` computes componentwise. -/
@[simp]
theorem stageProjectFst_map_app {X Y : Stage (C × D) n} (f : X ⟶ Y) (a : Ar n) :
    ((stageProjectFst C D n).map f).hom.app a = (f.hom.app a).1 := rfl

/-- Projected object to `D` computes componentwise. -/
@[simp]
theorem stageProjectSnd_obj_obj (X : Stage (C × D) n) (a : Ar n) :
    ((stageProjectSnd C D n).obj X).obj.obj a = (X.obj.obj a).2 := rfl

/-- Projected map to `D` computes componentwise. -/
@[simp]
theorem stageProjectSnd_map_app {X Y : Stage (C × D) n} (f : X ⟶ Y) (a : Ar n) :
    ((stageProjectSnd C D n).map f).hom.app a = (f.hom.app a).2 := rfl

/-- Paired object computes componentwise. -/
@[simp]
theorem stagePair_obj_obj (p : Stage C n × Stage D n) (a : Ar n) :
    ((stagePair C D n).obj p).obj.obj a = (p.1.obj.obj a, p.2.obj.obj a) := rfl

/-- Paired map first component computes componentwise. -/
@[simp]
theorem stagePair_map_app_fst {p q : Stage C n × Stage D n} (f : p ⟶ q) (a : Ar n) :
    (((stagePair C D n).map f).hom.app a).1 = f.1.hom.app a := rfl

/-- Paired map second component computes componentwise. -/
@[simp]
theorem stagePair_map_app_snd {p q : Stage C n × Stage D n} (f : p ⟶ q) (a : Ar n) :
    (((stagePair C D n).map f).hom.app a).2 = f.2.hom.app a := rfl

end CategoryTheory.Waldhausen.SConstruction
