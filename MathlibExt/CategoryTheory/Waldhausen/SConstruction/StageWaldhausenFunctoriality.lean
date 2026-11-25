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

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory

/-!
# Stage functoriality for Waldhausen-exact functors

An explicitly supplied `Functor.IsWaldhausenExact` structure lets a functor
between arbitrary Waldhausen categories act on finite `S`-construction
stages.  Postcomposition preserves the stage predicate because it preserves
zero objects and cofibration sequences, and it restricts to the pointwise
weak-equivalence stage categories because it preserves weak equivalences.

The construction is mixed-universe.  Its object, morphism, inclusion,
reindexing, identity, and source-first composition laws are recorded without
installing any global exactness instance.  This file constructs no nerve,
realization, comma-category criterion, approximation theorem, weak-homotopy
endpoint, chain consequence, or spectrum map.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor.IsWaldhausenExact

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E]
variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]
  [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : D ⥤ E}

open Waldhausen.SConstruction

/-- Postcomposition by a Waldhausen-exact functor preserves the finite-stage
predicate. -/
theorem isStage_postcomp (hF : F.IsWaldhausenExact)
    (n : ℕ) (A : Ar n ⥤ C) (hA : IsStage n A) :
    IsStage n (A ⋙ F) where
  diag_isZero i := hF.map_isZero (hA.diag_isZero i)
  cofiber_triple hij hjk := by
    simpa only [Functor.comp_map] using
      hF.map_cofibrationSequence (hA.cofiber_triple hij hjk)

/-- Mixed-universe stage map supplied by explicit Waldhausen exactness. -/
def mapStage (hF : F.IsWaldhausenExact) (n : ℕ) :
    Stage C n ⥤ Stage D n :=
  (stageProperty D n).lift
    (forget C n ⋙ (Functor.whiskeringRight _ _ _).obj F)
    (fun X => hF.isStage_postcomp n X.obj X.property)

/-- The underlying diagram of the generic stage map is postcomposition. -/
@[simp]
theorem mapStage_obj (hF : F.IsWaldhausenExact) (n : ℕ)
    (X : Stage C n) :
    ((hF.mapStage n).obj X).obj = X.obj ⋙ F :=
  rfl

/-- The underlying morphism of the generic stage map is postwhiskering. -/
@[simp]
theorem mapStage_map (hF : F.IsWaldhausenExact) (n : ℕ)
    {X Y : Stage C n} (f : X ⟶ Y) :
    ((hF.mapStage n).map f).hom = Functor.whiskerRight f.hom F :=
  rfl

/-- The generic stage map preserves pointwise stage weak equivalences. -/
theorem stageWeak_of_mapStage (hF : F.IsWaldhausenExact)
    (n : ℕ) {X Y : Stage C n} (f : X ⟶ Y)
    (hf : stageWeak C n f) :
    stageWeak D n ((hF.mapStage n).map f) := by
  rw [mem_stageWeak] at hf ⊢
  intro a
  exact hF.map_weakEquivalence _ (hf a)

/-- Mixed-universe weak-stage map supplied by explicit Waldhausen
exactness. -/
def mapStageWeak (hF : F.IsWaldhausenExact) (n : ℕ) :
    StageWeakCategory C n ⥤ StageWeakCategory D n where
  obj X := ⟨(hF.mapStage n).obj X.obj⟩
  map {X Y} f :=
    ⟨(hF.mapStage n).map f.hom,
      hF.stageWeak_of_mapStage n f.hom f.property⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    exact (hF.mapStage n).map_id X.obj
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact (hF.mapStage n).map_comp f.hom g.hom

/-- The weak-stage object map is the restriction of the stage object map. -/
@[simp]
theorem mapStageWeak_obj (hF : F.IsWaldhausenExact) (n : ℕ)
    (X : StageWeakCategory C n) :
    ((hF.mapStageWeak n).obj X).obj = (hF.mapStage n).obj X.obj :=
  rfl

/-- The weak-stage morphism map is the restriction of the stage morphism
map. -/
@[simp]
theorem mapStageWeak_map (hF : F.IsWaldhausenExact) (n : ℕ)
    {X Y : StageWeakCategory C n} (f : X ⟶ Y) :
    ((hF.mapStageWeak n).map f).hom = (hF.mapStage n).map f.hom :=
  rfl

/-- Weak-stage inclusion commutes with the generic stage maps. -/
@[simp]
theorem mapStageWeak_inclusion (hF : F.IsWaldhausenExact) (n : ℕ) :
    hF.mapStageWeak n ⋙ stageWeakInclusion D n =
      stageWeakInclusion C n ⋙ hF.mapStage n := by
  rfl

/-- Postcomposition commutes strictly with contravariant stage
reindexing. -/
@[simp]
theorem mapStage_reindex (hF : F.IsWaldhausenExact)
    {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := C) f ⋙ hF.mapStage a.len =
      hF.mapStage b.len ⋙ reindexStage (C := D) f := by
  rfl

/-- Weak-stage restriction commutes strictly with contravariant
reindexing. -/
@[simp]
theorem mapStageWeak_reindex (hF : F.IsWaldhausenExact)
    {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStageWeak C f ⋙ hF.mapStageWeak a.len =
      hF.mapStageWeak b.len ⋙ reindexStageWeak D f := by
  rfl

/-- The Waldhausen-exact identity induces the identity stage map. -/
@[simp]
theorem mapStage_id (C : Type u₁) [Category.{v₁} C]
    [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] (n : ℕ) :
    (Functor.IsWaldhausenExact.id (C := C)).mapStage n =
      𝟭 (Stage C n) := by
  rfl

/-- Source-first composition of Waldhausen-exact functors induces
composition of stage maps. -/
@[simp]
theorem mapStage_comp (hF : F.IsWaldhausenExact)
    (hG : G.IsWaldhausenExact) (n : ℕ) :
    (hF.comp hG).mapStage n = hF.mapStage n ⋙ hG.mapStage n := by
  rfl

/-- The Waldhausen-exact identity induces the identity weak-stage map. -/
@[simp]
theorem mapStageWeak_id (C : Type u₁) [Category.{v₁} C]
    [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] (n : ℕ) :
    (Functor.IsWaldhausenExact.id (C := C)).mapStageWeak n =
      𝟭 (StageWeakCategory C n) := by
  rfl

/-- Source-first composition of Waldhausen-exact functors induces
composition of weak-stage maps. -/
@[simp]
theorem mapStageWeak_comp (hF : F.IsWaldhausenExact)
    (hG : G.IsWaldhausenExact) (n : ℕ) :
    (hF.comp hG).mapStageWeak n =
      hF.mapStageWeak n ⋙ hG.mapStageWeak n := by
  rfl

end CategoryTheory.Functor.IsWaldhausenExact
