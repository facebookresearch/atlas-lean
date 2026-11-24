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

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality

/-!
# Tests for generic Waldhausen stage functoriality

These clients pin independent source, target, and intermediate universes;
object and morphism formulas; weak-stage restriction; reindexing; and
identity/source-first composition.  Exact-category clients compare the
generic maps, under explicitly supplied Waldhausen exactness, with the
existing additive exact-category maps.

No global exact-category adapter, simplicial Stage map, comma-category
criterion, approximation theorem, weak-homotopy endpoint, chain consequence,
or spectrum statement is added or tested.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWaldhausenFunctorialityTests

section General

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E]
variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]
  [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : D ⥤ E}
variable (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)

example (n : ℕ) : Stage C n ⥤ Stage D n :=
  hF.mapStage n

example (n : ℕ) : StageWeakCategory C n ⥤ StageWeakCategory D n :=
  hF.mapStageWeak n

example (n : ℕ) (X : Stage C n) :
    (forget D n).obj ((hF.mapStage n).obj X) = X.obj ⋙ F :=
  hF.mapStage_obj n X

example (n : ℕ) {X Y : Stage C n} (f : X ⟶ Y) :
    (forget D n).map ((hF.mapStage n).map f) =
      Functor.whiskerRight ((forget C n).map f) F :=
  hF.mapStage_map n f

example (n : ℕ) (X : StageWeakCategory C n) :
    ((hF.mapStageWeak n).obj X).obj = (hF.mapStage n).obj X.obj :=
  hF.mapStageWeak_obj n X

example (n : ℕ) {X Y : StageWeakCategory C n} (f : X ⟶ Y) :
    ((hF.mapStageWeak n).map f).hom = (hF.mapStage n).map f.hom :=
  hF.mapStageWeak_map n f

example (n : ℕ) :
    hF.mapStageWeak n ⋙ stageWeakInclusion D n =
      stageWeakInclusion C n ⋙ hF.mapStage n :=
  hF.mapStageWeak_inclusion n

example (n : ℕ) {X Y : Stage C n} (f : X ⟶ Y)
    (hf : stageWeak C n f) :
    stageWeak D n ((hF.mapStage n).map f) :=
  hF.stageWeak_of_mapStage n f hf

example {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := C) f ⋙ hF.mapStage a.len =
      hF.mapStage b.len ⋙ reindexStage (C := D) f :=
  hF.mapStage_reindex f

example {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStageWeak C f ⋙ hF.mapStageWeak a.len =
      hF.mapStageWeak b.len ⋙ reindexStageWeak D f :=
  hF.mapStageWeak_reindex f

example (n : ℕ) :
    (Functor.IsWaldhausenExact.id (C := C)).mapStage n =
      𝟭 (Stage C n) :=
  Functor.IsWaldhausenExact.mapStage_id C n

example (n : ℕ) :
    (Functor.IsWaldhausenExact.id (C := C)).mapStageWeak n =
      𝟭 (StageWeakCategory C n) :=
  Functor.IsWaldhausenExact.mapStageWeak_id C n

example (n : ℕ) :
    (hF.comp hG).mapStage n =
      hF.mapStage n ⋙ hG.mapStage n :=
  hF.mapStage_comp hG n

example (n : ℕ) :
    (hF.comp hG).mapStageWeak n =
      hF.mapStageWeak n ⋙ hG.mapStageWeak n :=
  hF.mapStageWeak_comp hG n

end General

section ExactCategoryComparison

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable [HasZeroObject C] [HasZeroObject D]
variable [HasBinaryBiproducts C] [HasBinaryBiproducts D]
variable [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

variable (hF : F.IsWaldhausenExact)

example (n : ℕ) : hF.mapStage n = mapStage C D F n := by
  rfl

example (n : ℕ) : hF.mapStageWeak n = mapStageWeak C D F n := by
  rfl

example (n : ℕ) (X : Stage C n) :
    (forget D n).obj ((hF.mapStage n).obj X) = X.obj ⋙ F :=
  hF.mapStage_obj n X

end ExactCategoryComparison

section TypeZero

variable {C₀ D₀ : Type 0} [Category.{0} C₀] [Category.{0} D₀]
  [HasZeroObject C₀] [HasZeroObject D₀]
  [WaldhausenCategoryWithoutGluing C₀] [WaldhausenCategoryWithoutGluing D₀]
variable {F₀ : C₀ ⥤ D₀} (hF₀ : F₀.IsWaldhausenExact)

example (n : ℕ) : Stage C₀ n ⥤ Stage D₀ n :=
  hF₀.mapStage n

end TypeZero

section TypeOne

variable {C₁ D₁ : Type 1} [Category.{1} C₁] [Category.{1} D₁]
  [HasZeroObject C₁] [HasZeroObject D₁]
  [WaldhausenCategoryWithoutGluing C₁] [WaldhausenCategoryWithoutGluing D₁]
variable {F₁ : C₁ ⥤ D₁} (hF₁ : F₁.IsWaldhausenExact)

example (n : ℕ) : StageWeakCategory C₁ n ⥤ StageWeakCategory D₁ n :=
  hF₁.mapStageWeak n

end TypeOne

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Functor.IsWaldhausenExact.simplicialStageWeakMap

#guard_msgs (error, substring := true) in
#check CategoryTheory.Functor.StagewiseTheoremACondition

#guard_msgs (error, substring := true) in
#check WaldhausenKTheory.approximation_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check WaldhausenKTheory.approximation_quasiIso_normalizedChainComplexMap

#guard_msgs (error, substring := true) in
#check WaldhausenKTheory.approximation_equiv

#guard_msgs (error, substring := true) in
#check WaldhausenKTheory.approximationSpectrumMap

end Nonclaims

#print axioms CategoryTheory.Functor.IsWaldhausenExact.isStage_postcomp
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage_obj
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage_map
#print axioms CategoryTheory.Functor.IsWaldhausenExact.stageWeak_of_mapStage
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_obj
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_map
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_inclusion
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage_reindex
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_reindex
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage_id
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStage_comp
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_id
#print axioms CategoryTheory.Functor.IsWaldhausenExact.mapStageWeak_comp

end StageWaldhausenFunctorialityTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
