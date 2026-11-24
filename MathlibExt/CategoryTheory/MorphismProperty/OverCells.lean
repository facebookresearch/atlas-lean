/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.LiftingProperties.Over
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Actual indexed cells in an over category

For each original cell and each actual map of its target to the base,
form the same cell in the over category. Its right lifting class is
exactly the original indexed right class on the underlying map. Original
squares and their whole base triangles are retained. A small index and
local smallness prove that this actual base-indexed family is small, with
independent object, Hom, index and working universes.
-/

noncomputable section
universe k w v u
open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {I : Type w} (i : I → Arrow C) (S : C)

/-- Index an original cell by its actual whole target map to the fixed base. -/
abbrev OverCellIndex := Σ s : I, (i s).right ⟶ S

/-- The original cell with its literal structural maps to the fixed base. -/
def overCell (s : OverCellIndex i S) :
    Over.mk ((i s.1).hom ≫ s.2) ⟶ Over.mk s.2 := Over.homMk (i s.1).hom rfl

/-- The entire original underlying cell is retained. -/
@[simp]
theorem overCell_left (s : OverCellIndex i S) : (overCell i S s).left = (i s.1).hom := rfl

/-- The actual family of all original cells over their supplied whole base maps. -/
def overCells : MorphismProperty (Over S) := .ofHoms (overCell i S)

/-- Original local Hom smallness and index smallness give the genuine small base-indexed family. -/
theorem overCells_isSmall [Small.{k} I] [LocallySmall.{k} C] :
    IsSmall.{k} (overCells i S) := by
  let _ : ∀ s : I, Small.{k} ((i s).right ⟶ S) := fun s =>
    (inferInstance : LocallySmall.{k} C).hom_small _ _
  exact isSmall_ofHoms (overCell i S)

/-- If the original indexed cells are monic, so are their actual lifts to the over category. -/
theorem overCells_le_monomorphisms (hm : ∀ s : I, Mono (i s).hom) :
    overCells i S ≤ monomorphisms (Over S) := by
  apply (ofHoms_le_iff (overCell i S) (monomorphisms (Over S))).mpr
  intro s
  let _ : Mono (i s.1).hom := hm s.1
  let _ : Mono (overCell i S s).left := hm s.1
  exact Over.mono_of_mono_left _

/-- Lifting all actual base-indexed cells is exactly the original underlying indexed right lifting
condition. -/
theorem overCells_rlp_iff {U V : Over S} (p : U ⟶ V) :
    (overCells i S).rlp p ↔ (ofHoms (fun s : I => (i s).hom)).rlp p.left := by
  constructor
  · intro hp A D f hf
    obtain ⟨s⟩ := hf
    refine ⟨fun {a b} sq => ?_⟩
    let q := b ≫ V.hom
    let c := overCell i S ⟨s, q⟩
    let a' : Over.mk ((i s).hom ≫ q) ⟶ U := Over.homMk a (by
      change a ≫ U.hom = (i s).hom ≫ q
      rw [← Over.w p, ← Category.assoc, sq.w, Category.assoc])
    let b' : Over.mk q ⟶ V := Over.homMk b rfl
    let _ : HasLiftingProperty c p := hp _
      (show overCells i S c from ofHoms.mk (f := overCell i S) ⟨s, q⟩)
    have sq' : CommSq a' c p b' := ⟨Over.OverMorphism.ext sq.w⟩
    exact CommSq.HasLift.mk' ⟨sq'.lift.left,
      congrArg Over.Hom.left sq'.fac_left, congrArg Over.Hom.left sq'.fac_right⟩
  · intro hp A D f hf
    obtain ⟨s⟩ := hf
    let _ : HasLiftingProperty (overCell i S s).left p.left := by
      change HasLiftingProperty (i s.1).hom p.left
      exact hp _ (ofHoms.mk s.1)
    exact HasLiftingProperty.over (overCell i S s) p

end CategoryTheory.MorphismProperty
