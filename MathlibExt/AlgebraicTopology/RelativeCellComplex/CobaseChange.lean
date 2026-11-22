/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The SAME full cell attachment under actual cobase change

Pasting the two original pushout squares retains the complete actual
cell occurrence type, generator labels, coproduct cocones and maps.
Only the supplied original base and target maps are composed. The
entire resulting cell attachment is proved by those SAME universal
properties, with independent category, Hom, cell and occurrence universes.
-/

@[expose] public section

noncomputable section
universe w t u v
open CategoryTheory Limits

namespace HomotopicalAlgebra.AttachCells
variable {C : Type u} [Category.{v} C] {α : Type t} {A B : α → C}
  {g : ∀ i, A i ⟶ B i} {X Y X' Y' : C} {f : X ⟶ Y}
  (a : AttachCells.{w} g f) (s : X ⟶ X') (t : Y ⟶ Y') (f' : X' ⟶ Y')
  (hp : IsPushout f s t f')

/-- Cobase change the SAME complete original cell attachment, retaining every occurrence and generator. -/
def cobaseChange : AttachCells.{w} g f' where
  ι := a.ι
  π := a.π
  cofan₁ := a.cofan₁
  cofan₂ := a.cofan₂
  isColimit₁ := a.isColimit₁
  isColimit₂ := a.isColimit₂
  m := a.m
  hm := a.hm
  g₁ := a.g₁ ≫ s
  g₂ := a.g₂ ≫ t
  isPushout := a.isPushout.paste_horiz hp.flip

/-- The original occurrence labels survive actual cobase change literally. -/
theorem cobaseChange_label (i : a.ι) : (cobaseChange a s t f' hp).π i = a.π i := rfl

/-- Every complete original target-cell leg survives as its SAME composed whole map. -/
theorem cobaseChange_cell (i : a.ι) :
    (cobaseChange a s t f' hp).cell i = a.cell i ≫ t := (Category.assoc _ _ _).symm

end HomotopicalAlgebra.AttachCells
