/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.OriginalAttachCellsFiniteCocone

/-!
# Descending from an entire original simultaneous attachment

The actual full target cofan and original pushout construct the
descender determined by its same source map and every whole cell map.
No replacement coproduct or replacement target is used.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)

/-- The genuine full original attachment descender keeps its original cofan and both
original pushout maps. -/
def originalDesc {Z : C} (r : X ⟶ Z) (b : ∀ i : c.ι, B (c.π i) ⟶ Z)
    (hb : ∀ i, g (c.π i) ≫ b i = c.occurrenceAttaching i ≫ r) : Y ⟶ Z :=
  c.isPushout.desc r (Cofan.IsColimit.desc c.isColimit₂ b) (by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro i
    rw [c.hm_assoc, Cofan.IsColimit.fac]
    exact (Category.assoc _ _ _).symm.trans (hb i).symm)

/-- The whole original attachment descender retains the same full source map. -/
theorem root_originalDesc {Z : C} (r : X ⟶ Z) (b : ∀ i : c.ι, B (c.π i) ⟶ Z)
    (hb : ∀ i, g (c.π i) ≫ b i = c.occurrenceAttaching i ≫ r) :
    f ≫ c.originalDesc r b hb = r := c.isPushout.inl_desc _ _ _

/-- The whole original attachment descender retains every same complete original cell map. -/
theorem cell_originalDesc {Z : C} (r : X ⟶ Z) (b : ∀ i : c.ι, B (c.π i) ⟶ Z)
    (hb : ∀ i, g (c.π i) ≫ b i = c.occurrenceAttaching i ≫ r) (i : c.ι) :
    c.cell i ≫ c.originalDesc r b hb = b i := by
  change (c.cofan₂.inj i ≫ c.g₂) ≫ c.isPushout.desc r
    (Cofan.IsColimit.desc c.isColimit₂ b) _ = _
  rw [Category.assoc, c.isPushout.inr_desc, Cofan.IsColimit.fac]

end HomotopicalAlgebra.AttachCells
