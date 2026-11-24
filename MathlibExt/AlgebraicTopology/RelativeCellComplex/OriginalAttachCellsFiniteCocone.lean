/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentMaps

/-!
# Finite subfamilies of an actual original simultaneous attachment

Each occurrence is taken from the same supplied AttachCells structure.
Its entire original cofan maps, boundary and pushout are retained.
The finite-subfamily under-root diagram has a genuine cocone to the
same original target, with literal root and cell readbacks.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)

/-- The original full cell map of each actual occurrence. -/
abbrev occurrenceMap (i : c.ι) : A (c.π i) ⟶ B (c.π i) := g (c.π i)

/-- The original full attaching map of each actual occurrence. -/
abbrev occurrenceAttaching (i : c.ι) : A (c.π i) ⟶ X := c.cofan₁.inj i ≫ c.g₁

omit [HasColimitsOfSize.{w, w} C] in
/-- The original simultaneous attachment satisfies each full original cell boundary. -/
theorem occurrence_boundary (i : c.ι) :
    c.occurrenceMap i ≫ c.cell i = c.occurrenceAttaching i ≫ f := by
  calc
    c.occurrenceMap i ≫ c.cell i = (c.cofan₁.inj i ≫ c.m) ≫ c.g₂ := by
      rw [c.hm]
      exact (Category.assoc _ _ _).symm
    _ = (c.cofan₁.inj i ≫ c.g₁) ≫ f := by
      rw [Category.assoc, ← c.isPushout.w, ← Category.assoc]

/-- The finite-subfamily diagram uses the actual original occurrences and attaching maps. -/
abbrev finiteDiagram : Finset c.ι ⥤ Under X :=
  FinitePartialAttachment.diagram c.occurrenceMap c.occurrenceAttaching

/-- The genuine partial-pushout map to the same complete original attachment target. -/
def partialToOriginal (s : Finset c.ι) :
    FinitePartialAttachment.object c.occurrenceMap c.occurrenceAttaching s ⟶ Y :=
  FinitePartialAttachment.desc c.occurrenceMap c.occurrenceAttaching s f
    (fun i => c.cell i.1) (fun i => c.occurrence_boundary i.1)

/-- The actual partial comparison retains the same entire original source map. -/
theorem root_partialToOriginal (s : Finset c.ι) :
    FinitePartialAttachment.root c.occurrenceMap c.occurrenceAttaching s ≫
      c.partialToOriginal s = f :=
  FinitePartialAttachment.root_desc c.occurrenceMap c.occurrenceAttaching s _ _ _

/-- The actual partial comparison retains every same entire original selected cell. -/
theorem cell_partialToOriginal (s : Finset c.ι) (i : s) :
    FinitePartialAttachment.cell c.occurrenceMap c.occurrenceAttaching s i ≫
      c.partialToOriginal s = c.cell i.1 :=
  FinitePartialAttachment.cell_desc c.occurrenceMap c.occurrenceAttaching s _ _ _ i

/-- The full partial comparisons commute with the same actual original subset maps. -/
theorem partialToOriginal_naturality {s z : Finset c.ι} (h : s ⊆ z) :
    FinitePartialAttachment.map c.occurrenceMap c.occurrenceAttaching h ≫
      c.partialToOriginal z = c.partialToOriginal s := by
  apply FinitePartialAttachment.hom_ext c.occurrenceMap c.occurrenceAttaching s
  · rw [← Category.assoc, FinitePartialAttachment.root_map]
    exact (c.root_partialToOriginal z).trans (c.root_partialToOriginal s).symm
  · intro i
    rw [← Category.assoc, FinitePartialAttachment.cell_map]
    exact (c.cell_partialToOriginal z _).trans (c.cell_partialToOriginal s i).symm

/-- The actual finite-subfamily under-root cocone ends at the same original full source arrow. -/
def finiteCocone : Cocone c.finiteDiagram where
  pt := Under.mk f
  ι :=
    { app s := Under.homMk (c.partialToOriginal s) (c.root_partialToOriginal s)
      naturality {_s _z} h := by
        apply Under.UnderMorphism.ext
        exact (c.partialToOriginal_naturality (leOfHom h)).trans (Category.comp_id _).symm }

/-- The entire original target arrow is read back literally from the finite cocone. -/
theorem finiteCocone_root : c.finiteCocone.pt.hom = f := rfl

/-- Every actual finite-cocone leg is the same complete original partial comparison. -/
theorem finiteCocone_leg (s : Finset c.ι) :
    (c.finiteCocone.ι.app s).right = c.partialToOriginal s := rfl

end HomotopicalAlgebra.AttachCells
