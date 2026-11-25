/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.OriginalAttachCellsDesc

/-!
# Every cocone retains the original full cell family

A cocone over the finite original subfamilies has a full cell map for
every original occurrence. Its singleton leg gives that map, and
subset naturality recovers the same map from every larger subfamily.
The entire original boundary equation is preserved.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)
  (s : Cocone c.finiteDiagram)

/-- The complete original cocone leg with its literal partial-attachment source type. -/
abbrev coconeLeg (p : Finset c.ι) :
    FinitePartialAttachment.object c.occurrenceMap c.occurrenceAttaching p ⟶ s.pt.right :=
  (s.ι.app p).right

/-- The same whole original occurrence read from its actual singleton cocone leg. -/
def coconeCell (i : c.ι) : B (c.π i) ⟶ s.pt.right :=
  FinitePartialAttachment.cell c.occurrenceMap c.occurrenceAttaching {i}
    ⟨i, Finset.mem_singleton_self i⟩ ≫ c.coconeLeg s {i}

/-- The full singleton cocone cell has the same actual original boundary at the cocone root. -/
theorem coconeCell_boundary (i : c.ι) :
    g (c.π i) ≫ c.coconeCell s i = c.occurrenceAttaching i ≫ s.pt.hom := by
  change g (c.π i) ≫ (FinitePartialAttachment.cell c.occurrenceMap
    c.occurrenceAttaching {i} ⟨i, Finset.mem_singleton_self i⟩ ≫
      c.coconeLeg s {i}) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ c.coconeLeg s {i})
      (FinitePartialAttachment.boundary c.occurrenceMap c.occurrenceAttaching {i}
        ⟨i, Finset.mem_singleton_self i⟩)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun q => c.occurrenceAttaching i ≫ q) (Under.w (s.ι.app {i})))))

/-- Every larger actual finite subfamily reads back the same whole original cocone cell. -/
theorem cell_cocone_leg (p : Finset c.ι) (i : p) :
    FinitePartialAttachment.cell c.occurrenceMap c.occurrenceAttaching p i ≫
      c.coconeLeg s p = c.coconeCell s i.1 := by
  let h : ({i.1} : Finset c.ι) ⊆ p := Finset.singleton_subset_iff.mpr i.2
  have hn :
      FinitePartialAttachment.map c.occurrenceMap c.occurrenceAttaching h ≫
        c.coconeLeg s p = c.coconeLeg s {i.1} :=
    (congrArg (fun q => q.right) (s.ι.naturality (homOfLE h))).trans (Category.comp_id _)
  have hc :
      FinitePartialAttachment.cell c.occurrenceMap c.occurrenceAttaching {i.1}
          ⟨i.1, Finset.mem_singleton_self i.1⟩ ≫
        FinitePartialAttachment.map c.occurrenceMap c.occurrenceAttaching h =
      FinitePartialAttachment.cell c.occurrenceMap c.occurrenceAttaching p i :=
    FinitePartialAttachment.cell_map c.occurrenceMap c.occurrenceAttaching h _
  exact (congrArg (fun q => q ≫ c.coconeLeg s p) hc.symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun q => FinitePartialAttachment.cell c.occurrenceMap
        c.occurrenceAttaching {i.1} ⟨i.1, Finset.mem_singleton_self i.1⟩ ≫ q) hn))

end HomotopicalAlgebra.AttachCells
