/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.OriginalAttachCellsFiniteCoconeCells

/-!
# The original simultaneous attachment is the finite-subfamily colimit

The universal property is proved on the same full original cofans and
pushout. A cocone's singleton cells give its full descender, and all
larger finite legs are recovered by the original subset naturality.
No alternate simultaneous attachment is substituted.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)

/-- The full original cofans descend every finite-subfamily cocone to its same root object. -/
def originalFiniteDesc (s : Cocone c.finiteDiagram) : Y ⟶ s.pt.right :=
  c.originalDesc s.pt.hom (c.coconeCell s) (c.coconeCell_boundary s)

/-- The actual finite-colimit descender retains the same entire original root map. -/
theorem root_originalFiniteDesc (s : Cocone c.finiteDiagram) :
    f ≫ c.originalFiniteDesc s = s.pt.hom := c.root_originalDesc _ _ _

/-- The actual finite-colimit descender retains each same entire original singleton cell map. -/
theorem cell_originalFiniteDesc (s : Cocone c.finiteDiagram) (i : c.ι) :
    c.cell i ≫ c.originalFiniteDesc s = c.coconeCell s i := c.cell_originalDesc _ _ _ i

/-- Every full original finite leg factors through the genuine original descender. -/
theorem partialToOriginal_desc (s : Cocone c.finiteDiagram) (p : Finset c.ι) :
    c.partialToOriginal p ≫ c.originalFiniteDesc s = c.coconeLeg s p := by
  apply FinitePartialAttachment.hom_ext c.occurrenceMap c.occurrenceAttaching p
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ c.originalFiniteDesc s) (c.root_partialToOriginal p)).trans
        ((c.root_originalFiniteDesc s).trans (Under.w (s.ι.app p)).symm))
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ c.originalFiniteDesc s) (c.cell_partialToOriginal p i)).trans
        ((c.cell_originalFiniteDesc s i.1).trans (c.cell_cocone_leg s p i).symm))

/-- The actual descender in the original under category keeps the literal full source triangle. -/
def finiteDesc (s : Cocone c.finiteDiagram) : Under.mk f ⟶ s.pt :=
  Under.homMk (c.originalFiniteDesc s) (c.root_originalFiniteDesc s)

/-- The same original full under-category cocone is genuinely a colimit of all finite
original subfamilies. -/
def finiteIsColimit : IsColimit c.finiteCocone where
  desc s := c.finiteDesc s
  fac s p := by
    apply Under.UnderMorphism.ext
    exact c.partialToOriginal_desc s p
  uniq s m hm := by
    apply Under.UnderMorphism.ext
    apply c.hom_ext
    · exact (Under.w m).trans (c.root_originalFiniteDesc s).symm
    · intro i
      have h := congrArg (fun q => q.right) (hm ({i} : Finset c.ι))
      have hc := congrArg (fun q => FinitePartialAttachment.cell c.occurrenceMap
        c.occurrenceAttaching {i} ⟨i, Finset.mem_singleton_self i⟩ ≫ q) h
      have he : c.cell i ≫ m.right = c.coconeCell s i :=
        (congrArg (fun q => q ≫ m.right) (c.cell_partialToOriginal {i} _).symm).trans
          ((Category.assoc _ _ _).trans hc)
      exact he.trans (c.cell_originalFiniteDesc s i).symm

end HomotopicalAlgebra.AttachCells
