/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentMaps
import Mathlib.Data.Finset.Insert

/-!
# Actual original partial-attachment descenders after inserting one original cell

The old full selected cells and the single SAME new original cell retain
their actual original maps. Their genuine boundary equation constructs
the complete original descender on the entire enlarged finite family,
with exact old-root, old-cell and new-cell readbacks.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} [DecidableEq I] {A B : I → C} (g : ∀ i, A i ⟶ B i)
  {X : C} (a : ∀ i, A i ⟶ X)

/-- The SAME complete original partial-pushout map inserting the specified original occurrence. -/
abbrev insertMap (s : Finset I) (i : I) : object g a s ⟶ object g a (insert i s) :=
  map g a (Finset.subset_insert i s)

/-- The entire SAME new original cell in the actual enlarged finite attachment. -/
abbrev newCell (s : Finset I) (i : I) : B i ⟶ object g a (insert i s) :=
  cell g a (insert i s) ⟨i, Finset.mem_insert_self i s⟩

/-- The SAME old full cell maps and new full cell map on the complete enlarged original family. -/
def insertCells (s : Finset I) (i : I) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z) (j : ↥(insert i s)) : B j.1 ⟶ Z :=
  if h : j.1 = i then eqToHom (congrArg B h) ≫ b
  else cell g a s ⟨j.1, (Finset.mem_insert.mp j.2).resolve_left h⟩ ≫ r

/-- The SAME actual new original cell is read back literally. -/
theorem insertCells_new (s : Finset I) (i : I) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z) :
    insertCells g a s i r b ⟨i, Finset.mem_insert_self i s⟩ = b := by
  simp only [insertCells, dite_eq_left rfl, eqToHom_refl, Category.id_comp]

/-- Every entire old original cell retains its SAME specified map. -/
theorem insertCells_old (s : Finset I) (i : I) (hi : i ∉ s) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z) (j : s) :
    insertCells g a s i r b ⟨j.1, Finset.mem_insert_of_mem j.2⟩ = cell g a s j ≫ r := by
  have hj : j.1 ≠ i := fun h => hi (h ▸ j.2)
  simp only [insertCells, dite_eq_right hj]

/-- The SAME complete original inserted cell family has precisely the genuine original
boundary equation. -/
theorem insertCells_boundary (s : Finset I) (i : I) (hi : i ∉ s) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z)
    (hb : (a i ≫ root g a s) ≫ r = g i ≫ b) (j : ↥(insert i s)) :
    g j.1 ≫ insertCells g a s i r b j = a j.1 ≫ (root g a s ≫ r) := by
  by_cases hj : j.1 = i
  · have he : j = ⟨i, Finset.mem_insert_self i s⟩ := Subtype.ext hj
    rw [he, insertCells_new]
    exact hb.symm.trans (Category.assoc _ _ _)
  · have hm : j.1 ∈ s := (Finset.mem_insert.mp j.2).resolve_left hj
    let k : s := ⟨j.1, hm⟩
    have he : j = ⟨k.1, Finset.mem_insert_of_mem k.2⟩ := Subtype.ext rfl
    rw [he, insertCells_old g a s i hi]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ r) (boundary g a s k)).trans (Category.assoc _ _ _))

/-- The genuine complete original inserted-family descender retains both original maps. -/
def insertDesc (s : Finset I) (i : I) (hi : i ∉ s) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z)
    (hb : (a i ≫ root g a s) ≫ r = g i ≫ b) : object g a (insert i s) ⟶ Z :=
  desc g a (insert i s) (root g a s ≫ r) (insertCells g a s i r b)
    (insertCells_boundary g a s i hi r b hb)

/-- The actual inserted-family descender retains the SAME entire new original cell map. -/
theorem newCell_insertDesc (s : Finset I) (i : I) (hi : i ∉ s) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z)
    (hb : (a i ≫ root g a s) ≫ r = g i ≫ b) :
    newCell g a s i ≫ insertDesc g a s i hi r b hb = b :=
  (cell_desc g a (insert i s) _ _ _ ⟨i, Finset.mem_insert_self i s⟩).trans
    (insertCells_new g a s i r b)

/-- The actual inserted-family descender retains the SAME entire old original
partial-attachment map. -/
theorem insertMap_insertDesc (s : Finset I) (i : I) (hi : i ∉ s) {Z : C}
    (r : object g a s ⟶ Z) (b : B i ⟶ Z)
    (hb : (a i ≫ root g a s) ≫ r = g i ≫ b) :
    insertMap g a s i ≫ insertDesc g a s i hi r b hb = r := by
  apply hom_ext g a s
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ insertDesc g a s i hi r b hb) (root_map g a _)).trans
        (root_desc g a (insert i s) _ _ _))
  · intro j
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ insertDesc g a s i hi r b hb) (cell_map g a _ j)).trans
        ((cell_desc g a (insert i s) _ _ _ _).trans (insertCells_old g a s i hi r b j)))

end HomotopicalAlgebra.FinitePartialAttachment
