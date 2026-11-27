/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentInsertDesc

/-!
# The original single-cell pushout in a finite attachment

Inserting an unselected occurrence gives a genuine pushout of its
original whole cell map along its original attaching map into the old
partial attachment. The old and new cell inclusions are retained.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} [DecidableEq I] {A B : I → C} (g : ∀ i, A i ⟶ B i)
  {X : C} (a : ∀ i, A i ⟶ X)

/-- The actual insertion square commutes with the original complete cell boundary. -/
theorem insert_condition (s : Finset I) (i : I) :
    (a i ≫ root g a s) ≫ insertMap g a s i = g i ≫ newCell g a s i := by
  rw [Category.assoc, root_map]
  exact (boundary g a (insert i s) ⟨i, Finset.mem_insert_self i s⟩).symm

/-- The old partial attachment and the new complete cell determine maps from the enlarged
attachment. -/
theorem insert_hom_ext (s : Finset I) (i : I) {Z : C}
    {f h : object g a (insert i s) ⟶ Z}
    (hr : insertMap g a s i ≫ f = insertMap g a s i ≫ h)
    (hb : newCell g a s i ≫ f = newCell g a s i ≫ h) : f = h := by
  apply hom_ext g a (insert i s)
  · exact (root_map g a (Finset.subset_insert i s)).symm ▸
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => root g a s ≫ q) hr).trans (Category.assoc _ _ _).symm))
  · intro j
    by_cases hj : j.1 = i
    · have he : j = ⟨i, Finset.mem_insert_self i s⟩ := Subtype.ext hj
      rw [he]
      exact hb
    · have hm : j.1 ∈ s := (Finset.mem_insert.mp j.2).resolve_left hj
      let k : s := ⟨j.1, hm⟩
      have he : j = occurrence (Finset.subset_insert i s) k := Subtype.ext rfl
      rw [he, ← cell_map]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => cell g a s k ≫ q) hr).trans (Category.assoc _ _ _).symm)

/-- Adding one original occurrence is the genuine pushout of its same complete original cell map. -/
theorem insert_isPushout (s : Finset I) (i : I) (hi : i ∉ s) :
    IsPushout (a i ≫ root g a s) (g i) (insertMap g a s i) (newCell g a s i) :=
  IsPushout.mk' (insert_condition g a s i)
    (fun {_Z} {_f _h} hr hb => insert_hom_ext g a s i hr hb)
    (fun {_Z} r b hb => ⟨insertDesc g a s i hi r b hb,
      insertMap_insertDesc g a s i hi r b hb, newCell_insertDesc g a s i hi r b hb⟩)

end HomotopicalAlgebra.FinitePartialAttachment
