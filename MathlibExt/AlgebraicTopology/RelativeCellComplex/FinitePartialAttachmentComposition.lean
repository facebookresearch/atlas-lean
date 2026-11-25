/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentInsertPushout
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentEmpty

/-!
# Genuine finite composition of the original partial attachments

For a composition-stable morphism property containing isomorphisms,
weakness of the original single-cell cobase changes proves membership
of every actual finite root and every inclusion of partial attachments.
The maps are those of the original finite-subfamily under diagram.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} [DecidableEq I] {A B : I → C} (g : ∀ i, A i ⟶ B i)
  {X : C} (a : ∀ i, A i ⟶ X)
  (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso]
  [P.IsStableUnderComposition]
  (hP : (MorphismProperty.ofHoms g).pushouts ≤ P)

include hP

omit [DecidableEq I] in
/-- Every actual original finite-family root is a finite composite of the same single-cell
cobase changes. -/
theorem root_mem (s : Finset I) : P (root g a s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let _ := root_empty_isIso g a
    exact P.of_isIso _
  | @insert i s hi ih =>
    have hn : P (insertMap g a s i) :=
      hP _ (MorphismProperty.pushouts_mk _ (insert_isPushout g a s i hi) ⟨i⟩)
    exact (root_map g a (Finset.subset_insert i s)) ▸ P.comp_mem _ _ ih hn

omit [P.RespectsIso] in
/-- The actual map adding any finite original family to a fixed old family belongs to the
same property. -/
theorem map_union_mem (s t z : Finset I) (hz : z = s ∪ t) (h : s ⊆ z) :
    P (map g a h) := by
  induction t using Finset.induction_on generalizing z with
  | empty =>
    simp only [Finset.union_empty] at hz
    subst z
    rw [map_id]
    exact P.id_mem _
  | @insert i t _hi ih =>
    rw [Finset.union_insert] at hz
    by_cases hi : i ∈ s ∪ t
    · rw [Finset.insert_eq_of_mem hi] at hz
      exact ih z hz h
    · have hm : P (map g a (show s ⊆ s ∪ t from Finset.subset_union_left)) :=
        ih (s ∪ t) rfl Finset.subset_union_left
      have hn : P (insertMap g a (s ∪ t) i) :=
        hP _ (MorphismProperty.pushouts_mk _
          (insert_isPushout g a (s ∪ t) i hi) ⟨i⟩)
      subst z
      exact (map_comp g a (show s ⊆ s ∪ t from Finset.subset_union_left)
        (Finset.subset_insert i (s ∪ t))) ▸ P.comp_mem _ _ hm hn

omit [P.RespectsIso] [DecidableEq I] in
/-- Every transition in the finite-subfamily diagram belongs to the same property. -/
theorem map_mem {s t : Finset I} (h : s ⊆ t) : P (map g a h) := by
  classical
  exact map_union_mem g a P hP s t t (Finset.union_eq_right.mpr h).symm h

end HomotopicalAlgebra.FinitePartialAttachment
