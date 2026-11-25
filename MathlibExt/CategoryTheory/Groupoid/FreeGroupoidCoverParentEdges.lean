/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverParent
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverNeighborWords

/-!
# The actual original cover root and unique parent edge

The full native normal word determines every individual cover vertex,
including the original root, parent, edge orientation and complete
original generator coefficient. These are proved from original words;
no tree or weak conclusion is supplied as an assumption.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- The SAME original cover root has its actual empty native word. -/
lemma coverRoot_word : CoverVertex.word V z (coverRoot V z) = [] := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  change normalWord V (𝟙 ((Quiver.FreeGroupoid.of V).obj z)) = []
  unfold normalWord
  rw [(labelledFunctor V).map_id]
  exact FreeGroup.toWord_one

/-- Rank zero identifies the SAME individual original cover root. -/
lemma CoverVertex.rank_eq_zero_iff (a : CoverVertex V z) :
    CoverVertex.rank V z a = 0 ↔ a = coverRoot V z := by
  constructor
  · intro h
    apply CoverVertex.word_injective V z
    have hn : CoverVertex.word V z a = [] := List.length_eq_zero_iff.mp h
    exact hn.trans (coverRoot_word V z).symm
  · intro h
    subst a
    change (CoverVertex.word V z (coverRoot V z)).length = 0
    rw [coverRoot_word]
    rfl

/-- An actual downward original generator is exactly the last negative full label. -/
lemma coverArrow_down_last {a b : CoverVertex V z} (f : CoverArrow V z a b)
    (h : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a) :
    (CoverVertex.word V z a).getLast? = some (⟨a.target, b.target, f.arrow⟩, false) := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  by_contra he
  have hw := (congrArg (CoverVertex.word V z) (coverArrow_target_eq_append V z f)).trans
    (CoverVertex.append_word V z a f.arrow)
  have hl := congrArg List.length (hw.trans (ite_eq_right he))
  rw [List.length_concat] at hl
  change (CoverVertex.word V z b).length + 1 = (CoverVertex.word V z a).length at h
  omega

/-- An actual upward original generator is exactly the last positive full label. -/
lemma coverArrow_up_last {a b : CoverVertex V z} (f : CoverArrow V z a b)
    (h : CoverVertex.rank V z a + 1 = CoverVertex.rank V z b) :
    (CoverVertex.word V z b).getLast? = some (⟨a.target, b.target, f.arrow⟩, true) := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have hw := (congrArg (CoverVertex.word V z) (coverArrow_target_eq_append V z f)).trans
    (CoverVertex.append_word V z a f.arrow)
  by_cases he : (CoverVertex.word V z a).getLast? = some (⟨a.target, b.target, f.arrow⟩, false)
  · have hl := congrArg List.length (hw.trans (ite_eq_left he))
    rw [List.length_dropLast] at hl
    change (CoverVertex.word V z a).length + 1 = (CoverVertex.word V z b).length at h
    omega
  · have hc : ((CoverVertex.word V z a).concat (⟨a.target, b.target, f.arrow⟩, true)).getLast? =
        some (⟨a.target, b.target, f.arrow⟩, true) := by
      rw [List.concat_eq_append]
      exact List.getLast?_concat
    exact (congrArg List.getLast? (hw.trans (ite_eq_right he))).trans hc

/-- Two SAME original cover arrows with the same endpoints have the SAME complete original
coefficient. -/
theorem CoverArrow.subsingleton (a b : CoverVertex V z) : Subsingleton (CoverArrow V z a b) := by
  refine ⟨fun f g => ?_⟩
  apply CoverArrow.ext_coefficient V z
  rcases coverArrow_rank_step V z f with h | h
  · have he := (coverArrow_down_last V z f h).symm.trans (coverArrow_down_last V z g h)
    have hp : arrowLabel V (.inr f.arrow) = arrowLabel V (.inr g.arrow) := Option.some.inj he
    exact Sum.inr.inj (eq_of_heq (arrowLabel_arrow_heq V (.inr f.arrow) (.inr g.arrow) hp))
  · have he := (coverArrow_up_last V z f h).symm.trans (coverArrow_up_last V z g h)
    have hp : arrowLabel V (.inl f.arrow) = arrowLabel V (.inl g.arrow) := Option.some.inj he
    exact Sum.inl.inj (eq_of_heq (arrowLabel_arrow_heq V (.inl f.arrow) (.inl g.arrow) hp))

/-- The SAME original nonroot cover-parent vertex, reconstructed from the actual full prefix
word. -/
def coverParent (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) : CoverVertex V z :=
  (cover_parent_exists V z a ha).choose

/-- The actual parent retains the SAME original full word with its last signed generator removed. -/
lemma coverParent_word (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    CoverVertex.word V z (coverParent V z a ha) = (CoverVertex.word V z a).dropLast :=
  (cover_parent_exists V z a ha).choose_spec.2.1

/-- The actual original parent lowers rank by exactly one. -/
lemma coverParent_rank (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    CoverVertex.rank V z (coverParent V z a ha) + 1 = CoverVertex.rank V z a :=
  (cover_parent_exists V z a ha).choose_spec.2.2

/-- Every actual parent is joined by an original generator with its full native path triangle. -/
lemma coverParent_arrow (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    Nonempty (CoverArrow V z (coverParent V z a ha) a) ∨
      Nonempty (CoverArrow V z a (coverParent V z a ha)) :=
  (cover_parent_exists V z a ha).choose_spec.1

end Quiver.FreeGroupoid.OriginalWords
