/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverRank

/-!
# Exact lower original cover-neighbor words

The full original edge append rule and native ranks determine the
complete word of the smaller neighbor: it is the SAME original full
word with its last signed generator removed. Full original word
injection gives unique lower neighbors without assuming a tree.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- The SAME original downward generating edge retains the exact original parent word. -/
lemma coverArrow_down_word {a b : CoverVertex V z} (f : CoverArrow V z a b)
    (h : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a) :
    CoverVertex.word V z b = (CoverVertex.word V z a).dropLast := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have hb := coverArrow_target_eq_append V z f
  have hw := (congrArg (CoverVertex.word V z) hb).trans (CoverVertex.append_word V z a f.arrow)
  by_cases he : (CoverVertex.word V z a).getLast? = some (⟨a.target, b.target, f.arrow⟩, false)
  · exact hw.trans (ite_eq_left he)
  · have hl := congrArg List.length (hw.trans (ite_eq_right he))
    change (CoverVertex.word V z b).length + 1 = (CoverVertex.word V z a).length at h
    rw [List.length_concat] at hl
    omega

/-- The SAME original upward generating edge retains the exact original source as the
parent's full word. -/
lemma coverArrow_up_word {a b : CoverVertex V z} (f : CoverArrow V z a b)
    (h : CoverVertex.rank V z a + 1 = CoverVertex.rank V z b) :
    CoverVertex.word V z a = (CoverVertex.word V z b).dropLast := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have hb := coverArrow_target_eq_append V z f
  have hw := (congrArg (CoverVertex.word V z) hb).trans (CoverVertex.append_word V z a f.arrow)
  by_cases he : (CoverVertex.word V z a).getLast? = some (⟨a.target, b.target, f.arrow⟩, false)
  · have hl := congrArg List.length (hw.trans (ite_eq_left he))
    rw [List.length_dropLast] at hl
    change (CoverVertex.word V z a).length + 1 = (CoverVertex.word V z b).length at h
    omega
  · have heq := hw.trans (ite_eq_right he)
    have hc : ((CoverVertex.word V z a).concat (⟨a.target, b.target, f.arrow⟩, true)).dropLast =
        CoverVertex.word V z a := by
      rw [List.concat_eq_append]
      exact List.dropLast_concat
    exact ((congrArg List.dropLast heq).trans hc).symm

/-- Full original cover vertices have at most one lower neighbor with its SAME actual native
word. -/
theorem lowerCoverNeighbor_unique (a b c : CoverVertex V z)
    (hab : Nonempty (CoverArrow V z a b) ∨ Nonempty (CoverArrow V z b a))
    (hac : Nonempty (CoverArrow V z a c) ∨ Nonempty (CoverArrow V z c a))
    (hb : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a)
    (hc : CoverVertex.rank V z c + 1 = CoverVertex.rank V z a) : b = c := by
  apply CoverVertex.word_injective V z
  have hbw : CoverVertex.word V z b = (CoverVertex.word V z a).dropLast := by
    rcases hab with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact coverArrow_down_word V z f hb
    · exact coverArrow_up_word V z f hb
  have hcw : CoverVertex.word V z c = (CoverVertex.word V z a).dropLast := by
    rcases hac with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact coverArrow_down_word V z f hc
    · exact coverArrow_up_word V z f hc
  exact hbw.trans hcw.symm

end Quiver.FreeGroupoid.OriginalWords
