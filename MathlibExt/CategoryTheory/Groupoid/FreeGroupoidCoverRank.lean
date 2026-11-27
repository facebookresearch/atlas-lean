/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverQuiver

/-!
# Actual original covering-graph reduced-word rank

The rank of a native cover vertex is its full original reduced-label
word length. Every original generating cover arrow changes rank by
exactly one, using the complete native original append/cancel formula.
No tree, finite generation or weak outcome is supplied.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- The actual full original reduced-word length of a native cover vertex. -/
def CoverVertex.rank (a : CoverVertex V z) : ℕ := (CoverVertex.word V z a).length

/-- Every SAME original cover-arrow target is its whole native original generator append. -/
lemma coverArrow_target_eq_append {a b : CoverVertex V z} (f : CoverArrow V z a b) :
    b = CoverVertex.append V z a f.arrow := by
  cases b with
  | mk y p =>
    have he := f.path_eq
    exact congrArg (fun h => (⟨y, h⟩ : CoverVertex V z)) he.symm

/-- Every actual original generating cover edge changes the SAME full native rank by one. -/
theorem coverArrow_rank_step {a b : CoverVertex V z} (f : CoverArrow V z a b) :
    CoverVertex.rank V z b + 1 = CoverVertex.rank V z a ∨
      CoverVertex.rank V z a + 1 = CoverVertex.rank V z b := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have he := CoverVertex.append_word V z a f.arrow
  have hb := coverArrow_target_eq_append V z f
  have hw : CoverVertex.word V z b = if (CoverVertex.word V z a).getLast? =
    some (⟨a.target, b.target, f.arrow⟩,
    false) then
      (CoverVertex.word V z a).dropLast else (CoverVertex.word V z a).concat (⟨a.target,
        b.target, f.arrow⟩, true) := by
    exact (congrArg (CoverVertex.word V z) hb).trans he
  by_cases h : (CoverVertex.word V z a).getLast? = some (⟨a.target, b.target, f.arrow⟩, false)
  · have hne : CoverVertex.word V z a ≠ [] := by intro hn; rw [hn] at h; cases h
    have hl := congrArg List.length hw
    rw [ite_eq_left h, List.length_dropLast] at hl
    left
    unfold CoverVertex.rank
    have hp : 0 < (CoverVertex.word V z a).length := by
      cases hw : CoverVertex.word V z a with
      | nil => exact False.elim (hne hw)
      | cons l L => exact Nat.zero_lt_succ _
    omega
  · have hl := congrArg List.length hw
    rw [ite_eq_right h, List.length_concat] at hl
    exact Or.inr hl.symm

end Quiver.FreeGroupoid.OriginalWords
