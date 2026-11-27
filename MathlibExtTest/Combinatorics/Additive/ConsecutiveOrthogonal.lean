/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import MathlibExt.Combinatorics.Additive.ConsecutiveOrthogonal

namespace MetaMathlibExt

/-- A row of two ones forces the block to contain both coordinates. -/
example : ∃ s t : Fin 2, s < t ∧ ∑ _j ∈ Finset.Icc s t, (1 : ZMod 2) = 0 := by
  obtain ⟨s, t, hst, hsum⟩ := exists_consecutive_orthogonal (a := 1) (m := 2)
    (by decide) (fun _ _ => 1)
  refine ⟨s, t, hst.lt_of_ne ?_, hsum 0⟩
  rintro rfl
  simpa using hsum 0

/-- One column below the bound, two alternating rows can have no common zero-sum block. -/
example : ¬ ∃ s t : Fin 3, s ≤ t ∧ ∀ i : Fin 2,
    ∑ j ∈ Finset.Icc s t, (if j.val % 2 = i.val then (1 : ZMod 2) else 0) = 0 := by
  decide

/-- At the threshold for one set, a set containing both endpoints forces the full block. -/
example : ∃ s t : ℕ, 1 ≤ s ∧ s < t ∧ t ≤ 2 ∧ Even (Finset.Icc s t ∩ Finset.range 4).card := by
  obtain ⟨s, t, hs, hst, ht, hev⟩ := exists_consecutive_even_inter (a := 1) (m := 2) le_rfl
    (fun _ => Finset.range 4)
  refine ⟨s, t, hs, hst.lt_of_ne ?_, ht, hev 0⟩
  rintro rfl
  have hsX : s ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  simpa [Finset.singleton_inter_of_mem hsX] using hev 0

/-- With two alternating sets, three positions do not suffice. -/
example : ¬ ∃ s t : Fin 4, 1 ≤ s.val ∧ s ≤ t ∧
    ∀ i : Fin 2, Even (Finset.Icc s.val t.val ∩ ![{1, 3}, {2}] i).card := by
  decide

/-- With no rows, the theorem still gives a nonzero vector in dimension one. -/
example : ∃ w : Fin 1 → ZMod 2, w ≠ 0 :=
  (exists_ne_zero_orthogonal (a := 0) (m := 1) (by decide) Fin.elim0).imp fun _ hw => hw.1

/-- For the row `(1, 1)`, the nonzero witness has coordinate sum zero. -/
example : ∃ w : Fin 2 → ZMod 2, w ≠ 0 ∧ w 0 + w 1 = 0 := by
  obtain ⟨w, hw, hrow⟩ := exists_ne_zero_orthogonal (a := 1) (m := 2)
    (by decide) (fun _ _ => 1)
  exact ⟨w, hw, by simpa only [Fin.sum_univ_two, mul_one] using hrow 0⟩

/-- With no sets, the theorem still gives a nonempty subset of `{1}`. -/
example : ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 1 :=
  (exists_nonempty_even_inter (a := 0) (m := 1) le_rfl Fin.elim0).imp fun _ hY => ⟨hY.1, hY.2.1⟩

/-- For the single set `{1}` and `m = 2`, the witness must avoid `1`. -/
example : ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 2 ∧ 1 ∉ Y := by
  obtain ⟨Y, hne, hsub, hev⟩ := exists_nonempty_even_inter (a := 1) (m := 2) le_rfl ![{1}]
  refine ⟨Y, hne, hsub, fun h1 => ?_⟩
  simpa [Finset.inter_singleton_of_mem h1] using hev 0

/-- The bound `a + 1 ≤ m` is sharp: for `a = m = 2`, the sets `{1}` and `{2}` have no witness. -/
example : ¬ ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 2 ∧
    ∀ i : Fin 2, Even (Y ∩ ![{1}, {2}] i).card := by
  rintro ⟨Y, hne, hsub, hev⟩
  have hY : ∃ Y ∈ (Finset.Icc 1 2).powerset, Y.Nonempty ∧
      ∀ i : Fin 2, Even (Y ∩ ![{1}, {2}] i).card :=
    ⟨Y, Finset.mem_powerset.mpr hsub, hne, hev⟩
  revert hY
  decide

end MetaMathlibExt
