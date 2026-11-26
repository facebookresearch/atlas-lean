/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733
import Mathlib.Tactic.NormNum

/-! # Tests for line-compatible sequences -/

namespace MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted.Tests

private def a : ℝ × ℝ := (0, 0)
private def b : ℝ × ℝ := (1, 0)
private def c : ℝ × ℝ := (2, 0)

-- All ordered pairs of three collinear points give the same line.
example : lineSizes ({a, b, c} : Finset (ℝ × ℝ)) = {3} := by
  classical
  have hab : a ≠ b := by norm_num [a, b, Prod.mk.injEq]
  have hbc : b ≠ c := by norm_num [b, c, Prod.mk.injEq]
  have hac : a ≠ c := by norm_num [a, c, Prod.mk.injEq]
  have hb : b ∈ line[ℝ, a, c] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨1/2, Prod.ext ?_ ?_⟩ <;>
      norm_num [a, b, c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.fst_add,
        Prod.snd_add, Prod.fst_smul, Prod.snd_smul, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  have h₁ : line[ℝ, a, b] = line[ℝ, a, c] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ..) hb hab
  have h₂ : line[ℝ, b, c] = line[ℝ, a, c] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hb (right_mem_affineSpan_pair ..) hbc
  let P : Finset (ℝ × ℝ) := {a, b, c}
  have hlines :
      (P.offDiag.image fun pq => line[ℝ, pq.1, pq.2]) = {line[ℝ, a, c]} := by
    ext l
    simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨p, q⟩, ⟨hp, hq, hne⟩, rfl⟩
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with (rfl | rfl | rfl) <;> rcases hq with (rfl | rfl | rfl) <;>
        first | contradiction | exact h₁ | exact h₂ | rfl |
          rw [AffineSubspace.affineSpan_pair_comm (p₁ := c) (p₂ := a)] |
          rw [AffineSubspace.affineSpan_pair_comm (p₁ := b) (p₂ := a), h₁] |
          rw [AffineSubspace.affineSpan_pair_comm (p₁ := c) (p₂ := b), h₂]
    · rintro rfl
      exact ⟨(a, c), ⟨by simp [P], by simp [P], hac⟩, rfl⟩
  have hpoints : (P.filter fun r => r ∈ line[ℝ, a, c]) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with (rfl | rfl | rfl)
    · exact left_mem_affineSpan_pair ..
    · exact hb
    · exact right_mem_affineSpan_pair ..
  have hcard : P.card = 3 := by simp [P, hab, hbc, hac]
  change lineSizes P = _
  rw [lineSizes, hlines]
  simp [hpoints, hcard]

example : lineCompatibleCount 0 = 1 := by
  classical
  have h : {X : Multiset ℕ | ∃ P : Finset (ℝ × ℝ), P.card = 0 ∧ lineSizes P = X} =
      {(0 : Multiset ℕ)} := by
    ext X
    simp [Finset.card_eq_zero, lineSizes, eq_comm]
  rw [lineCompatibleCount, h, Set.ncard_singleton]

example : ∃ C : ℝ, ∀ n : ℕ, (lineCompatibleCount n : ℝ) ≤ Real.exp (C * Real.sqrt n) :=
  lineCompatibleCountSubexponential_holds

end MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted.Tests
