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

-- Selecting the horizontal side of this triangle gives the one-entry profile [2].
open Classical in
example :
    let P : Finset (ℝ × ℝ) := {a, b, (0, 1)}
    P.card = 3 ∧ (P.filter (· ∈ line[ℝ, a, b])).card = 2 := by
  have hoff : ((0, 1) : ℝ × ℝ) ∉ line[ℝ, a, b] := by
    intro h
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
    have hsnd := congrArg Prod.snd ht
    norm_num [a, b, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.snd_add,
      Prod.snd_smul, Prod.snd_sub] at hsnd
  dsimp only
  constructor
  · simp [a, b]
  · simp only [Finset.filter_insert, Finset.filter_singleton, left_mem_affineSpan_pair,
      right_mem_affineSpan_pair, hoff, ite_true, ite_false]
    simp [a, b]

-- No three-point set has [2] as its complete profile.
example (P : Finset (ℝ × ℝ)) (hP : P.card = 3) : lineSizes P ≠ {2} := by
  classical
  intro h
  let lines := P.offDiag.image fun pq => line[ℝ, pq.1, pq.2]
  have hone : lines.card = 1 := by
    simpa only [lines, lineSizes, Multiset.card_map, Multiset.card_singleton, Finset.card_val]
      using congrArg Multiset.card h
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hone
  have hall : (P.filter (· ∈ ℓ)) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨q, hq, hne⟩ := P.exists_mem_ne (by omega) p
    have hpq : line[ℝ, p, q] ∈ lines :=
      Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hne.symm⟩, rfl⟩
    rw [hℓ, Finset.mem_singleton] at hpq
    exact hpq ▸ left_mem_affineSpan_pair ℝ p q
  change lines.val.map (fun l => (P.filter (· ∈ l)).card) = {2} at h
  simp [hℓ, hall, hP] at h

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
