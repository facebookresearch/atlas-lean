/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BalancedMinimumEvolutionDefs
-- Real arithmetic on the balanced minimum-evolution lengths.
import Mathlib.Tactic.NormNum
-- Case analysis on the species `Fin 2`.
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution (RTree UTree pauplinCoeff)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BalancedMinimumEvolutionInstance) :
    balancedMinimumEvolutionDec (bitEncode i) = true ↔
      WellFormed i ∧ BalancedMinimumEvolutionFeasible i := by
  simp [balancedMinimumEvolutionDec, bitDecode_bitEncode]

/-- Two species at dissimilarity `1`, with bound `L = a / b`. -/
private abbrev two (a b : ℕ) : BalancedMinimumEvolutionInstance :=
  (2, [[(0, 1), (1, 1)], [(1, 1), (0, 1)]], (a, b))

/-- Three species at mutual dissimilarity `1`, with bound `L = 3 / 2`. -/
private abbrev three : BalancedMinimumEvolutionInstance :=
  (3, [[(0, 1), (1, 1), (1, 1)], [(1, 1), (0, 1), (1, 1)], [(1, 1), (1, 1), (0, 1)]], (3, 2))

example : WellFormed (two 1 2) := by unfold WellFormed entry; decide

example : WellFormed three := by unfold WellFormed entry; decide

/-- Distinct species of `two` are at dissimilarity `1`. -/
private theorem two_dissim (a b : ℕ) {x y : Fin 2} (h : x ≠ y) : dissim (two a b) x y = 1 := by
  revert h
  fin_cases x <;> fin_cases y <;> simp [dissim, entry]

/-- The tree with the two leaves `x` and `y` on the ends of its root edge has balanced
minimum-evolution length `1` when `x ≠ y`. -/
private theorem two_bmeLength (a b : ℕ) (len : ℝ) {x y : Fin 2} (h : x ≠ y) :
    (UTree.mk (.leaf x) len (.leaf y)).bmeLength (dissim (two a b)) = 1 := by
  simp [UTree.bmeLength, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff,
    two_dissim a b h, two_dissim a b (Ne.symm h)]

/-- Yes-instance (two species): the tree joining the two leaves has length `1 ≤ 1`. -/
example : balancedMinimumEvolutionDec (bitEncode (two 1 1)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed entry; decide,
    ⟨.leaf 0, 1, .leaf 1⟩, by decide, ?_⟩
  rw [two_bmeLength 1 1 1 (by decide)]
  norm_num

/-- Yes-instance (three species): the tree `((0, 1), 2)` has every pair of leaves at
topological distance `2`, so its length is `3 · (1 / 2) = 3 / 2 ≤ 3 / 2`. -/
example : balancedMinimumEvolutionDec (bitEncode three) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed entry; decide,
    ⟨.node 1 (.leaf 0) 1 (.leaf 1), 1, .leaf 2⟩, by decide, ?_⟩
  simp [UTree.bmeLength, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff, dissim, entry]
  norm_num

/-- A rooted binary tree has at least one leaf, and a `node` has at least two. -/
private theorem leaves_length_pos {X : Type} (t : RTree X) : 0 < t.leaves.length := by
  induction t with
  | leaf x => simp [RTree.leaves]
  | node a l b r ihl _ => simp [RTree.leaves]; omega

/-- A rooted binary tree with exactly one leaf is a leaf. -/
private theorem eq_leaf_of_length_one {X : Type} {t : RTree X} (h : t.leaves.length = 1) :
    ∃ x, t = .leaf x := by
  cases t with
  | leaf x => exact ⟨x, rfl⟩
  | node a l b r =>
    have := leaves_length_pos l
    have := leaves_length_pos r
    simp [RTree.leaves] at h
    omega

/-- Every tree on the two species joins them by one edge and has length `1 > 1 / 2`. -/
private theorem two_half_not_feasible : ¬ BalancedMinimumEvolutionFeasible (two 1 2) := by
  rintro ⟨T, hperm, hle⟩
  obtain ⟨l, len, r⟩ := T
  have hlen := hperm.length_eq
  simp only [UTree.labels, List.length_append, List.length_map, List.length_finRange] at hlen
  have hl := leaves_length_pos l
  have hr := leaves_length_pos r
  obtain ⟨x, rfl⟩ := eq_leaf_of_length_one (t := l) (by omega)
  obtain ⟨y, rfl⟩ := eq_leaf_of_length_one (t := r) (by omega)
  have hxy : x ≠ y := by
    have hnd := hperm.nodup_iff.2 (List.nodup_finRange 2)
    simpa [UTree.labels, RTree.leaves] using hnd
  rw [two_bmeLength 1 2 len hxy] at hle
  norm_num at hle

/-- No-instance: well formed, but every tree on two species has length `1 > L = 1 / 2`. -/
example : balancedMinimumEvolutionDec (bitEncode (two 1 2)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => two_half_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: an asymmetric matrix (`δ₀₁ = 1`, `δ₁₀ = 2`) is rejected. -/
example : balancedMinimumEvolutionDec (bitEncode
    ((2, [[(0, 1), (1, 1)], [(2, 1), (0, 1)]], (2, 1)) : BalancedMinimumEvolutionInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed entry
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BalancedMinimumEvolutionInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : balancedMinimumEvolutionDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution
