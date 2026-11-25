/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179

/-! # Tests for `MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179` -/

namespace MathlibExtTest.RandomSubsetSumsBalancedErdosProblem1179

open Filter Finset MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179Wanted

-- Test section: subset-sum counts. The empty set has one subset, the empty one, with sum `0`.
example {G : Type*} [AddCommGroup G] : subsetSumCount (∅ : Finset G) 0 = 1 := by
  simp [subsetSumCount, Finset.filter_singleton]

example {G : Type*} [AddCommGroup G] {g : G} (hg : g ≠ 0) :
    subsetSumCount (∅ : Finset G) g = 0 := by
  simp [subsetSumCount, Finset.filter_singleton, Ne.symm hg]

private lemma powerset_one : ({1} : Finset (ZMod 2)).powerset = {∅, {1}} := by decide

-- In `ZMod 2`, the two subsets of `{1}` have the sums `0` and `1`.
private lemma subsetSumCount_one (g : ZMod 2) : subsetSumCount ({1} : Finset (ZMod 2)) g = 1 := by
  rw [subsetSumCount, powerset_one]
  rcases (by decide : ∀ g : ZMod 2, g = 0 ∨ g = 1) g with rfl | rfl
  · simp [Finset.filter_insert, Finset.filter_singleton, show (1 : ZMod 2) ≠ 0 by decide]
  · simp [Finset.filter_insert, Finset.filter_singleton, show (0 : ZMod 2) ≠ 1 by decide]

-- Test section: balanced sets. Every element of `ZMod 2` is the sum of exactly one subset of
-- `{1}`, which is the mean `2 ^ 1 / 2`: the set is `0`-balanced.
example : IsBalanced 0 ({1} : Finset (ZMod 2)) := by
  intro g
  simp [subsetSumCount_one g, ZMod.card]

-- The empty set misses `1`, so it is not `1/2`-balanced in `ZMod 2`.
example : ¬ IsBalanced (1 / 2) (∅ : Finset (ZMod 2)) := by
  intro h
  have h1 := h 1
  have : subsetSumCount (∅ : Finset (ZMod 2)) 1 = 0 := by
    simp [subsetSumCount, Finset.filter_singleton, show (0 : ZMod 2) ≠ 1 by decide]
  rw [this] at h1
  norm_num [ZMod.card, abs_of_neg] at h1

-- Test section: the probability. With more than `|G|` elements there is no subset, and the
-- quotient `0 / 0` is `0`.
example (ε : ℝ) : balancedProbability (ZMod 2) ε 3 = 0 := by
  have : (univ : Finset (ZMod 2)).powersetCard 3 = ∅ :=
    Finset.powersetCard_eq_empty.2 (by simp [ZMod.card])
  simp [balancedProbability, this]

-- Test section: Erdős Problem 1179. The lower bound: a `1/2`-balanced subset of `ZMod 4` has at
-- least two elements.
example (A : Finset (ZMod 4)) (hA : IsBalanced (1 / 2) A) : 4 ≤ 2 ^ A.card := by
  have := (balancedSubsetSumsThresholdLogTwo_holds (1 / 2) (by norm_num) (by norm_num)).2
    (ZMod 4) A hA
  simpa [ZMod.card] using this

-- The upper bound along the cyclic groups `ZMod (i + 1)`: random subsets of the chosen sizes are
-- `1/2`-balanced with probability tending to `1`.
example : ∃ k : ℕ → ℕ, Tendsto (fun N : ℕ => (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
    Tendsto (fun i => balancedProbability (ZMod (i + 1)) (1 / 2) (k (i + 1))) atTop (nhds 1) := by
  obtain ⟨⟨k, hk, hG⟩, -⟩ :=
    balancedSubsetSumsThresholdLogTwo_holds (1 / 2) (by norm_num) (by norm_num)
  refine ⟨k, hk, ?_⟩
  have := hG (fun i => ZMod (i + 1)) (by simpa [ZMod.card] using tendsto_add_atTop_nat 1)
  simpa [ZMod.card] using this

end MathlibExtTest.RandomSubsetSumsBalancedErdosProblem1179
