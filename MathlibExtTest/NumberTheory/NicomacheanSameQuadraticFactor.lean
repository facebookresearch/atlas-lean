/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.NicomacheanSameQuadraticFactor

/-! # Tests for Nicomachean families sharing a quadratic factor -/

open MetaMathlibExt

private def shortSeed : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
private def longSeed : List ℤ := [1, 2, 3, 3, 3, 5, 5, 6, 7, 9, 10, 12]

-- Verify the two explicit lists without the family theorem. They are distinct even as bags.
example : (shortSeed : Multiset ℤ) ≠ (longSeed : Multiset ℤ) ∧
    (∀ x ∈ shortSeed, 0 < x) ∧ (∀ x ∈ longSeed, 0 < x) ∧
    shortSeed.sum = 66 ∧ longSeed.sum = 66 ∧
    nicomacheanNu shortSeed = 0 ∧ nicomacheanNu longSeed = 0 := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · intro h
    have hc : (11 : ℕ) ≠ 12 := by decide
    exact hc (congrArg Multiset.card h)
  · norm_num [shortSeed, List.forall_mem_cons]
  · norm_num [longSeed, List.forall_mem_cons]

-- Verify the full formula for each witness using its computed sum and defect.
example (a b : ℤ) :
    nicomacheanNu (shortSeed ++ [a, b]) = -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 132) ∧
    nicomacheanNu (longSeed ++ [a, b]) = -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 132) := by
  have h (s : List ℤ) (hs : s.sum = 66) (hν : nicomacheanNu s = 0) :
      nicomacheanNu (s ++ [a, b]) = -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 132) := by
    rw [nicomacheanNu_append, hs, hν]
    simp only [List.sum_cons, List.sum_nil, add_zero, List.map_cons, List.map_nil, zero_add]
    ring
  exact ⟨h shortSeed (by decide) (by decide), h longSeed (by decide) (by decide)⟩

-- Compute both zero factors and a nonzero value without either public theorem.
example : nicomacheanNu (shortSeed ++ [2, -2]) = 0 ∧
    nicomacheanNu (longSeed ++ [13, 12]) = 0 ∧
    nicomacheanNu (shortSeed ++ [2, -1]) = 126 ∧
    nicomacheanNu (longSeed ++ [2, -1]) = 126 := by
  decide

-- Concatenation also works with nonzero initial defect and a tail of length three.
example : nicomacheanNu ([2] ++ [1, -2, 3] : List ℤ) = -12 ∧
    nicomacheanNu ([2] : List ℤ) + (2 * ([2] : List ℤ).sum + ([1, -2, 3] : List ℤ).sum) *
      ([1, -2, 3] : List ℤ).sum - (([1, -2, 3] : List ℤ).map (· ^ 3)).sum = -12 := by
  decide

-- The empty family satisfies the claim without applying the general theorem.
example : ∃ σ : Fin 0 → List ℤ, Function.Injective (fun i => (σ i : Multiset ℤ)) ∧
    ∃ c : ℤ, ∀ i, (∀ x ∈ σ i, 0 < x) ∧ nicomacheanNu (σ i) = 0 ∧
      ∀ a b : ℤ, nicomacheanNu (σ i ++ [a, b]) =
        -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 2 * c) :=
  ⟨Fin.elim0, fun i => i.elim0, 0, fun i => i.elim0⟩

-- A client can use the common factor to obtain equal defects across three lists.
example : ∃ σ : Fin 3 → List ℤ, Function.Injective (fun i => (σ i : Multiset ℤ)) ∧
    ∀ i j, nicomacheanNu (σ i ++ [2, -1]) = nicomacheanNu (σ j ++ [2, -1]) := by
  obtain ⟨σ, hinj, c, h⟩ := exists_nicomachean_family_same_quadratic_factor 3
  exact ⟨σ, hinj, fun i j => ((h i).2.2 2 (-1)).trans (((h j).2.2 2 (-1)).symm)⟩
