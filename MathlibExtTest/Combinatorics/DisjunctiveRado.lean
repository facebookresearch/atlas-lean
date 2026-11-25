/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DisjunctiveRado

open MathlibExt.Combinatorics.DisjunctiveRadoWanted

-- With the smallest admissible parameters, a single ordinary part fills every gap.
example (N : ℕ) (hN : N ≤ 8) : ∃ x y : ℕ, x ≤ 2 ∧ y ≤ 2 ∧ x + 3 * y = N := by
  obtain ⟨x, y, hx, hy, hsum⟩ := exists_bounded_rep 3 2 1 N (by decide) (by decide) (by decide) hN
  exact ⟨x 0, y, hx 0 (by decide), hy, by simpa using hsum⟩

-- At the top of the two-part range the scaled part must attain its cap.
example (N : ℕ) (hlo : 8 ≤ N) (hhi : N ≤ 10) :
    ∃ u v : ℕ, u ≤ 2 ∧ v ≤ 2 ∧ u + v + 3 * 2 = N := by
  obtain ⟨x, y, hx, hy, hsum⟩ := exists_bounded_rep 3 2 2 N (by decide) (by decide) (by decide) hhi
  have h₀ := hx 0 (by decide)
  have h₁ := hx 1 (by decide)
  simp [Finset.sum_range_succ] at hsum
  exact ⟨x 0, x 1, h₀, h₁, by omega⟩

-- Reducing the cap below a - 1 leaves a gap even with one ordinary part.
example : ¬ ∃ x y : ℕ, x ≤ 1 ∧ y ≤ 1 ∧ x + 3 * y = 2 := by
  rintro ⟨x, y, hx, hy, hsum⟩
  omega

-- An empty set of target constants admits no bound for the coloring problem.
example (m : ℕ) (a : ℤ) : disjRadoSet m a ∅ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro R hR
  obtain ⟨c, hc, _⟩ := hR.2 (fun _ => false)
  exact Finset.notMem_empty c hc
