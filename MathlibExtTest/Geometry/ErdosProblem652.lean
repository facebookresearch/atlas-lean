/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.ErdosProblem652

open MathlibExt.Geometry.ErdosProblem652Wanted

-- Each point of a pair sees exactly one distance. Equality at the threshold is excluded.
example (a b : Plane) (hab : a ≠ b) :
    countSmallPoints {a, b} 1 = 0 ∧ countSmallPoints {a, b} 2 = 2 := by
  classical
  have one (x y : Plane) (h : x ≠ y) : distinctDistancesFrom {x, y} x = 1 := by
    unfold distinctDistancesFrom
    apply Finset.card_eq_one.mpr
    refine ⟨dist y x, ?_⟩
    ext r
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have ha := one a b hab
  have hb : distinctDistancesFrom {a, b} b = 1 := by
    rw [Finset.pair_comm]
    exact one b a hab.symm
  simp [countSmallPoints, Finset.filter_insert, Finset.filter_singleton, ha, hb, hab]

-- With zero required pins, every real constant is admissible, including negative constants.
example : erdosAlpha 0 = 0 := by
  have h (c : ℝ) : isAdmissibleBound 0 c := by
    refine ⟨0, fun n _ => ?_⟩
    obtain ⟨X, hX⟩ := Finset.exists_card_eq (α := Plane) n
    exact ⟨X, hX, Nat.zero_le _⟩
  simp [erdosAlpha, h]

example (b : ℝ) : ∃ k₀ : ℕ, ∀ k ≥ k₀, b ≤ erdosAlpha k :=
  Filter.tendsto_atTop_atTop.mp conjecture_holds b
