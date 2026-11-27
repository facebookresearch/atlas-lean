/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703

/-! # Tests for the Frankl–Rödl forbidden intersection theorem -/

namespace MathlibExtTest.Combinatorics.ForbiddenIntersectionErdosProblem703

open MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703Wanted

example :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n r : ℕ, ε * n < r → (r : ℝ) < (1 / 2 - ε) * n →
      ∀ F : Finset (Finset (Fin n)), (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) →
        (F.card : ℝ) < (2 - δ) ^ n :=
  forbiddenIntersectionExponentialGap_holds

-- All eight singleton sets avoid intersection size two, even on the diagonal.
example : ∃ δ : ℝ, 0 < δ ∧ (8 : ℝ) < (2 - δ) ^ 8 := by
  let F : Finset (Finset (Fin 8)) :=
    Finset.univ.map ⟨fun a => {a}, Finset.singleton_injective⟩
  have hcard : F.card = 8 := by simp [F]
  obtain ⟨δ, hδ, hbound⟩ :=
    forbiddenIntersectionExponentialGap_holds (1 / 8) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  have h := hbound 8 2 (by norm_num) (by norm_num) F ?_
  · simpa only [hcard, Nat.cast_ofNat] using h
  · intro A hA B _
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hA
    change ({a} ∩ B).card ≠ 2
    have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := {a}) (s₂ := B))
    simp only [Finset.card_singleton] at hle
    omega

end MathlibExtTest.Combinatorics.ForbiddenIntersectionErdosProblem703
