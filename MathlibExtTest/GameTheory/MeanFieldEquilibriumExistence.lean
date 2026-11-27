/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MeanFieldEquilibriumExistence

open MathlibExt.GameTheory.MeanFieldEquilibrium
open MathlibExt.GameTheory.MeanFieldEquilibriumWanted

/-- On a singleton, all probability vectors coincide, so even a negative bound works. -/
example (F : (Unit → ℝ) → Unit → ℝ) : ∃ m, IsMeanFieldEquilibrium F m := by
  apply exists_isMeanFieldEquilibrium F (-1)
  intro m₁ m₂ hm₁ hm₂ y
  have heq : m₁ = m₂ := by
    funext u
    calc m₁ u = 1 := by simpa using hm₁.2
         _ = m₂ u := by simpa using hm₂.2.symm
  simp [heq]

/-- Two-state crowd aversion has an equilibrium for any extension of its cost off the simplex. -/
example (F : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (h : ∀ m : Fin 2 → ℝ, (∀ y, 0 ≤ m y) → ∑ y, m y = 1 → ∀ y, F m y = m y) :
    ∃ m, IsMeanFieldEquilibrium F m := by
  apply exists_isMeanFieldEquilibrium F 1
  intro m₁ m₂ hm₁ hm₂ y
  rw [h m₁ hm₁.1 hm₁.2, h m₂ hm₂.1 hm₂.2, one_mul]
  exact Finset.single_le_sum (f := fun z => |m₁ z - m₂ z|)
    (fun z _ => abs_nonneg _) (Finset.mem_univ y)
