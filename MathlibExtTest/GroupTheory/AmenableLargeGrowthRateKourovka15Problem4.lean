/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.GroupTheory.AmenableLargeGrowthRateKourovka15Problem4

open MathlibExt.GroupTheory.AmenableLargeGrowthRateKourovka15Problem4Wanted

-- The definition still works above the universe used for counterexamples.
example {Γ : Type 1} [Group Γ] {k : ℕ} (S : Group.Generators Γ (Fin k)) :
    growthRate S =
      Filter.limsup (fun n : ℕ => (Nat.card {g : Γ // S.wordLength g ≤ n} : ℝ) ^ ((1 : ℝ) / n))
        Filter.atTop := rfl

-- Refuting the original proposition yields actual witnesses, strictly above any positive gap.
private theorem exists_strictWitness (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (Γ : Type) (_ : Group Γ) (S : Group.Generators Γ (Fin k)),
      Function.Injective S.val ∧ 2 * (k : ℝ) - 1 - δ < growthRate S ∧ IsAmenable Γ := by
  by_contra h
  apply largeGrowthRateImpliesNonamenable_refuted
  refine ⟨k, hk, δ / 2, by linarith, ?_⟩
  intro Γ inst S hS hg ham
  exact h ⟨Γ, inst, S, hS, by linarith, ham⟩

-- Minimum rank and a threshold requiring exponential growth.
example : ∃ (Γ : Type) (_ : Group Γ) (S : Group.Generators Γ (Fin 2)),
    Function.Injective S.val ∧ (5 : ℝ) / 2 < growthRate S ∧ IsAmenable Γ := by
  obtain ⟨Γ, inst, S, hinj, hg, ham⟩ := exists_strictWitness 2 le_rfl (1 / 2) (by norm_num)
  refine ⟨Γ, inst, S, hinj, ?_, ham⟩
  norm_num at hg
  linarith
