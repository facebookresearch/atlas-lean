/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.EffectivePopulationSizeSeparateSexes
import Mathlib.Tactic.NormNum

/-!
# Tests for one-generation effective population size with separate sexes
-/

open MathlibExt.Biology.PopulationGenetics.EffectivePopulationSizeSeparateSexes

-- An unbalanced population has a strictly smaller, nonintegral effective size.
example : collisionProbability 2 3 = 5 / 48 ∧
    (∀ n : ℝ, collisionProbability 2 3 = 1 / (2 * n) ↔ n = 24 / 5) ∧
    (24 / 5 : ℝ) < 5 := by
  obtain ⟨hc, _, hsize, hle, heq⟩ :=
    effective_population_size_separate_sexes 2 3 (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hc ⊢
    exact hc
  · intro n
    rw [hsize]
    norm_num
  · have hlt := lt_of_le_of_ne hle (fun h ↦ (by decide : (2 : ℕ) ≠ 3) (heq.mp h))
    convert hlt using 1 <;> norm_num

-- Equal counts attain the total population size.
example : collisionProbability 3 3 = 1 / 12 ∧
    (∀ n : ℝ, collisionProbability 3 3 = 1 / (2 * n) ↔ n = 6) := by
  obtain ⟨hc, _, hsize, _, heq⟩ :=
    effective_population_size_separate_sexes 3 3 (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · norm_num at hc ⊢
    exact hc
  · intro n
    rw [hsize, heq.mpr rfl]
    norm_num

-- With one parent of each sex, there are four equally likely parental gene copies.
example : collisionProbability 1 1 = 1 / 4 ∧
    (∀ n : ℝ, collisionProbability 1 1 = 1 / (2 * n) ↔ n = 2) := by
  obtain ⟨hc, _, hsize, _, heq⟩ :=
    effective_population_size_separate_sexes 1 1 (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · norm_num at hc ⊢
    exact hc
  · intro n
    rw [hsize, heq.mpr rfl]
    norm_num
