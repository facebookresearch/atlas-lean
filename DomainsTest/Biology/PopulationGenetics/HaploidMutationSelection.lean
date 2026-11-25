/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.HaploidMutationSelection
import Mathlib.Tactic.NormNum

open Filter Set
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics

private noncomputable def step (s u p : ℝ) : ℝ := p * (1 - u) / (1 - (1 - p) * s)

-- The lethal all-mutant state is not an equilibrium, even though Lean's quotient is zero there.
example : ¬ (0 < (1 : ℝ) - (1 - 0) * 1 ∧ step 1 (1 / 4) 0 = 0) := by
  obtain ⟨_, _, hfixed, _⟩ := haploid_mutation_selection_balance
    (s := 1) (u := 1 / 4) (by norm_num) le_rfl (by norm_num) (by norm_num)
  intro h
  have h' := (hfixed 0 (by norm_num [Set.mem_Icc])).1 h
  norm_num at h'

-- Starting at wild-type fixation in the lethal case reaches the interior fixed point in one step.
example : step 1 (1 / 4) 1 = 3 / 4 ∧ step 1 (1 / 4) (3 / 4) = 3 / 4 := by
  obtain ⟨_, _, _, _, hlethal, _⟩ := haploid_mutation_selection_balance
    (s := 1) (u := 1 / 4) (by norm_num) le_rfl (by norm_num) (by norm_num)
  constructor
  · change (fun p : ℝ ↦ p * (1 - 1 / 4) / (1 - (1 - p) * 1)) 1 = 3 / 4
    rw [hlethal rfl 1 (by norm_num [Set.mem_Ioc])]
    norm_num
  · change (fun p : ℝ ↦ p * (1 - 1 / 4) / (1 - (1 - p) * 1)) (3 / 4) = 3 / 4
    rw [hlethal rfl (3 / 4) (by norm_num [Set.mem_Ioc])]
    norm_num

-- Nonlethal selection has both equilibria; an orbit starting below the positive one increases.
example :
    step (1 / 2) (1 / 8) 0 = 0 ∧
    step (1 / 2) (1 / 8) (3 / 4) = 3 / 4 ∧
    (1 / 2 : ℝ) < step (1 / 2) (1 / 8) (1 / 2) ∧
    Monotone (fun n : ℕ ↦ (step (1 / 2) (1 / 8))^[n] (1 / 2)) := by
  obtain ⟨_, _, hfixed, _, _, hsign, hbalance, _⟩ := haploid_mutation_selection_balance
    (s := 1 / 2) (u := 1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hzero := (hfixed 0 (by norm_num [Set.mem_Icc])).2 (Or.inl ⟨by norm_num, rfl⟩)
  have hpos := (hfixed (3 / 4) (by norm_num [Set.mem_Icc])).2 (Or.inr ⟨by norm_num, by norm_num⟩)
  have hhalf : (1 / 2 : ℝ) ∈ Ioc 0 1 := by norm_num [Set.mem_Ioc]
  have hinc := ((hsign (1 / 2) hhalf).1).2 (by norm_num)
  obtain ⟨_, _, _, _, horbit⟩ := hbalance (by norm_num)
  exact ⟨hzero.2, hpos.2, hinc, (horbit (1 / 2) hhalf).2.1 (by norm_num)⟩

-- The all-wild-type start decreases to the interior equilibrium; its load equals the mutation rate.
example :
    Tendsto (fun n : ℕ ↦ (step (1 / 2) (1 / 8))^[n] 1) atTop (𝓝 (3 / 4)) ∧
    Antitone (fun n : ℕ ↦ (step (1 / 2) (1 / 8))^[n] 1) ∧
    1 - (1 - (1 - (3 / 4 : ℝ)) * (1 / 2)) = 1 / 8 := by
  obtain ⟨_, _, _, _, _, _, hbalance, _⟩ := haploid_mutation_selection_balance
    (s := 1 / 2) (u := 1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (1 : ℝ) - (1 / 8) / (1 / 2) = 3 / 4 := by norm_num
  obtain ⟨_, _, _, hload, horbit⟩ := hbalance (by norm_num)
  have h := horbit 1 (by norm_num [Set.mem_Ioc])
  refine ⟨?_, h.2.2 (by norm_num), ?_⟩
  · have hlim : Tendsto (fun n : ℕ ↦ (step (1 / 2) (1 / 8))^[n] 1) atTop
        (𝓝 ((1 : ℝ) - (1 / 8) / (1 / 2))) := h.1
    rwa [he] at hlim
  · change 1 - (1 - (1 - (1 - (1 / 8 : ℝ) / (1 / 2))) * (1 / 2)) = 1 / 8 at hload
    rwa [he] at hload

-- At the threshold u = s the wild type tends to zero, but stays positive at every finite step.
example :
    Tendsto (fun n : ℕ ↦ (step (1 / 2) (1 / 2))^[n] 1) atTop (𝓝 0) ∧
    StrictAnti (fun n : ℕ ↦ (step (1 / 2) (1 / 2))^[n] 1) ∧
    ∀ n : ℕ, 0 < (step (1 / 2) (1 / 2))^[n] 1 := by
  obtain ⟨_, hstay, _, _, _, _, _, hthreshold⟩ := haploid_mutation_selection_balance
    (s := 1 / 2) (u := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₁ : (1 : ℝ) ∈ Ioc 0 1 := by norm_num [Set.mem_Ioc]
  have h := hthreshold le_rfl 1 h₁
  exact ⟨h.1, h.2, fun n ↦ (hstay 1 h₁ n).1⟩

end MathlibExt.Biology.PopulationGenetics
