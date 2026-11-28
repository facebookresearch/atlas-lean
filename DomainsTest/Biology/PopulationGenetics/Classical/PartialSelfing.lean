/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.PartialSelfing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter Set Topology
open MathlibExt.Biology.PopulationGenetics.PartialSelfing

-- With no selfing, every generation after the base consists of unrelated outcrosses.
example (t : ℕ) : inbreedingCoeff 0 (3 / 4) (t + 1) = 0 := by
  obtain ⟨_, _, hstep, _, _⟩ := inbreeding_under_partial_selfing
    (S := 0) (F₀ := 3 / 4) (hS := by norm_num) (hF₀ := by norm_num)
  simpa using hstep t

-- Complete selfing halves the non-IBD probability in each generation, even for nonzero `F₀`.
example : inbreedingCoeff 1 (1 / 4) 3 = 29 / 32 ∧
    Tendsto (inbreedingCoeff 1 (1 / 4)) atTop (𝓝 1) := by
  obtain ⟨_, _, _, hfull, _⟩ := inbreeding_under_partial_selfing
    (S := 1) (F₀ := 1 / 4) (hS := by norm_num) (hF₀ := by norm_num)
  obtain ⟨hcomplement, hlim⟩ := hfull rfl
  refine ⟨?_, hlim⟩
  have h := hcomplement 3
  norm_num at h
  linarith

-- At `S = 1/2`, the real fixed point is `1/3` and the centered factor is `1/4`.
example :
    (∀ x : ℝ, (1 / 4) * (1 + x) = x ↔ x = 1 / 3) ∧
      inbreedingCoeff (1 / 2) (2 / 3) 2 = 17 / 48 ∧
      Tendsto (inbreedingCoeff (1 / 2) (2 / 3)) atTop (𝓝 (1 / 3)) := by
  obtain ⟨_, _, _, _, hpartial⟩ := inbreeding_under_partial_selfing
    (S := 1 / 2) (F₀ := 2 / 3) (hS := by norm_num) (hF₀ := by norm_num)
  obtain ⟨hfixed, hcenter, hlim⟩ := hpartial (by norm_num)
  refine ⟨fun x => ?_, ?_, ?_⟩
  · convert hfixed x using 2 <;> norm_num
  · have h := hcenter 2
    norm_num at h
    linarith
  · convert hlim using 2
    norm_num
