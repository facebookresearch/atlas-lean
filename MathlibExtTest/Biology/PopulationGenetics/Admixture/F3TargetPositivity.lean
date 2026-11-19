/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.F3TargetPositivity

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture

open MathlibExt.Biology.PopulationGenetics.Admixture

/-! Boundary tests for target-only `f3` positivity. -/

/-- Non-vacuity with a genuinely admixed (non-binary) source: one edge of
length `2`, target weight `1`, source weights `1/2` and `1/4` give the
strictly positive value `3/4`, and the core lemma applies. -/
example :
    (0 : ℝ) ≤ ∑ _e : Fin 1, ((1 : ℝ) - 1 / 2) * (1 - 1 / 4) * 2 ∧
      (∑ _e : Fin 1, ((1 : ℝ) - 1 / 2) * (1 - 1 / 4) * 2) = 3 / 4 := by
  constructor
  · exact sum_nonneg_of_target_binary (fun _ => 2) (fun _ => 1) (fun _ => 1 / 2)
      (fun _ => 1 / 4) (fun _ => by norm_num) (fun _ => Or.inr rfl)
      (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
      (fun _ => by norm_num)
  · norm_num

/-- Endpoint case `wC = 0`: the term reduces to `wA * wB * len ≥ 0`. -/
example :
    (0 : ℝ) ≤ ∑ _e : Fin 1, ((0 : ℝ) - 1 / 3) * (0 - 1 / 5) * 7 :=
  sum_nonneg_of_target_binary (fun _ => 7) (fun _ => 0) (fun _ => 1 / 3)
    (fun _ => 1 / 5) (fun _ => by norm_num) (fun _ => Or.inl rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num)

/-- Sharpness: without binary target weights the conclusion fails; with
`wC = 1/2`, `wA = 1`, `wB = 0`, `len = 1`, the single term is `-1/4 < 0`. -/
example :
    (∑ _e : Fin 1, ((1 / 2 : ℝ) - 1) * (1 / 2 - 0) * 1) < 0 := by
  norm_num

/-- Zero drift lengths give `f3`-sum `0`. -/
example :
    (∑ _e : Fin 2, ((fun _ => (1 : ℝ)) _e - 1 / 2) * (1 - 1 / 4) * 0) = 0 := by
  simp

end MathlibExtTest.Biology.PopulationGenetics.Admixture
