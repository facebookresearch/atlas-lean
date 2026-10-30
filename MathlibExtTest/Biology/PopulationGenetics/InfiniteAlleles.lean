/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.InfiniteAlleles

@[expose] public section

open Filter Topology MathlibExt.Biology.PopulationGenetics.InfiniteAlleles

namespace MathlibExtTest.Biology.PopulationGenetics.InfiniteAlleles

/-! ### Concrete parameters (non-vacuity witness)

`M = 2` gene copies (one diploid individual) and `u = 1/2`: `F' = (1/4)(1/2 + F/2)`, with fixed
point `F* = (1/4) / (2 - 1/4) = 1/7`. -/

example : eqHomozygosity 2 (1 / 2) = 1 / 7 := by
  norm_num [eqHomozygosity]

example : homozygosityStep 2 (1 / 2) (1 / 7) = 1 / 7 := by
  norm_num [homozygosityStep]

example : homozygosityStep 2 (1 / 2) 1 = 1 / 4 := by
  norm_num [homozygosityStep]

example : homozygosityStep 2 (1 / 2) (eqHomozygosity 2 (1 / 2)) = eqHomozygosity 2 (1 / 2) :=
  homozygosityStep_eqHomozygosity (by norm_num) (by norm_num) (by norm_num)

/-- `F = 1` is not a fixed point when `u > 0`: mutation keeps creating new alleles. -/
example : homozygosityStep 2 (1 / 2) 1 ≠ 1 := by
  norm_num [homozygosityStep]

/-! ### Boundary cases -/

/-- `u = 1`: every copy mutates, so no two copies are identical. -/
example (M : ℕ) : eqHomozygosity M 1 = 0 := by
  simp [eqHomozygosity]

/-- `M = 1`: the two sampled copies always share the parent, `F* = (1 - u)²`. -/
example (u : ℝ) : eqHomozygosity 1 u = (1 - u) ^ 2 := by
  simp [eqHomozygosity]

/-! ### Convergence and the large-population limit -/

example (F₀ : ℝ) : Tendsto (fun t : ℕ => (homozygosityStep 2 (1 / 2))^[t] F₀) atTop
    (𝓝 (eqHomozygosity 2 (1 / 2))) :=
  tendsto_iterate_homozygosityStep (by norm_num) (by norm_num) (by norm_num) F₀

example : Tendsto (fun N : ℕ => eqHomozygosity (2 * N) (1 / (4 * N))) atTop (𝓝 (1 / 2)) := by
  have := tendsto_eqHomozygosity (θ := 1) one_pos
  norm_num at this ⊢
  exact this

example (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => 1 - eqHomozygosity (2 * N) (θ / (4 * N))) atTop
      (𝓝 (θ / (1 + θ))) :=
  tendsto_one_sub_eqHomozygosity hθ

example (M : ℕ) (hM : 0 < M) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (F : ℝ) :
    homozygosityStep M u F = F ↔ F = eqHomozygosity M u :=
  homozygosityStep_eq_self_iff hM hu0 hu1 F

/-- `u = 0` (no mutation, outside the domain of the theorems): the formula gives `F* = 1`,
eventual fixation of one allele. -/
example : eqHomozygosity 2 0 = 1 := by
  norm_num [eqHomozygosity]

/-- `M = 0` is outside the model: the definition then uses the junk value `1/0 = 0`. -/
example (u F : ℝ) : homozygosityStep 0 u F = (1 - u) ^ 2 * F := by
  simp [homozygosityStep]

#print axioms tendsto_iterate_homozygosityStep
#print axioms tendsto_eqHomozygosity

end MathlibExtTest.Biology.PopulationGenetics.InfiniteAlleles
