/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.MutationSelectionBalance

@[expose] public section

open Filter Topology MathlibExt.Biology.PopulationGenetics.MutationSelectionBalance

namespace MathlibExtTest.Biology.PopulationGenetics.MutationSelectionBalance

/-! ### The linear recursion on concrete numbers (`s = 1/10`, `U = 1/1000`) -/

/-- One step from `0`: the new LoF frequency is `U`. -/
example : linStep (1 / 10) (1 / 1000) 0 = 1 / 1000 := by norm_num [linStep]

/-- The equilibrium `U / s = 1/100` is fixed. -/
example : linStep (1 / 10) (1 / 1000) (1 / 100) = 1 / 100 := by norm_num [linStep]

/-- The closed form after two steps from `0`: `U/s (1 - (1 - s)²) = 19/10000`. -/
example : (linStep (1 / 10) (1 / 1000))^[2] 0 = 19 / 10000 := by
  rw [linStep_iterate (by norm_num)]; norm_num

/-- Global attraction from any start. -/
example : Tendsto (fun t => (linStep (1 / 10) (1 / 1000))^[t] (1 / 2)) atTop
    (𝓝 ((1 / 1000) / (1 / 10))) :=
  tendsto_linStep_iterate (by norm_num) (by norm_num) _ _

/-- The de novo fraction at equilibrium is `s = 1/10`. -/
example : deNovoFraction (1 / 10) (1 / 1000) ((1 / 1000) / (1 / 10)) = 1 / 10 :=
  deNovoFraction_eq (by norm_num) (by norm_num)

/-- Boundary `s = 1` (lethal heterozygotes): equilibrium is `U` and is reached in one step. -/
example (U x : ℝ) : linStep 1 U x = U := by simp [linStep]

/-- Outside the domain, `s = 2`: the orbit oscillates and does not converge (`x_t` alternates
between `x` and `U - x`); the attraction theorem requires `s < 2`. -/
example (U x : ℝ) : (linStep 2 U)^[2] x = x := by
  simp [linStep]; ring

/-- At `s = 0` (`s = 0` makes `U / s` the junk value `0`): the frequency grows linearly,
`x_t = x + t U`, and has no fixed point when `U ≠ 0`. -/
example (U x : ℝ) (t : ℕ) : (linStep 0 U)^[t] x = x + t * U := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, linStep]; push_cast; ring

/-! ### The linear Wright–Fisher chain: a bottleneck -/

/-- Non-vacuity of the kernel's probability hypotheses: from `1` copy in `2` with `s = 1/2`,
`U = 1/4`, the sampling probability is `1/2 ∈ [0, 1]`. -/
example : linStep (1 / 2) (1 / 4) (((1 : Fin 3) : ℕ) / (2 : ℕ)) = 1 / 2 := by
  norm_num [linStep]

/-- A kernel entry: sampling `N' = 1` copy with probability `1/2` gives `1` LoF copy with
probability `1/2`. -/
example : kernel (1 / 2) (1 / 4) 2 1 1 1 = 1 / 2 := by
  norm_num [kernel, bernsteinPolynomial, linStep]

/-- The demography-free mean for a bottleneck from `4` to `1` gene copy, from the point mass at
`2` copies out of `4`: after one generation the mean is `(1 - s)/2 + U`. -/
example : meanFreq 1 (pushStep (1 / 2) (1 / 4) 4 1 (fun i => if i = 2 then 1 else 0)) =
    1 / 2 := by
  rw [meanFreq_pushStep _ _ _ (by norm_num) (by simp)]
  simp [meanFreq, linStep]
  norm_num

/-! ### The diploid model -/

/-- Multiplicative fitness with `s = 1/10`, `U = 1/1000`: `U / s` is an equilibrium. -/
example : diploidStep (1 / 10) (2 * (1 / 10) - (1 / 10) ^ 2) (1 / 1000) ((1 / 1000) / (1 / 10)) =
    (1 / 1000) / (1 / 10) :=
  diploidStep_mult_fixed (by norm_num) (by norm_num)

/-- The Haldane–Muller load does not depend on `s`. -/
example (s : ℝ) (hs : s ≠ 0) :
    1 - meanFitness s (2 * s - s ^ 2) ((1 / 1000) / s) = 2 * (1 / 1000) - (1 / 1000) ^ 2 :=
  load_mult_at_equilibrium hs (by norm_num)

/-- Recessive lethality (`t = 1`) satisfies the hypothesis `2s - s² ≤ t` for every `s`. -/
example (s : ℝ) : 2 * s - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s - 1)]

/-- The bound applied to recessive lethals with `s = 1/10`. -/
example (U q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (h : diploidStep (1 / 10) 1 U q = q) :
    q ≤ U / (1 / 10) :=
  le_div_of_diploidStep_eq (by norm_num) (by norm_num) le_rfl (by norm_num) hq0 hq1 h

/-- Junk value at `q = 1` with lethal homozygotes: the mean fitness is `0` and `selected` is the
junk value `0`, which is why the bound assumes `q < 1`. -/
example : meanFitness (1 / 10) 1 1 = 0 ∧ selected (1 / 10) 1 1 = 0 := by
  constructor <;> norm_num [meanFitness, selected]

end MathlibExtTest.Biology.PopulationGenetics.MutationSelectionBalance
