/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.JukesCantor

/-!
# Tests for the Jukes–Cantor model

Values at `t = 0` and `μ = 0` (identity matrix), row sums and nonnegativity at concrete rates
and times, explicit entries at `μ = 3`, `t = 1`, the Chapman–Kolmogorov equation at concrete
times, the forward equation at `t = 0` (the derivative is the rate matrix), zero row sums of
the rate matrix, the matrix exponential at `t = 0` and its row sums, `pDiff = 0` at `t = 0`,
and the distance correction at concrete values.
-/

@[expose] public section

open Real Finset

namespace MathlibExtTest.Biology.Phylogenetics.JukesCantor

open MathlibExt.Biology.Phylogenetics.JukesCantor

-- At `t = 0` the transition matrix is the identity.
example : jcProb 2 0 0 0 = 1 := by simp [jcProb_zero]
example : jcProb 2 0 1 3 = 0 := by simp [jcProb_zero]

-- With rate `0` nothing changes, whatever the time.
example (t : ℝ) : jcProb 0 t 2 2 = 1 := by norm_num [jcProb]
example (t : ℝ) : jcProb 0 t 2 0 = 0 := by norm_num [jcProb]

-- Row sums at concrete rates and times.
example : ∑ j, jcProb 1 2 0 j = 1 := sum_jcProb 1 2 0
example : ∑ j, jcProb (1 / 10) 7 3 j = 1 := sum_jcProb _ _ 3

-- Nonnegativity at concrete values, and for `μ, t ≥ 0`.
example : 0 ≤ jcProb 1 2 0 1 := jcProb_nonneg (by norm_num) 0 1
example {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) (i j : Fin 4) : 0 ≤ jcProb μ t i j :=
  jcProb_nonneg (mul_nonneg hμ ht) i j

-- Explicit entries at `μ = 3`, `t = 1`.
example : jcProb 3 1 0 0 = 1 / 4 + 3 / 4 * exp (-4) := by norm_num [jcProb]
example : jcProb 3 1 0 2 = 1 / 4 - 1 / 4 * exp (-4) := by norm_num [jcProb]

-- Chapman–Kolmogorov at concrete times.
example : ∑ k, jcProb 1 2 0 k * jcProb 1 3 k 1 = jcProb 1 5 0 1 := by
  rw [sum_jcProb_mul_jcProb]; norm_num

-- The forward equation at `t = 0`: the derivative of `P` is the rate matrix.
example (μ : ℝ) (i j : Fin 4) : HasDerivAt (fun t => jcProb μ t i j) (jcRate μ i j) 0 := by
  have h := hasDerivAt_jcProb μ 0 i j
  simp only [jcProb_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true] at h
  exact h

-- The rate matrix has zero row sums.
example (μ : ℝ) : ∑ j, jcRate μ 0 j = 0 := by
  simp [Fin.sum_univ_four, jcRate]; ring

-- No differences at `t = 0`; the distance correction at concrete values.
example (μ : ℝ) : pDiff μ 0 1 = 0 := by simp [pDiff_eq]
example : pDiff 3 1 0 = 3 / 4 * (1 - exp (-4)) := by rw [pDiff_eq]; norm_num
example : jcDistance (pDiff (1 / 10) 5 2) = 1 / 2 := by rw [jcDistance_pDiff]; norm_num
example : jcDistance 0 = 0 := by simp [jcDistance]

-- Rate-matrix property for a nonnegative rate, and the domain of the distance.
example : 0 ≤ jcRate 2 0 3 := jcRate_nonneg (by norm_num) (by decide)
example (μ : ℝ) (k : Fin 4) : ∑ j, jcRate μ k j = 0 := sum_jcRate μ k
example (i : Fin 4) : pDiff 2 3 i ∈ Set.Ico 0 (3 / 4) := pDiff_mem_Ico (by norm_num) i
-- Outside the biological domain (`μ * t < 0`) the proportion is negative.
example : pDiff 1 (-1) 0 < 0 := by
  rw [pDiff_eq]
  have : (1 : ℝ) < exp (4 / 3) := one_lt_exp_iff.mpr (by norm_num)
  norm_num
  linarith
-- Boundary: at the saturation value `p = 3/4` (outside the domain) the true distance diverges,
-- and the totalized logarithm returns the junk value `0`.
example : jcDistance (3 / 4) = 0 := by norm_num [jcDistance]

-- The matrix exponential: at `t = 0` it is the identity, and its rows sum to `1`.
example : NormedSpace.exp ((0 : ℝ) • jcRateMatrix 1) 2 2 = 1 := by
  rw [← jcProb_eq_exp, jcProb_zero]; simp
example (μ t : ℝ) : ∑ j, NormedSpace.exp (t • jcRateMatrix μ) 1 j = 1 := by
  simp only [← jcProb_eq_exp, sum_jcProb]

#print axioms sum_jcProb_mul_jcProb
#print axioms jcProb_eq_exp
#print axioms hasDerivAt_jcProb
#print axioms jcDistance_pDiff

end MathlibExtTest.Biology.Phylogenetics.JukesCantor
