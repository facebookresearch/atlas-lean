/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreVariance

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.FiniteProbability
  MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreVariance

/-! ### Boundary: the row-sum bound is attained

For the identity matrix on `Fin 2` (absolute row sums `1`) and `w = (1, 1)`, both sides of
`sum_mul_mul_le_of_rowSum` equal `2`, computed from the definitions. -/

/-- The identity matrix on `Fin 2`. -/
def C2 : Fin 2 → Fin 2 → ℝ := fun j k => if j = k then 1 else 0

theorem C2_rowSum (j : Fin 2) : ∑ k, |C2 j k| = 1 := by
  fin_cases j <;> simp [C2, Fin.sum_univ_two]

theorem C2_quadratic_eq_bound :
    ∑ j, ∑ k, (1 : ℝ) * 1 * C2 j k = 1 * ∑ _j : Fin 2, (1 : ℝ) ^ 2 := by
  simp [C2]

/-! ### The least-squares weights, computed

For `x = (0, 1)`: `x̄ = 1/2`, `S_xx = 1/2`, the weights are `∓1`, and their squares sum to
`2 = 1 / S_xx`. -/

theorem sxy_example : sxy ![(0 : ℝ), 1] ![0, 1] = 1 / 2 := by
  simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_two]
  norm_num

theorem olsWeight_sq_example :
    ∑ j, ((![(0 : ℝ), 1] j - sampleMean ![(0 : ℝ), 1]) / sxy ![(0 : ℝ), 1] ![0, 1]) ^ 2 = 2 := by
  rw [sxy_example]
  simp [sampleMean_eq_sum_div, Fin.sum_univ_two]
  norm_num

/-! ### A nonconstant LD-block model

On `Fin 4` with the uniform probability measure, two markers with sign statistics
`(1, 1, -1, -1) / 2` and `(1, -1, 1, -1) / 2` in a single LD block (`K = 2`); each statistic has
variance `1/4`, computed from the definitions. -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Two sign statistics on `Fin 4`. -/
noncomputable def sgn : Fin 2 → Fin 4 → ℝ :=
  ![![1/2, 1/2, -1/2, -1/2], ![1/2, -1/2, 1/2, -1/2]]

theorem variance_sgn (j : Fin 2) : Var[sgn j; μ4] = 1 / 4 := by
  rw [variance_eq_sub MemLp.of_discrete]
  fin_cases j <;> simp [integral_μ4, sgn] <;> norm_num

/-- The single-block model for the two sign statistics. -/
noncomputable def sgnBlock : LDBlockModel μ4 sgn 2 (1 / 4) where
  block := fun _ => 0
  card_block_le := fun _ => by simp
  indepFun := fun _ _ h => absurd rfl h
  memLp := fun _ => MemLp.of_discrete
  variance_le := fun j => (variance_sgn j).le

/-! ### LD-score spread for growing `M`

`M = n + n` markers whose LD scores are `0` on the first half and `1` on the second half have
`S_ℓℓ = M / 4`, so the spread condition holds with `c = 1/4`. -/

/-- LD scores `0` on the first `n` markers and `1` on the last `n`. -/
noncomputable def halfLD (n : ℕ) : Fin (n + n) → ℝ := fun j => if (j : ℕ) < n then 0 else 1

theorem sum_halfLD (n : ℕ) : ∑ j, halfLD n j = n := by
  rw [Fin.sum_univ_add]
  simp [halfLD]

theorem sampleMean_halfLD {n : ℕ} (hn : 0 < n) : sampleMean (halfLD n) = 1 / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sampleMean_eq_sum_div, sum_halfLD]
  simp only [Fintype.card_fin, Nat.cast_add]
  field_simp
  ring

theorem sxy_halfLD (n : ℕ) : sxy (halfLD n) (halfLD n) = ((n + n : ℕ) : ℝ) / 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sxy]
  rw [sxy, sampleMean_halfLD hn, Fin.sum_univ_add]
  simp [halfLD]
  ring

/-! ### Non-vacuity of the limit theorem

Constant statistics in singleton LD blocks (`K = 1`, `V = 0`), the LD scores `halfLD n`,
`M = N = n + n`: every hypothesis of `tendsto_variance_h2Hat_of_ldBlock` holds. -/

theorem card_val_eq_le (n : ℕ) (j : Fin n) : #{k : Fin n | (k : ℕ) = j} ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact Fin.ext (ha.trans hb.symm)

/-- Constant statistics in singleton blocks satisfy the LD-block model. -/
noncomputable def constBlock (M : ℕ) : LDBlockModel μ4 (fun (_ : Fin M) (_ : Fin 4) => (0 : ℝ))
    1 0 where
  block := fun j => j
  card_block_le := card_val_eq_le M
  indepFun := fun _ _ _ => indepFun_const_left _ _
  memLp := fun _ => memLp_const _
  variance_le := fun _ => by simp [variance_eq_sub (memLp_const (0 : ℝ))]

theorem tendsto_add_self : Tendsto (fun n : ℕ => n + n) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_add_left n n) tendsto_id

theorem spread_halfLD (n : ℕ) : (1 / 4 : ℝ) * ((n + n : ℕ) : ℝ) ≤ sxy (halfLD n) (halfLD n) := by
  rw [sxy_halfLD]
  linarith

theorem tendsto_variance_const_example : Tendsto (fun n : ℕ => Var[fun _ : Fin 4 =>
      olsSlope (halfLD n) (fun (_ : Fin (n + n)) => (0 : ℝ)) * ((n + n : ℕ) : ℝ) /
        ((n + n : ℕ) : ℝ); μ4]) atTop (𝓝 0) :=
  tendsto_variance_h2Hat_of_ldBlock (N := fun n => n + n) (M := fun n => n + n)
    (χ := fun n (_ : Fin (n + n)) (_ : Fin 4) => (0 : ℝ))
    (est := fun n (_ : Fin 4) => olsSlope (halfLD n) (fun (_ : Fin (n + n)) => (0 : ℝ)) *
      ((n + n : ℕ) : ℝ) / ((n + n : ℕ) : ℝ))
    halfLD (fun n => constBlock (n + n)) (by norm_num) one_pos spread_halfLD
    (fun n => (one_mul _).le) tendsto_add_self (fun _ _ => rfl)

/-! ### Axioms -/

#print axioms sum_mul_mul_le_of_rowSum
#print axioms variance_olsSlope_le
#print axioms variance_h2Hat_le
#print axioms LDBlockModel.sum_abs_covariance_le
#print axioms tendsto_variance_h2Hat_of_rowSum
#print axioms tendsto_variance_h2Hat_of_ldBlock
#print axioms tendsto_evariance_h2Hat_chiSqStrat

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreVariance
