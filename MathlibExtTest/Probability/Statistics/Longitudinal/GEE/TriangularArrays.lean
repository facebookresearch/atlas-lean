/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.TriangularArrays

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal
open ProbabilityTheory.GEE.Triangular

namespace MathlibExtTest.GEETriangular

/-! ### Smoke tests for the API -/

example : maxClusterSize (fun _ i => i + 1) 4 = 4 := by decide
example : totalSize (fun _ i => i + 1) 4 = 10 := by decide
example : totalSize dominantSizes 5 = 9 := by decide
example : maxClusterSize dominantSizes 5 = 5 := by decide

/-! ### Allowed growth -/

/-- Fixed cluster size `3` (iid-compatible) satisfies the growth condition. -/
example : ClusterGrowth (fun _ _ => 3) := clusterGrowth_const 3 (by norm_num)

/-- Growing balanced clusters of size `⌊√n⌋ + 1` satisfy the growth condition, since
`(⌊√n⌋ + 1) / n → 0`. -/
example : ClusterGrowth (fun n _ => Nat.sqrt n + 1) := by
  refine clusterGrowth_balanced (fun n => Nat.sqrt n + 1) (fun _ => Nat.succ_pos _) ?_
  have hsq : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ + (n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h1 := tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hsq
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hle : ((Nat.sqrt n : ℕ) : ℝ) ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hnn : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt hn'.le).symm
  push_cast
  rw [div_le_iff₀ hn', add_mul, inv_mul_cancel₀ hn'.ne']
  calc (Nat.sqrt n : ℝ) + 1 ≤ √(n : ℝ) + 1 := by linarith
    _ = (√(n : ℝ))⁻¹ * n + 1 := by
        rw [inv_mul_eq_div, add_left_inj, eq_div_iff hs.ne']
        exact hnn.symm

/-- A growing dominant cluster (`n` observations next to singletons) violates it. -/
example : ¬ ClusterGrowth dominantSizes := not_clusterGrowth_dominantSizes

/-! ### Boundary case: a dominant cluster on a concrete probability space -/

/-- The fair coin measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [← two_mul, mul_one, one_div]
  exact ENNReal.mul_inv_cancel (by positivity) (by simp)

/-- Cluster `0` carries a mean-zero `±1` score with the whole row variance; the other clusters
are degenerate. -/
def dominantArray (_n i : ℕ) (b : Bool) : ℝ := if i = 0 then (if b then 1 else -1) else 0

example (k : ℕ) : ∫ b, dominantArray k 0 b ∂fairCoin = 0 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  have htrue : fairCoin.real {true} = 1 / 2 := by simp [fairCoin, Measure.real]
  have hfalse : fairCoin.real {false} = 1 / 2 := by simp [fairCoin, Measure.real]
  simp [dominantArray, htrue, hfalse]

/-- The dominant-cluster array fails the Lindeberg condition. -/
example : ¬ LindebergConditionTriangular dominantArray fairCoin := by
  refine not_lindeberg_of_dominant_cluster dominantArray (fun _ _ _ => measurable_of_finite _)
    (fun _ _ _ => Integrable.of_finite) (fun _ => 0)
    ((eventually_ge_atTop 1).mono fun n hn => mem_range.2 (by omega)) one_pos
    (Eventually.of_forall fun n => ?_).frequently
  have : (fun b => dominantArray n 0 b ^ 2) = fun _ => (1 : ℝ) := by
    funext b; cases b <;> simp [dominantArray]
  rw [this, integral_const, probReal_univ, smul_eq_mul, mul_one]

/-! ### Boundary case: no estimating-equation root -/

/-- Three clusters of two binary observations, all successes: no root at any `β`. -/
example (β : ℝ) : binaryEE (fun _ => 2) (fun _ => 2) 3 β ≠ 0 :=
  binaryEE_no_root (fun _ _ => by norm_num) ⟨0, by simp, by norm_num⟩ β

example : ¬ ∃ β, binaryEE (fun _ => 2) (fun _ => 2) 3 β = 0 := fun ⟨β, h⟩ =>
  binaryEE_no_root (fun _ _ => by norm_num) ⟨0, by simp, by norm_num⟩ β h

/-! ### iid regime: the linear estimating equation has the explicit root -/

example (S : ℕ → Unit → ℝ) : linearEE S 2 3 (linearEERoot S 2 3 ()) () = 0 :=
  (linearEE_eq_zero_iff (by norm_num) (by norm_num)).2 rfl

end MathlibExtTest.GEETriangular
