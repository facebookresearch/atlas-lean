/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.TotalProgeny

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability.GaltonWatson
open scoped ENNReal NNReal Nat

namespace MathlibExtTest.Probability.BranchingProcess.TotalProgeny

/-! ### Cycle lemma on concrete sequences -/

/-- One ancestor, steps `(2, 0, 0)`: only the unshifted sequence is first passage. -/
example : #{r ∈ range 3 | IsFirstPassage 1 3 (rotate ![2, 0, 0] r)} = 1 := by decide

/-- Two ancestors, periodic steps `(1, 0, 1, 0)`: two good shifts, counted by index. -/
example : #{r ∈ range 4 | IsFirstPassage 2 4 (rotate ![1, 0, 1, 0] r)} = 2 := by decide

/-- Two ancestors, steps `(0, 2, 0, 0)`. -/
example : #{r ∈ range 4 | IsFirstPassage 2 4 (rotate ![0, 2, 0, 0] r)} = 2 := by decide

/-- The theorem applied to a concrete sequence. -/
example : #{r ∈ range 5 | IsFirstPassage 3 5 (rotate ![0, 1, 0, 1, 0] r)} = 3 :=
  card_filter_isFirstPassage_rotate (by norm_num) _ (by decide)

/-! ### Weights: concrete values and boundary cases -/

/-- With weights `p(j) = j + 1`, `H(1, 4) = 30` and `W(1, 4) = 120 = 4 · 30`. -/
example : hittingWeight (fun j => j + 1) 1 4 = 30 := by decide
example : walkWeight (fun j => j + 1) 1 4 = 120 := by decide

/-- One step from one ancestor: `T = 1` iff the ancestor has no children. -/
example (p : ℕ → ℝ) : hittingWeight p 1 1 = p 0 := by
  have : (Nat.antidiagonalTuple 1 (1 - 1)).filter
      (fun x => ∑ i, x i + 1 = 1 ∧ IsFirstPassage 1 1 x) = {![0]} := by decide
  rw [hittingWeight, this, sum_singleton, Fin.prod_univ_one]
  rfl

/-- Boundary `k > n`: the walk cannot reach `0` by time `n`, so both weights vanish. -/
example : hittingWeight (fun j => j + 1) 3 2 = 0 := by decide
example : walkWeight (fun j => j + 1) 3 2 = 0 := by decide

/-- Boundary `k = n = 0`: the empty forest has total progeny `0` with probability one. -/
example : hittingWeight (fun j => j + 1) 0 0 = 1 := by decide

/-- Boundary `k = 0 < n`: no first passage at a positive time. -/
example : hittingWeight (fun j => j + 1) 0 3 = 0 := by decide

/-- The hitting-time theorem checked on a concrete instance with `k = 2`. -/
example : (5 : ℕ) * hittingWeight (fun j => 2 * j + 3) 2 5 =
    2 * walkWeight (fun j => 2 * j + 3) 2 5 := natCast_mul_hittingWeight _ _ _

/-! ### Otter–Dwass and Borel for Poisson offspring (non-vacuity) -/

/-- Otter–Dwass for Poisson(`r`) offspring, three ancestors, total progeny `7`. -/
example (r : ℝ≥0) :
    (7 : ℝ≥0∞) * (Measure.pi fun _ : Fin 7 => poissonMeasure r)
        {x | ∑ i, x i + 3 = 7 ∧ IsFirstPassage 3 7 x} =
      3 * (Measure.pi fun _ : Fin 7 => poissonMeasure r) {x | ∑ i, x i + 3 = 7} :=
  natCast_mul_measure_firstPassage _ 3 7

/-- Borel law at `n = 1`: `P(T = 1) = e^{-r}`, the probability of no children. -/
example (r : ℝ≥0) : hittingWeight (fun j => (poissonMeasure r).real {j}) 1 1 =
    Real.exp (-r) := by
  rw [hittingWeight_poisson_one r le_rfl]; simp

/-- Borel law at `n = 2`: `P(T = 2) = r e^{-2r}` (one child, who has none). -/
example (r : ℝ≥0) : hittingWeight (fun j => (poissonMeasure r).real {j}) 1 2 =
    r * Real.exp (-(2 * r)) := by
  rw [hittingWeight_poisson_one r (by norm_num)]
  norm_num [Nat.factorial]; ring_nf

/-- The same value computed directly from the definition: `p(1) p(0) = r e^{-r} · e^{-r}`. -/
example (r : ℝ≥0) : hittingWeight (fun j => (poissonMeasure r).real {j}) 1 2 =
    (poissonMeasure r).real {1} * (poissonMeasure r).real {0} := by
  rw [hittingWeight]
  have : (Nat.antidiagonalTuple 2 (2 - 1)).filter
      (fun x => ∑ i, x i + 1 = 2 ∧ IsFirstPassage 1 2 x) = {![1, 0]} := by decide
  rw [this, sum_singleton, Fin.prod_univ_two]
  rfl

/-! ### Mean total progeny -/

/-- No offspring (`m = 0`): the total progeny is the ancestor alone. -/
example : meanTotalProgeny (Measure.dirac 0) = 1 := by
  rw [meanTotalProgeny_eq, mean, lintegral_dirac]; simp

/-- Boundary `m = 1` (exactly one child each): the mean total progeny is infinite. -/
example : meanTotalProgeny (Measure.dirac 1) = ∞ := by
  rw [meanTotalProgeny_eq, mean, lintegral_dirac]; simp

end MathlibExtTest.Probability.BranchingProcess.TotalProgeny
