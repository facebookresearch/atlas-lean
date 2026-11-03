/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranIndependence

/-!
# Tests for Cochran's theorem: joint independence and the rank criterion

The rank criterion on the coordinate projections of `ℚ²` (both directions) and a non-example
(`A₁ = A₂ = ½ I` sums to `I` but the ranks add up to `4 ≠ 2`); independence of a projection and
its orthogonal complement; the sample-mean statements for `n = 3` and the boundary `n = 1`; a
two-group analysis of variance; and the empty-group convention `groupMean = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExtTest.Probability.Distributions.CochranIndependence

/-- The two coordinate projections of `ℚ²`. -/
def coordProj : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ :=
  ![!![1, 0; 0, 0], !![0, 0; 0, 1]]

theorem coordProj_sum : ∑ k, coordProj k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordProj, Fin.sum_univ_two]

/-- The coordinate projections are idempotent and annihilate each other, so their ranks add up
to `2`. -/
example : ∑ k, (coordProj k).rank = 2 := by
  have h := (cochran_rank_criterion coordProj coordProj_sum).2 ⟨fun k => by
    fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [coordProj],
    fun k l hkl => by
      fin_cases k <;> fin_cases l
      · exact absurd rfl hkl
      · ext i j; fin_cases i <;> fin_cases j <;> simp [coordProj]
      · ext i j; fin_cases i <;> fin_cases j <;> simp [coordProj]
      · exact absurd rfl hkl⟩
  simpa using h

/-- Non-example: `½ I + ½ I = I`, but `½ I` is not idempotent, so the ranks do not add up to the
size. -/
example : ∑ _k : Fin 2, ((1 / 2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)).rank ≠ 2 := by
  intro h
  have hsum : ∑ _k : Fin 2, (1 / 2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul]
    norm_num
  have h' := ((cochran_rank_criterion (fun _ : Fin 2 => (1 / 2 : ℚ) • (1 : Matrix (Fin 2)
    (Fin 2) ℚ)) hsum).1 (by simpa using h)).1 0
  have := congrFun (congrFun h' 0) 0
  norm_num [Matrix.smul_apply] at this

/-- A subspace and its orthogonal complement give independent projections of a standard
Gaussian vector. -/
example (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
    iIndepFun (fun (b : Bool) x => (if b then K else Kᗮ).starProjection x)
      (stdGaussian (EuclideanSpace ℝ (Fin 3))) := by
  refine iIndepFun_starProjection_stdGaussian _ fun b c hbc => ?_
  cases b <;> cases c
  · exact absurd rfl hbc
  · exact (Submodule.isOrtho_orthogonal_right K).symm
  · exact Submodule.isOrtho_orthogonal_right K
  · exact absurd rfl hbc

/-- The sample mean and the sum of squared deviations of three i.i.d. `N(2, 5)` variables are
independent. -/
example : IndepFun (fun x : Fin 3 → ℝ => (∑ i, x i) / 3)
    (fun x : Fin 3 → ℝ => ∑ i, (x i - (∑ j, x j) / 3) ^ 2)
    (Measure.pi fun _ : Fin 3 => gaussianReal 2 5) := by
  exact_mod_cast indepFun_sampleMean_sumSqDev (n := 3) 2 5

/-- The sample mean of three i.i.d. `N(2, 6)` variables has law `N(2, 2)`. -/
example : HasLaw (fun x : Fin 3 → ℝ => (∑ i, x i) / 3) (gaussianReal 2 2)
    (Measure.pi fun _ : Fin 3 => gaussianReal 2 6) := by
  have h := hasLaw_sampleMean (n := 3) (by norm_num) 2 6
  have h6 : (6 : NNReal) / (3 : ℕ) = 2 := by norm_num
  rw [h6] at h
  exact_mod_cast h

/-- Boundary `n = 1`: the sample mean is the observation itself. -/
example : HasLaw (fun x : Fin 1 → ℝ => (∑ i, x i) / 1) (gaussianReal 0 1)
    (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by
  simpa using hasLaw_sampleMean (n := 1) one_pos 0 1

/-- Group labels: observations `0, 1` in one group, `2, 3` in the other. -/
def half (i : Fin 4) : Bool := decide (i.val < 2)

/-- Two groups of two observations: between- and within-group sums of squares are
independent. -/
example : IndepFun
    (fun x : Fin 4 → ℝ => ∑ i, (groupMean half x (half i) - (∑ j, x j) / 4) ^ 2)
    (fun x : Fin 4 → ℝ => ∑ i, (x i - groupMean half x (half i)) ^ 2)
    (Measure.pi fun _ : Fin 4 => gaussianReal 0 1) := by
  simpa using indepFun_sumSqBetween_sumSqWithin half 0 1

/-- An empty group has mean `0` (Lean's `a / 0 = 0`). -/
example (x : Fin 2 → ℝ) : groupMean (fun _ : Fin 2 => true) x false = 0 := by
  simp [groupMean]

/-- A group mean over a nonempty group is the average. -/
example (x : Fin 2 → ℝ) : groupMean (fun _ : Fin 2 => ()) x () = (x 0 + x 1) / 2 := by
  simp [groupMean, Fin.sum_univ_two]

end MathlibExtTest.Probability.Distributions.CochranIndependence
