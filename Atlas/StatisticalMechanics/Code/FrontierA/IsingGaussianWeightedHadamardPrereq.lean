/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianWeightedLeeYang










open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedFieldRadius (a : V → Real) : Real :=
  ∑ v : V, |a v|

theorem finiteIsingWeightedFieldRadius_nonneg (a : V → Real) :
    0 ≤ finiteIsingWeightedFieldRadius a := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem norm_weightedSpinSum_le_radius
    (a : V → Real) (s : ConfigSpace V) :
    ‖∑ v : V, (a v : Complex) * spin s v‖ ≤
      finiteIsingWeightedFieldRadius a := by
  calc
    ‖∑ v : V, (a v : Complex) * spin s v‖ ≤
        ∑ v : V, ‖(a v : Complex) * spin s v‖ := norm_sum_le _ _
    _ = ∑ v : V, |a v| := by
      apply Finset.sum_congr rfl
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold spin
      split <;> norm_num
    _ = finiteIsingWeightedFieldRadius a := rfl


theorem finiteIsingWeightedFieldPartition_analyticOnNhd
    (beta : Real) (a : V → Real) :
    AnalyticOnNhd Complex (finiteIsingWeightedFieldPartition G beta a)
      Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  unfold finiteIsingWeightedFieldPartition
  fun_prop

theorem finiteIsingWeightedFieldPartition_zero
    (beta : Real) (a : V → Real) :
    finiteIsingWeightedFieldPartition G beta a 0 =
      ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) := by
  simp [finiteIsingWeightedFieldPartition]


theorem finiteIsingWeightedFieldPartition_zero_re_pos
    (beta : Real) (a : V → Real) :
    0 < (finiteIsingWeightedFieldPartition G beta a 0).re := by
  rw [finiteIsingWeightedFieldPartition_zero]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_pos
  · intro s _
    unfold zeroFieldInteractionWeight
    positivity
  · exact Finset.univ_nonempty



theorem norm_finiteIsingWeightedFieldPartition_le
    (beta : Real) (a : V → Real) (z : Complex) :
    ‖finiteIsingWeightedFieldPartition G beta a z‖ ≤
      (∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s) *
        Real.exp (‖z‖ * finiteIsingWeightedFieldRadius a) := by
  unfold finiteIsingWeightedFieldPartition
  calc
    ‖∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : Complex) *
          Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v)‖ ≤
        ∑ s : ConfigSpace V,
          ‖(zeroFieldInteractionWeight G beta s : Complex) *
            Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s : ConfigSpace V,
        zeroFieldInteractionWeight G beta s *
          Real.exp (‖z‖ * finiteIsingWeightedFieldRadius a) := by
      apply Finset.sum_le_sum
      intro s _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      · rw [Complex.norm_exp]
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          calc
            (z * ∑ v : V, (a v : Complex) * spin s v).re ≤
                ‖z * ∑ v : V, (a v : Complex) * spin s v‖ :=
              Complex.re_le_norm _
            _ = ‖z‖ * ‖∑ v : V, (a v : Complex) * spin s v‖ := norm_mul _ _
            _ ≤ ‖z‖ * finiteIsingWeightedFieldRadius a :=
              mul_le_mul_of_nonneg_left
                (norm_weightedSpinSum_le_radius a s) (norm_nonneg z)
        · unfold zeroFieldInteractionWeight
          exact (Real.exp_pos _).le
      · unfold zeroFieldInteractionWeight
        positivity
    _ = (∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s) *
        Real.exp (‖z‖ * finiteIsingWeightedFieldRadius a) := by
      rw [Finset.sum_mul]

end

end StatMech.FrontierA
