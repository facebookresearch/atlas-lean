/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.BernoulliProductTail

@[expose] public section

namespace MathlibExt.Probability.BernoulliProductTailTests

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ProbabilityTheory unitInterval
open MathlibExt.Probability.BernoulliProductTail
open MathlibExt.Probability.Combinatorics.RandomSubset

theorem T1_one_coord_sum_ge_one_eq_half :
    (randomSubsetLaw (fun _ : Fin 1 => (⟨(1 / 2 : ℝ),
      Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ : I))).real
        {ω | (1 : ℝ) ≤ ∑ i, coordVar i ω} = (1 / 2 : ℝ) := by
  rw [measureReal_sum_ge_eq_sum]
  have hfilter : Finset.univ.filter
      (fun b : Fin 1 → Bool => (1 : ℝ) ≤ ∑ i, coordVar i b) =
      {(fun _ : Fin 1 => true)} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      have hsum : ∑ i, coordVar i b = (if b 0 then (1 : ℝ) else 0) := by
        rw [Fin.sum_univ_one]
        simp [coordVar]
      rw [hsum] at h
      cases hb0 : b 0
      · simp [hb0] at h
        exact absurd h (by norm_num)
      · ext i
        fin_cases i
        simp [hb0]
    · intro h
      rw [h]
      have hsum : ∑ i, coordVar i (fun _ : Fin 1 => true) = (1 : ℝ) := by
        rw [Fin.sum_univ_one]
        simp [coordVar]
      rw [hsum]
  rw [hfilter]
  simp

theorem T2_two_coords_sum_ge_two_eq_quarter :
    (randomSubsetLaw (fun _ : Fin 2 => (⟨(1 / 2 : ℝ),
      Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ : I))).real
        {ω | (2 : ℝ) ≤ ∑ i, coordVar i ω} = (1 / 4 : ℝ) := by
  rw [measureReal_sum_ge_eq_sum]
  have hfilter : Finset.univ.filter
      (fun b : Fin 2 → Bool => (2 : ℝ) ≤ ∑ i, coordVar i b) =
      {(fun _ : Fin 2 => true)} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      have hsum : ∑ i, coordVar i b =
          (if b 0 then (1 : ℝ) else 0) + (if b 1 then (1 : ℝ) else 0) := by
        rw [Fin.sum_univ_two]
        simp [coordVar]
      rw [hsum] at h
      cases hb0 : b 0 <;> cases hb1 : b 1
      · simp [hb0, hb1] at h
        exact absurd h (by norm_num)
      · simp [hb0, hb1] at h
      · simp [hb0, hb1] at h
      · ext i
        fin_cases i <;> simp [hb0, hb1]
    · intro h
      rw [h]
      have hsum : ∑ i, coordVar i (fun _ : Fin 2 => true) = (2 : ℝ) := by
        rw [Fin.sum_univ_two]
        norm_num [coordVar]
      rw [hsum]
  rw [hfilter]
  simp [Fin.prod_univ_two]
  norm_num

#print axioms randomSubsetLaw_real_singleton
#print axioms integral_coordVar
#print axioms iIndepFun_coordVar
#print axioms measureReal_sum_ge_eq_sum
#print axioms measureReal_sum_ge_le_exp
#print axioms measureReal_sum_le_le_exp

end MathlibExt.Probability.BernoulliProductTailTests
