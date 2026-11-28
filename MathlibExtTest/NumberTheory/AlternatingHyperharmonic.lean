/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.AlternatingHyperharmonic

/-! # Tests for generalized and type II alternating hyperharmonic numbers -/

open MetaMathlibExt Asymptotics Filter Finset
open scoped Topology

-- At the smallest exponent and order, the asymptotic gives the alternating harmonic limit.
example : Tendsto (alternatingGeneralizedHarmonic 1) atTop (𝓝 (Real.log 2)) := by
  have h := alternatingHyperharmonic_typeII_isEquivalent (r := 1) (p := 1) le_rfl le_rfl
  apply IsEquivalent.tendsto_const (c := Real.log 2)
  simpa [signedIteratedPartialSum_one, Function.const_def] using h

-- Only the inner sum alternates in type II, so the two contributions are 1 and 1/2.
example : signedIteratedPartialSum false (alternatingGeneralizedHarmonic 1) 2 2 = 3 / 2 := by
  norm_num [signedIteratedPartialSum, alternatingGeneralizedHarmonic, Finset.sum_Icc_succ_top]

-- Order three introduces the factorial denominator.
example : (fun n => signedIteratedPartialSum false (alternatingGeneralizedHarmonic 2) 3 n)
    ~[atTop] fun n : ℕ => (n : ℝ) ^ 2 * alternatingZeta 2 / 2 := by
  simpa [Nat.factorial] using
    alternatingHyperharmonic_typeII_isEquivalent (r := 3) (p := 2) (by decide) (by decide)

private theorem harmonic_two_tendsto : Tendsto (generalizedHarmonic 2) atTop
    (𝓝 (Real.pi ^ 2 / 6)) := by
  have h : HasSum (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2
    simpa using hasSum_zeta_two
  refine h.tendsto_sum_nat.congr' (.of_forall fun n => ?_)
  simp [generalizedHarmonic_eq_sum_range, one_div]

-- The base order tends to the Basel sum, independently of the asymptotic theorem.
example : Tendsto (signedIteratedPartialSum false (generalizedHarmonic 2) 1) atTop
    (𝓝 (Real.pi ^ 2 / 6)) :=
  harmonic_two_tendsto.congr' (.of_forall fun n => (signedIteratedPartialSum_one false _ n).symm)

-- The order-two ratio has the same limit by Mathlib's Cesàro-mean theorem.
example : Tendsto (fun n : ℕ => signedIteratedPartialSum false (generalizedHarmonic 2) 2 n / n)
    atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  refine ((harmonic_two_tendsto.comp (tendsto_add_atTop_nat 1)).cesaro).congr'
    (.of_forall fun n => ?_)
  change _ = signedIteratedPartialSum false (generalizedHarmonic 2) (0 + 2) n / (n : ℝ)
  rw [signedIteratedPartialSum_succ, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [signedIteratedPartialSum_one, Nat.add_comm 1, div_eq_inv_mul]

private theorem harmonic_two_one : generalizedHarmonic 2 1 = 1 := by
  simpa using generalizedHarmonic_succ 2 0

private theorem harmonic_two_two : generalizedHarmonic 2 2 = 5 / 4 := by
  have h := generalizedHarmonic_succ 2 1
  rw [harmonic_two_one, Real.rpow_two] at h
  norm_num at h ⊢
  exact h

-- Check the range formula against the public successor rule, without using the range formula.
example : generalizedHarmonic 2 2 =
    ∑ k ∈ range 2, (((k + 1 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
  norm_num [harmonic_two_two, sum_range_succ, Real.rpow_two]

-- At order three and index two the unsigned sums give 1 + (1 + 5/4).
example : signedIteratedPartialSum false (generalizedHarmonic 2) 3 2 = 13 / 4 := by
  norm_num [signedIteratedPartialSum_succ, signedIteratedPartialSum_one, sum_Icc_succ_top,
    harmonic_two_one, harmonic_two_two]

-- At the smallest exponent, order three has leading coefficient π²/12.
example : (fun n => signedIteratedPartialSum false (generalizedHarmonic 2) 3 n) ~[atTop]
    fun n : ℕ => (n : ℝ) ^ 2 * (Real.pi ^ 2 / 6) / 2 := by
  rw [← hasSum_zeta_two.tsum_eq]
  simpa [Nat.factorial] using
    generalizedHyperharmonic_isEquivalent (p := 2) (r := 3) (by decide) (by decide)
