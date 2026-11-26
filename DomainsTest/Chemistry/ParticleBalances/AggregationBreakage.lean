/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.ParticleBalances.AggregationBreakage
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Two-bin fixtures for finite aggregation and breakage -/

open Set Chemistry.ParticleBalances
open scoped BigOperators

noncomputable section

namespace DomainsTest.Chemistry.ParticleBalances

private def aggregationN (k : Fin 2) : ℝ → ℝ :=
  if k = 0 then (fun t ↦ t⁻¹) else (fun t ↦ (1 - t⁻¹) / 2)

private def diagonalKernel (i j : Fin 2) : ℝ := if i = 0 ∧ j = 0 then 1 else 0

-- The nonzero event is two mass-one particles joining to make one mass-two particle.
-- The mass-two equation needs the diagonal contribution with coefficient 1/2.
example :
    (∑ k, (↑(k.val + 1 : ℕ) : ℝ) * aggregationN k 1) =
      (∑ k, (↑(k.val + 1 : ℕ) : ℝ) * aggregationN k 2) ∧
    AntitoneOn (fun t ↦ ∑ k, aggregationN k t) (Ici 1) := by
  refine (mass_conservation_and_particle_count_monotonicity (convex_Ici (1 : ℝ))
    aggregationN diagonalKernel (fun _ ↦ 0) (fun _ _ ↦ 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).imp
    (fun h ↦ h 1 (by simp) 2 (by norm_num)) (fun h ↦ h.1 fun _ ↦ rfl)
  · intro k t ht
    have ht' : 1 ≤ t := ht
    have hpos : 0 < t := by linarith
    fin_cases k
    · simpa [aggregationN] using inv_nonneg.mpr hpos.le
    · have hle : t⁻¹ ≤ 1 := by
        rw [← one_div]
        exact (div_le_one hpos).mpr ht'
      simpa [aggregationN] using div_nonneg (sub_nonneg.mpr hle) (by norm_num : (0 : ℝ) ≤ 2)
  · intro k t ht
    have ht' : 1 ≤ t := ht
    have hne : t ≠ 0 := by linarith
    have hi := (hasDerivAt_inv hne).continuousAt
    fin_cases k
    · simpa [aggregationN] using hi.continuousWithinAt
    · simpa [aggregationN] using ((continuousAt_const.sub hi).div_const 2).continuousWithinAt
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [diagonalKernel]
  · intro i j
    simp [diagonalKernel, and_comm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [diagonalKernel] at *
  · simp
  · simp
  · simp
  · simp
  · intro t ht k
    have ht' : 1 ≤ t := interior_subset ht
    have hne : t ≠ 0 := by linarith
    have h₁ : HasDerivAt (fun u : ℝ ↦ u⁻¹) (-(t⁻¹ * t⁻¹)) t := by
      convert hasDerivAt_inv hne using 1
      field_simp
    have h₂ : HasDerivAt (fun u : ℝ ↦ (1 - u⁻¹) / 2) (t⁻¹ * t⁻¹ / 2) t := by
      convert (h₁.const_sub (1 : ℝ)).div_const 2 using 1
      ring
    fin_cases k
    · simpa [aggregationN, diagonalKernel, Fin.sum_univ_two] using h₁.hasDerivWithinAt
    · simpa [aggregationN, diagonalKernel, Fin.sum_univ_two] using h₂.hasDerivWithinAt

private def breakageN (k : Fin 2) : ℝ → ℝ :=
  if k = 0 then (fun t ↦ 2 - 2 * Real.exp (-t)) else (fun t ↦ Real.exp (-t))

private def breakageRate (i : Fin 2) : ℝ := if i = 0 then 0 else 1

-- The active dimer splits into two monomers. The inactive monomer column is deliberately
-- negative and fails the mass constraint; it is invisible in the differential equation.
private def daughters (j i : Fin 2) : ℝ :=
  if i = 0 then -7 else if j = 0 then 2 else 0

example :
    (∑ k, (↑(k.val + 1 : ℕ) : ℝ) * breakageN k 0) =
      (∑ k, (↑(k.val + 1 : ℕ) : ℝ) * breakageN k 1) ∧
    MonotoneOn (fun t ↦ ∑ k, breakageN k t) (Ici 0) := by
  refine (mass_conservation_and_particle_count_monotonicity (convex_Ici (0 : ℝ))
    breakageN (fun _ _ ↦ 0) breakageRate daughters ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).imp
    (fun h ↦ h 0 (by simp) 1 (by norm_num)) (fun h ↦ h.2 fun _ _ ↦ rfl)
  · intro k t ht
    have ht' : 0 ≤ t := ht
    fin_cases k
    · have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht')
      simp [breakageN]
      linarith
    · simpa [breakageN] using (Real.exp_pos (-t)).le
  · intro k
    have he : Continuous (fun t : ℝ ↦ Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
    fin_cases k
    · have h : Continuous (fun t : ℝ ↦ 2 - 2 * Real.exp (-t)) := by fun_prop
      simpa [breakageN] using h.continuousOn
    · simpa [breakageN] using he.continuousOn
  · simp
  · simp
  · simp
  · intro i
    fin_cases i <;> norm_num [breakageRate]
  · intro i hi j
    fin_cases i <;> fin_cases j <;> norm_num [breakageRate, daughters] at *
  · intro i hi j hij
    fin_cases i <;> fin_cases j <;> norm_num [breakageRate, daughters] at *
  · intro i hi
    fin_cases i <;> norm_num [breakageRate, daughters, Fin.sum_univ_two] at *
  · intro t _ k
    have h₂ : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    have h₁ : HasDerivAt (fun u : ℝ ↦ 2 - 2 * Real.exp (-u)) (2 * Real.exp (-t)) t := by
      simpa using (h₂.const_mul 2).const_sub 2
    fin_cases k
    · simpa [breakageN, breakageRate, daughters, Fin.sum_univ_two] using h₁.hasDerivWithinAt
    · simpa [breakageN, breakageRate, daughters, Fin.sum_univ_two] using h₂.hasDerivWithinAt

end DomainsTest.Chemistry.ParticleBalances
