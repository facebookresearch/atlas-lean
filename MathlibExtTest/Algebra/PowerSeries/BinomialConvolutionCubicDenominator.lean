/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.BinomialConvolutionCubicDenominator
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for binomial products with cubic denominators -/

open MetaMathlibExt PowerSeries

private noncomputable def linearFactor (a : ℚ) : PowerSeries ℚ := 1 - C a * X

-- In the cubic below the off-diagonal pair (1, 2) is obtained by adding 7 to -4.
example : binomialProduct (linearFactor 7)⁻¹ (linearFactor (-4))⁻¹ = (linearFactor 3)⁻¹ := by
  have h : (7 : ℚ) + (-4) = 3 := by norm_num
  have hgeom := binomialProduct_X_pow_mul_inv_pow 0 0 (7 : ℚ) (-4)
  rw [h] at hgeom
  simpa [linearFactor] using hgeom

-- With root parameters 1, 2, 4, the input uses two geometric summands. Its square has
-- diagonal parameters 2 and 4 and an off-diagonal parameter 3, so both terms occur.
example :
    let f := (linearFactor 1)⁻¹ + (linearFactor 2)⁻¹
    ∃ u v : Polynomial ℚ, u.natDegree ≤ 2 ∧ v.natDegree ≤ 2 ∧
      binomialProduct f f =
        (u : PowerSeries ℚ) * (1 + C (-14 : ℚ) * X + C 56 * X ^ 2 + C (-64 : ℚ) * X ^ 3)⁻¹ +
          binomialProduct (1 + C (-7 : ℚ) * X)⁻¹
            ((v : PowerSeries ℚ) * (1 - C (-7 : ℚ) * X + C 14 * X ^ 2 - C (-8 : ℚ) * X ^ 3)⁻¹) := by
  intro f
  let α : Fin 3 → ℚ := fun i ↦ if i = 0 then 1 else if i = 1 then 2 else 4
  let p : Polynomial ℚ := 2 - Polynomial.C 11 * Polynomial.X +
    Polynomial.C 12 * Polynomial.X ^ 2
  have hD : 1 + C (-7 : ℚ) * X + C 14 * X ^ 2 + C (-8 : ℚ) * X ^ 3 =
      ∏ i, (1 - C (α i) * X) := by
    rw [Fin.prod_univ_three]
    change _ = linearFactor 1 * linearFactor 2 * linearFactor 4
    simp only [linearFactor, map_neg, map_one, map_ofNat]
    ring
  have hα : ∀ i j k, ¬(i = j ∧ j = k) → 2 * α i ≠ α j + α k := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp (config := { decide := true }) only [α] <;> norm_num
  have hp : p.degree < 3 := by
    refine (Polynomial.degree_lt_iff_coeff_zero p 3).2 ?_
    intro n hn
    have h0 : n ≠ 0 := by omega
    have h1 : 1 ≠ n := by omega
    have h2 : n ≠ 2 := by omega
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h0, h1, h2]
  have hf : f * (1 + C (-7 : ℚ) * X + C 14 * X ^ 2 + C (-8 : ℚ) * X ^ 3) =
      (p : PowerSeries ℚ) := by
    rw [hD, Fin.prod_univ_three]
    change _ * (linearFactor 1 * linearFactor 2 * linearFactor 4) = _
    have cancel (a : ℚ) : (linearFactor a)⁻¹ * linearFactor a = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [linearFactor])
    calc
      _ = ((linearFactor 1)⁻¹ * linearFactor 1) * linearFactor 2 * linearFactor 4 +
          ((linearFactor 2)⁻¹ * linearFactor 2) * linearFactor 1 * linearFactor 4 := by
        dsimp [f]
        ring
      _ = _ := by
        rw [cancel, cancel]
        change _ = Polynomial.coeToPowerSeries.ringHom p
        have hX : Polynomial.coeToPowerSeries.ringHom (Polynomial.X : Polynomial ℚ) = X :=
          Polynomial.coe_X
        simp only [p, map_sub, map_add, map_mul, map_pow, map_ofNat, linearFactor, map_one, hX]
        ring
  have h := binomialProduct_cubic_denominator (-7 : ℚ) 14 (-8) (by norm_num)
    α hD hα f f p p hp hp hf hf
  norm_num only at h
  exact h

#print axioms binomialProduct_cubic_denominator
