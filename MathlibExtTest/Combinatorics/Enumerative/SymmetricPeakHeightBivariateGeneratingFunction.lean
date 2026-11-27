/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightBivariateGeneratingFunction
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightBivariateGeneratingFunction`
-/

namespace MathlibExtTest.SymmetricPeakHeightBivariateGeneratingFunction

open MetaMathlibExt PowerSeries

/-- The coefficient of `xⁿ` in the bivariate series: the polynomial in `y` whose coefficient of
`yᵏ` is the total symmetric peak height over the compositions of `n` with `k` parts. -/
private noncomputable def P (n : ℕ) : Polynomial ℤ :=
  ∑ c : Composition n,
    Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length

/-- The coefficient of `yᵏ` in `P n` is `hsp(n, k)`. -/
private theorem coeff_P (n k : ℕ) :
    (P n).coeff k = ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = k),
      ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) := by
  simp [P, Finset.sum_filter, eq_comm]

/-- The coefficient of `xⁿ` in the identity, writing `Y` for the variable `y` and `Q = 1 + Y`,
where a term `P (n - k)` with `n < k` is absent:
`P n - 2 Q P (n - 1) + Q² P (n - 2) - P (n - 3) + 2 Q P (n - 4) - Q² P (n - 5)` is `Y³` for
`n = 4` and `0` otherwise. -/
private theorem coeff_identity (n : ℕ) :
    P n - 2 * (1 + Polynomial.X) * (if 1 ≤ n then P (n - 1) else 0) +
        (1 + Polynomial.X) ^ 2 * (if 2 ≤ n then P (n - 2) else 0) -
        (if 3 ≤ n then P (n - 3) else 0) +
        2 * (1 + Polynomial.X) * (if 4 ≤ n then P (n - 4) else 0) -
        (1 + Polynomial.X) ^ 2 * (if 5 ≤ n then P (n - 5) else 0) =
      if n = 4 then Polynomial.X ^ 3 else 0 := by
  have h := congrArg (coeff n) symmetricPeakHeightSum_compositions_bivariate_genFun
  have hP : ∀ H : (Polynomial ℤ)⟦X⟧,
      H * ((1 - X ^ 3) * (1 - X - C (Polynomial.X : Polynomial ℤ) * X) ^ 2) =
        H - C (2 * (1 + Polynomial.X)) * (X ^ 1 * H) +
          C ((1 + Polynomial.X) ^ 2) * (X ^ 2 * H) - X ^ 3 * H +
          C (2 * (1 + Polynomial.X)) * (X ^ 4 * H) - C ((1 + Polynomial.X) ^ 2) * (X ^ 5 * H) := by
    intro H
    simp only [map_mul, map_add, map_pow, map_one, map_ofNat, pow_one]
    ring
  rw [hP, coeff_C_mul_X_pow] at h
  simpa only [P, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk] using h

/-- The first values: `P n = 0` for `n ≤ 3`, `P 4 = Y³` (the composition `1 2 1`),
`P 5 = 2 Y³ + 2 Y⁴` (`1 3 1` with three parts, `1 2 1 1` and `1 1 2 1` with four) and
`P 6 = 3 Y³ + 6 Y⁴ + 3 Y⁵`. At `Y = 1` these are the totals `0, 0, 0, 0, 1, 4, 12`. -/
private theorem P_values : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 ∧ P 3 = 0 ∧ P 4 = Polynomial.X ^ 3 ∧
    P 5 = 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 ∧
    P 6 = 3 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 4 + 3 * Polynomial.X ^ 5 := by
  have h0 := coeff_identity 0
  have h1 := coeff_identity 1
  have h2 := coeff_identity 2
  have h3 := coeff_identity 3
  have h4 := coeff_identity 4
  have h5 := coeff_identity 5
  have h6 := coeff_identity 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  have e0 : P 0 = 0 := h0
  have e1 : P 1 = 0 := by linear_combination h1 + 2 * (1 + Polynomial.X) * e0
  have e2 : P 2 = 0 := by
    linear_combination h2 + 2 * (1 + Polynomial.X) * e1 - (1 + Polynomial.X) ^ 2 * e0
  have e3 : P 3 = 0 := by
    linear_combination h3 + 2 * (1 + Polynomial.X) * e2 - (1 + Polynomial.X) ^ 2 * e1 + e0
  have e4 : P 4 = Polynomial.X ^ 3 := by
    linear_combination h4 + 2 * (1 + Polynomial.X) * e3 - (1 + Polynomial.X) ^ 2 * e2 + e1 -
      2 * (1 + Polynomial.X) * e0
  have e5 : P 5 = 2 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 := by
    linear_combination h5 + 2 * (1 + Polynomial.X) * e4 - (1 + Polynomial.X) ^ 2 * e3 + e2 -
      2 * (1 + Polynomial.X) * e1 + (1 + Polynomial.X) ^ 2 * e0
  have e6 : P 6 = 3 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 4 + 3 * Polynomial.X ^ 5 := by
    linear_combination h6 + 2 * (1 + Polynomial.X) * e5 - (1 + Polynomial.X) ^ 2 * e4 + e3 -
      2 * (1 + Polynomial.X) * e2 + (1 + Polynomial.X) ^ 2 * e1
  exact ⟨e0, e1, e2, e3, e4, e5, e6⟩

-- Reading off a coefficient: over the compositions of `6` with four parts the symmetric peak
-- heights add up to `6`, from `1 2 1 2` and `2 1 2 1` (height `1`) and from `1 3 1 1` and
-- `1 1 3 1` (height `2`).
example : ∑ c ∈ Finset.univ.filter (fun c : Composition 6 => c.length = 4),
    ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) = 6 := by
  rw [← coeff_P, P_values.2.2.2.2.2.2]
  simp [Polynomial.coeff_X_pow]

-- Evaluating at `y = 1` gives the generating function of the total symmetric peak height over
-- all compositions, `∑ₙ hsp(n) xⁿ = x⁴ / ((1 - 2x)² (1 - x³))`, the univariate form of the lemma.
example :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3)) = X ^ 4 := by
  have h := congrArg (PowerSeries.map (Polynomial.evalRingHom (1 : ℤ)))
    symmetricPeakHeightSum_compositions_bivariate_genFun
  have hm : PowerSeries.map (Polynomial.evalRingHom (1 : ℤ)) (PowerSeries.mk fun n =>
      ∑ c : Composition n,
        Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length) =
      PowerSeries.mk
        (fun n => ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)) := by
    ext n
    simp [coeff_map]
  rw [map_mul, hm] at h
  simp only [map_mul, map_sub, map_pow, map_one, map_C, map_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_X, one_pow, one_mul] at h
  linear_combination h

end MathlibExtTest.SymmetricPeakHeightBivariateGeneratingFunction
