/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RegularCubicOverlined

open MetaMathlibExt PowerSeries

namespace MetaMathlibExt.regularCubicOverlinedCount_four_prime_mod_four

local instance fivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_nonsquare : legendreSym 5 (-2) = -1 := by
  apply (legendreSym.eq_neg_one_iff 5).mpr
  change ¬ ∃ x : ZMod 5, (-2 : ZMod 5) = x * x
  decide

-- Multiplication by the mth Euler factor subtracts the coefficient shifted by k * m.
private def eulerCoeff (k : ℕ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => eulerCoeff k m n -
      if k * (m + 1) ≤ n then eulerCoeff k m (n - k * (m + 1)) else 0

open scoped PowerSeries.WithPiTopology in
private theorem coeff_euler (k : ℕ) (hk : 0 < k) (n : ℕ) :
    coeff n (qEulerProduct k) = eulerCoeff k n n := by
  let f (m : ℕ) := (1 : ℤ⟦X⟧) - X ^ (k * (m + 1))
  have hprod : Multipliable f := by
    dsimp only [f]
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun d ↦
      Filter.eventually_atTop.mpr ⟨d, fun m hm ↦ ?_⟩
    rw [order_neg, order_X_pow, Nat.cast_lt]
    nlinarith
  have partialCoeff (m j : ℕ) : coeff j (∏ i ∈ Finset.range m, f i) = eulerCoeff k m j := by
    induction m generalizing j with
    | zero => simp [eulerCoeff, coeff_one]
    | succ m ih =>
      simp only [Finset.prod_range_succ, f, mul_sub, mul_one, map_sub, coeff_mul_X_pow', ih,
        eulerCoeff]
  have stable (m : ℕ) (hm : n ≤ m) : eulerCoeff k m n = eulerCoeff k n n := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => simp [eulerCoeff, show ¬ k * (m + 1) ≤ n by nlinarith, ih]
  apply tendsto_nhds_unique
    (((WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mp hprod.hasProd.tendsto_prod_nat) n)
  exact tendsto_atTop_of_eventually_const fun m (hm : n ≤ m) ↦
    (partialCoeff m n).trans (stable m hm)

-- Through degree nine the extra factor f₁₆/f₈ contributes 1 + q⁸.
-- Multiplying the proposed coefficients by the unit denominator checks them all at once.
example : regularCubicOverlinedCount 4 9 = 130 := by
  let a (n : ℕ) : ℤ := [1, 2, 4, 8, 13, 22, 36, 56, 86, 130][n]?.getD 0
  let D := qEulerProduct 1 ^ 2 * qEulerProduct 4 * qEulerProduct 8
  have hD : IsUnit D := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp (disch := decide) [D, constantCoeff_qEulerProduct]
  have hg := regularCubicOverlinedCount_generatingFunction (l := 4) (by decide)
  change D * mk (regularCubicOverlinedCount 4) = _ at hg
  have hd : X ^ 10 ∣ mk (regularCubicOverlinedCount 4) - mk a := by
    apply hD.dvd_mul_left.mp
    rw [mul_sub, hg, X_pow_dvd_iff]
    suffices h : ∀ i : Fin 10, coeff i.val
        (qEulerProduct 2 * qEulerProduct 4 ^ 2 * qEulerProduct 16 - D * mk a) = 0 from
      fun n hn ↦ h ⟨n, hn⟩
    simp (disch := decide) only [D, pow_two, map_sub, coeff_mul, coeff_mk, coeff_euler]
    decide
  have h := X_pow_dvd_iff.mp hd 9 (by decide)
  simpa [coeff_mk, a, sub_eq_zero] using h

-- One prime-square step takes the constant coefficient to index 37.
example : regularCubicOverlinedCount 4 37 ≡ 2 [ZMOD 4] := by
  have h := (regularCubicOverlinedCount_four_prime_mod_four 5 (by decide) five_nonsquare 1).1 0
  simpa (disch := decide) [coeff_zero_eq_constantCoeff, constantCoeff_qEulerProduct] using h

-- The first and last admissible nonzero residue classes at p = 5.
example : regularCubicOverlinedCount 4 57 ≡ 0 [ZMOD 4] ∧
    regularCubicOverlinedCount 4 117 ≡ 0 [ZMOD 4] := by
  have h := (regularCubicOverlinedCount_four_prime_mod_four 5 (by decide) five_nonsquare 0).2
  exact ⟨h 0 1 (by decide) (by decide), h 0 4 (by decide) (by decide)⟩

end MetaMathlibExt.regularCubicOverlinedCount_four_prime_mod_four
