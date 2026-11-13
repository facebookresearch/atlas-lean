/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingCriticalPolynomial

namespace StatMech.FrontierA



theorem one_sub_cos_add_le_two_sum (p q : ℝ) :
    1 - Real.cos (p + q) ≤
      2 * ((1 - Real.cos p) + (1 - Real.cos q)) := by
  have hcp : Real.cos p ≤ 1 := Real.cos_le_one p
  have hcq : Real.cos q ≤ 1 := Real.cos_le_one q
  have hp := Real.sin_sq_add_cos_sq p
  have hq := Real.sin_sq_add_cos_sq q
  have hsin : Real.sin p * Real.sin q ≤
      (Real.sin p ^ 2 + Real.sin q ^ 2) / 2 := by
    nlinarith [sq_nonneg (Real.sin p - Real.sin q)]
  have hsq : (Real.sin p ^ 2 + Real.sin q ^ 2) / 2 ≤
      (1 - Real.cos p) + (1 - Real.cos q) := by
    nlinarith [sq_nonneg (1 - Real.cos p), sq_nonneg (1 - Real.cos q)]
  have hprod : 0 ≤ (1 - Real.cos p) * (1 - Real.cos q) :=
    mul_nonneg (by linarith) (by linarith)
  rw [Real.cos_add]
  nlinarith



theorem triangularIsingSymbol_sub_zero (x y p q : ℝ) :
    triangularIsingSymbol x x y p q - triangularIsingSymbol x x y 0 0 =
      Real.sinh (2 * x) *
          ((1 - Real.cos p) + (1 - Real.cos q)) +
        Real.sinh (2 * y) * (1 - Real.cos (p + q)) := by
  simp [triangularIsingSymbol]
  ring



theorem exists_triangularIsingSymbol_quadratic_lower_at_root
    {β J : ℝ} (hβ : 0 < β)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q : ℝ,
      |p| ≤ Real.pi → |q| ≤ Real.pi →
      c * (p ^ 2 + q ^ 2) ≤
        triangularIsingSymbol β β (β * J) p q := by
  let s := Real.sinh (2 * β)
  let r := Real.sinh (2 * (β * J))
  have hs : 0 < s := Real.sinh_pos_iff.mpr (by linarith)
  have hrate : s * (s + 2 * r) = 1 := by
    rw [triangularIsingCriticalRate] at hroot
    change s ^ 2 + 2 * s * r = 1 at hroot
    nlinarith
  have hsum : 0 < s + 2 * r := by
    have hp : 0 < s * (s + 2 * r) := by rw [hrate]; norm_num
    rcases mul_pos_iff.mp hp with h | h
    · exact h.2
    · exact (lt_asymm hs h.1).elim
  have hzero : triangularIsingSymbol β β (β * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hβ).2 hroot
  by_cases hr : 0 ≤ r
  · refine ⟨2 * s / Real.pi ^ 2, ?_, ?_⟩
    · positivity
    · intro p q hp hq
      have hcp := Real.cos_le_one_sub_mul_cos_sq hp
      have hcq := Real.cos_le_one_sub_mul_cos_sq hq
      have hA : 2 / Real.pi ^ 2 * (p ^ 2 + q ^ 2) ≤
          (1 - Real.cos p) + (1 - Real.cos q) := by linarith
      have hB : 0 ≤ 1 - Real.cos (p + q) := by
        linarith [Real.cos_le_one (p + q)]
      have hmul := mul_le_mul_of_nonneg_left hA hs.le
      have hexcess := triangularIsingSymbol_sub_zero β (β * J) p q
      change triangularIsingSymbol β β (β * J) p q -
          triangularIsingSymbol β β (β * J) 0 0 =
        s * ((1 - Real.cos p) + (1 - Real.cos q)) +
          r * (1 - Real.cos (p + q)) at hexcess
      rw [hzero] at hexcess
      calc
        2 * s / Real.pi ^ 2 * (p ^ 2 + q ^ 2) =
            s * (2 / Real.pi ^ 2 * (p ^ 2 + q ^ 2)) := by ring
        _ ≤ s * ((1 - Real.cos p) + (1 - Real.cos q)) := hmul
        _ ≤ s * ((1 - Real.cos p) + (1 - Real.cos q)) +
            r * (1 - Real.cos (p + q)) :=
          le_add_of_nonneg_right (mul_nonneg hr hB)
        _ = triangularIsingSymbol β β (β * J) p q := by
          simpa only [sub_zero] using hexcess.symm
  · have hrneg : r < 0 := lt_of_not_ge hr
    refine ⟨2 * (s + 2 * r) / Real.pi ^ 2, ?_, ?_⟩
    · positivity
    · intro p q hp hq
      let A := (1 - Real.cos p) + (1 - Real.cos q)
      let B := 1 - Real.cos (p + q)
      have hcp := Real.cos_le_one_sub_mul_cos_sq hp
      have hcq := Real.cos_le_one_sub_mul_cos_sq hq
      have hA : 2 / Real.pi ^ 2 * (p ^ 2 + q ^ 2) ≤ A := by
        dsimp [A]
        linarith
      have hB : B ≤ 2 * A := by
        dsimp [A, B]
        exact one_sub_cos_add_le_two_sum p q
      have hrB : 2 * r * A ≤ r * B := by
        have := mul_le_mul_of_nonpos_left hB hrneg.le
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hA hsum.le
      have hexcess := triangularIsingSymbol_sub_zero β (β * J) p q
      change triangularIsingSymbol β β (β * J) p q -
          triangularIsingSymbol β β (β * J) 0 0 = s * A + r * B at hexcess
      rw [hzero] at hexcess
      calc
        2 * (s + 2 * r) / Real.pi ^ 2 * (p ^ 2 + q ^ 2) =
            (s + 2 * r) * (2 / Real.pi ^ 2 * (p ^ 2 + q ^ 2)) := by ring
        _ ≤ (s + 2 * r) * A := hmul
        _ = s * A + 2 * r * A := by ring
        _ ≤ s * A + r * B := by linarith
        _ = triangularIsingSymbol β β (β * J) p q := by
          simpa only [sub_zero] using hexcess.symm

end StatMech.FrontierA
