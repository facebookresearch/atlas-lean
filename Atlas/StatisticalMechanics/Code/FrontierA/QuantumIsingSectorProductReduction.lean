/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.QuantumIsingFiniteSpectralBridge
import Code.FrontierA.QuantumIsingAntiperiodicReduction








open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager

private theorem reducedParameterExpression_one_le
    (t x k : Real) (ht : 0 ≤ t) (hx : 0 ≤ x) (hx1 : x < 1) :
    1 ≤ Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
      Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k := by
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hsinh : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
  have hcos : 0 ≤ Real.cos k + 1 := by
    linarith [Real.neg_one_le_cos k]
  have hcoshDouble := Real.cosh_two_mul (t / 2)
  have hsinhDouble := Real.sinh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hcoshDouble hsinhDouble
  have hminimum :
      Real.cosh t * (1 + x ^ 2) - 2 * x * Real.sinh t -
          (1 - x ^ 2) =
        2 * (x * Real.cosh (t / 2) - Real.sinh (t / 2)) ^ 2 := by
    rw [hcoshDouble, hsinhDouble]
    nlinarith
  have hnumerator : 0 ≤
      Real.cosh t * (1 + x ^ 2) +
        2 * x * Real.sinh t * Real.cos k - (1 - x ^ 2) := by
    rw [show Real.cosh t * (1 + x ^ 2) +
          2 * x * Real.sinh t * Real.cos k - (1 - x ^ 2) =
        (Real.cosh t * (1 + x ^ 2) - 2 * x * Real.sinh t -
          (1 - x ^ 2)) +
          2 * x * Real.sinh t * (Real.cos k + 1) by ring,
      hminimum]
    positivity
  rw [show Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
        Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k =
      (Real.cosh t * (1 + x ^ 2) +
        2 * x * Real.sinh t * Real.cos k) / (1 - x ^ 2) by
    field_simp [hden.ne']]
  exact (le_div_iff₀ hden).2 (by linarith)

private theorem reducedParameterExpression_one_lt
    (t x k : Real) (ht : 0 < t) (hx : 0 < x) (hx1 : x < 1)
    (hk : -1 < Real.cos k) :
    1 < Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
      Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k := by
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hcos : 0 < Real.cos k + 1 := by linarith
  have hcoshDouble := Real.cosh_two_mul (t / 2)
  have hsinhDouble := Real.sinh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hcoshDouble hsinhDouble
  have hminimum :
      Real.cosh t * (1 + x ^ 2) - 2 * x * Real.sinh t -
          (1 - x ^ 2) =
        2 * (x * Real.cosh (t / 2) - Real.sinh (t / 2)) ^ 2 := by
    rw [hcoshDouble, hsinhDouble]
    nlinarith
  have hnumerator : 0 <
      Real.cosh t * (1 + x ^ 2) +
        2 * x * Real.sinh t * Real.cos k - (1 - x ^ 2) := by
    rw [show Real.cosh t * (1 + x ^ 2) +
          2 * x * Real.sinh t * Real.cos k - (1 - x ^ 2) =
        (Real.cosh t * (1 + x ^ 2) - 2 * x * Real.sinh t -
          (1 - x ^ 2)) +
          2 * x * Real.sinh t * (Real.cos k + 1) by ring,
      hminimum]
    positivity
  rw [show Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
        Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k =
      (Real.cosh t * (1 + x ^ 2) +
        2 * x * Real.sinh t * Real.cos k) / (1 - x ^ 2) by
    field_simp [hden.ne']]
  exact (lt_div_iff₀ hden).2 (by linarith)

theorem quantumIsingTrotterReducedParameter_one_le
    (beta h : Real) (n : Nat) (k : Real)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hn : 0 < n)
    (hx1 : beta * h / (2 * n) < 1) :
    1 ≤ quantumIsingTrotterReducedParameter beta h n k := by
  unfold quantumIsingTrotterReducedParameter
  exact reducedParameterExpression_one_le _ _ _
    (by positivity) (by positivity) hx1

theorem quantumIsingTrotterReducedParameter_one_lt_of_cos
    (beta h : Real) (n : Nat) (k : Real)
    (hbeta : 0 < beta) (hh : 0 < h) (hn : 0 < n)
    (hx1 : beta * h / (2 * n) < 1)
    (hk : -1 < Real.cos k) :
    1 < quantumIsingTrotterReducedParameter beta h n k := by
  unfold quantumIsingTrotterReducedParameter
  exact reducedParameterExpression_one_lt _ _ _
    (by positivity) (by positivity) hx1 hk

theorem cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one
    (L : Nat) [Fact (2 < L)] (i : Nat) (hi : i < L) :
    -1 < Real.cos
      (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi) := by
  let p : Real := 2 * Real.pi * (i + (1 : Real) / 2) / L
  have hL : 0 < (L : Real) := by
    have := (Fact.out : 2 < L)
    positivity
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hp2 : p < 2 * Real.pi := by
    dsimp only [p]
    rw [div_lt_iff₀ hL]
    have hi1R : (i : Real) + 1 ≤ L := by
      exact_mod_cast (Nat.succ_le_iff.mpr hi)
    have hi' : (i : Real) + 1 / 2 < L := by linarith
    nlinarith [Real.pi_pos]
  have hcne : Real.cos p ≠ 1 := by
    intro hc
    have hp0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hp2).mp hc
    linarith
  have hclt : Real.cos p < 1 :=
    lt_of_le_of_ne (Real.cos_le_one p) hcne
  change -1 < Real.cos (p - Real.pi)
  rw [Real.cos_sub_pi]
  linarith



theorem quantumIsingNormalizedSpinSector_eleven_sq_eq_spectralRootProduct
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingNormalizedSpinSector beta h L 1 1 ^ 2 =
      ∏ i ∈ Finset.range L,
        ((((1 - (beta * h / (2 * L)) ^ 2) *
            quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi))) ^ L *
          (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L) ^ 2 :
          Real) : Complex) := by
  have hL0 : L ≠ 0 := by have := (Fact.out : 2 < L); omega
  rw [quantumIsingNormalizedSpinSector_sq_eq_reducedProduct
    beta h L 1 1 (by positivity) hx1]
  norm_num only [Fin.val_one']
  change (∏ z : ZMod L × ZMod L,
      (fun i j : Nat ↦
        (2 * (1 - (beta * h / (2 * L)) ^ 2) *
          (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi) -
            Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L)) : Complex))
        z.1.val z.2.val) = _
  rw [prod_zmod_prod_eq_prod_range L (fun i j : Nat ↦
    (2 * (1 - (beta * h / (2 * L)) ^ 2) *
      (quantumIsingTrotterReducedParameter beta h L
          (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi) -
        Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L)) : Complex))]
  apply Finset.prod_congr rfl
  intro i hi
  have hiL := Finset.mem_range.mp hi
  let A := quantumIsingTrotterReducedParameter beta h L
    (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)
  let r := quantumIsingSpectralRoot A
  have hcos : -1 < Real.cos
      (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi) :=
    cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one L i hiL
  have hA : 1 < A := by
    dsimp only [A]
    exact quantumIsingTrotterReducedParameter_one_lt_of_cos beta h L _
      hbeta hh (by omega) hx1 hcos
  have hr : 1 < r := quantumIsingSpectralRoot_gt_one hA
  have hrepr : (r + r⁻¹) / 2 = A :=
    quantumIsingSpectralRoot_add_inv hA.le
  have htime := prod_sub_cos_quantumIsingAntiperiodicAngle L hL0 r
    (lt_trans zero_lt_one hr)
  rw [hrepr] at htime
  have hangle (j : Nat) :
      2 * Real.pi * (j + (1 : Real) / 2) / L =
        quantumIsingAntiperiodicAngle L j := by
    unfold quantumIsingAntiperiodicAngle
    ring
  have htime' :
      (∏ j ∈ Finset.range L,
        (A - Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L))) =
        (r / 2) ^ L * (1 + r⁻¹ ^ L) ^ 2 := by
    rw [show (∏ j ∈ Finset.range L,
        (A - Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L))) =
      ∏ j ∈ Finset.range L,
        (A - Real.cos (quantumIsingAntiperiodicAngle L j)) by
      apply Finset.prod_congr rfl
      intro j _
      rw [hangle]]
    exact htime
  norm_cast
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  change (2 * (1 - (beta * h / (2 * L)) ^ 2)) ^ L *
      (∏ j ∈ Finset.range L,
        (A - Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L))) = _
  rw [htime']
  dsimp only [r, A]
  rw [← mul_assoc, ← mul_pow]
  ring


theorem two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L 1 1‖ =
      ∑ i ∈ Finset.range L,
        ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
          (L : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)) +
          2 * Real.log
            (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L)) := by
  let S := quantumIsingNormalizedSpinSector beta h L 1 1
  let D := 1 - (beta * h / (2 * L)) ^ 2
  let A : Nat → Real := fun i ↦ quantumIsingTrotterReducedParameter beta h L
    (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)
  let r : Nat → Real := fun i ↦ quantumIsingSpectralRoot (A i)
  let B : Nat → Real := fun i ↦ (D * r i) ^ L * (1 + (r i)⁻¹ ^ L) ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    have hL : 0 < (L : Real) := by
      have := (Fact.out : 2 < L)
      positivity
    have hx : 0 < beta * h / (2 * L) :=
      div_pos (mul_pos hbeta hh) (mul_pos (by norm_num) hL)
    nlinarith
  have hr (i : Nat) (hi : i ∈ Finset.range L) : 1 < r i := by
    have hiL := Finset.mem_range.mp hi
    have hcos := cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one L i hiL
    apply quantumIsingSpectralRoot_gt_one
    dsimp only [r, A]
    exact quantumIsingTrotterReducedParameter_one_lt_of_cos beta h L _
      hbeta hh (by have := (Fact.out : 2 < L); omega) hx1 hcos
  have hB (i : Nat) (hi : i ∈ Finset.range L) : 0 < B i := by
    dsimp only [B]
    have hri : 0 < r i := lt_trans zero_lt_one (hr i hi)
    positivity
  have hsquare : S ^ 2 =
      ∏ i ∈ Finset.range L, ((B i : Real) : Complex) := by
    exact quantumIsingNormalizedSpinSector_eleven_sq_eq_spectralRootProduct
      beta h L hbeta hh hx1
  have hnorm : ‖S‖ ^ 2 = ∏ i ∈ Finset.range L, B i := by
    calc
      ‖S‖ ^ 2 = ‖S ^ 2‖ := by rw [norm_pow]
      _ = ‖∏ i ∈ Finset.range L, ((B i : Real) : Complex)‖ := by rw [hsquare]
      _ = ∏ i ∈ Finset.range L, B i := by
        rw [norm_prod]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hB i hi)]
  have hprod : 0 < ∏ i ∈ Finset.range L, B i := by
    exact Finset.prod_pos fun i hi ↦ hB i hi
  have hSnorm : 0 < ‖S‖ := by
    have hsq : 0 < ‖S‖ ^ 2 := by rw [hnorm]; exact hprod
    nlinarith [norm_nonneg S]
  calc
    2 * Real.log ‖S‖ = Real.log (‖S‖ ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log (∏ i ∈ Finset.range L, B i) := by rw [hnorm]
    _ = ∑ i ∈ Finset.range L, Real.log (B i) :=
      Real.log_prod fun i hi ↦ (hB i hi).ne'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hri : 0 < r i := lt_trans zero_lt_one (hr i hi)
      have hDr : D * r i ≠ 0 := mul_ne_zero hD.ne' hri.ne'
      have hcorr : 1 + (r i)⁻¹ ^ L ≠ 0 := by positivity
      dsimp only [B]
      rw [Real.log_mul (pow_ne_zero _ hDr) (pow_ne_zero _ hcorr),
        Real.log_pow, Real.log_pow, Real.log_mul hD.ne' hri.ne']
      dsimp only [r, A, D]
      rw [log_quantumIsingSpectralRoot]
      ring

end StatMech.FrontierA
