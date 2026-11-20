/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingAntiperiodicProduct










open scoped BigOperators

namespace StatMech.FrontierA

noncomputable def quantumIsingPeriodicRoot (n : Nat) (j : Nat) : Complex :=
  Complex.exp (2 * Real.pi * Complex.I / n) ^ j

theorem prod_one_sub_quantumIsingPeriodicRoot
    (n : Nat) (hn : n ≠ 0) (z : Complex) :
    (∏ j ∈ Finset.range n, (1 - z * quantumIsingPeriodicRoot n j)) =
      1 - z ^ n := by
  let zeta : Complex := Complex.exp (2 * Real.pi * Complex.I / n)
  have hzeta : IsPrimitiveRoot zeta n := by
    simpa [zeta] using Complex.isPrimitiveRoot_exp n hn
  have hp := X_pow_sub_C_eq_prod hzeta (Nat.pos_of_ne_zero hn)
    (by rfl : z ^ n = z ^ n)
  apply_fun Polynomial.eval (1 : Complex) at hp
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  calc
    (∏ j ∈ Finset.range n, (1 - z * quantumIsingPeriodicRoot n j)) =
        ∏ j ∈ Finset.range n, (1 - zeta ^ j * z) := by
      apply Finset.prod_congr rfl
      intro j hj
      unfold quantumIsingPeriodicRoot
      dsimp [zeta]
      ring
    _ = 1 - z ^ n := hp.symm

noncomputable def quantumIsingPeriodicAngle (n : Nat) (j : Nat) : Real :=
  2 * (j : Real) * Real.pi / n

private theorem quantumIsingPeriodicRoot_eq_exp
    (n j : Nat) (hn : n ≠ 0) :
    quantumIsingPeriodicRoot n j =
      Complex.exp ((quantumIsingPeriodicAngle n j : Real) * Complex.I) := by
  unfold quantumIsingPeriodicRoot quantumIsingPeriodicAngle
  rw [← Complex.exp_nat_mul]
  congr 1
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnC]
  push_cast
  field_simp [hnC]

private theorem normSq_one_sub_real_mul_periodicRoot
    (n j : Nat) (hn : n ≠ 0) (z : Real) :
    Complex.normSq (1 - (z : Complex) * quantumIsingPeriodicRoot n j) =
      1 - 2 * z * Real.cos (quantumIsingPeriodicAngle n j) + z ^ 2 := by
  rw [quantumIsingPeriodicRoot_eq_exp n j hn, Complex.exp_mul_I,
    Complex.normSq_apply]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq (quantumIsingPeriodicAngle n j)]

theorem prod_sub_cos_quantumIsingPeriodicAngle
    (n : Nat) (hn : n ≠ 0) (r : Real) (hr : 0 < r) :
    (∏ j ∈ Finset.range n,
      ((r + r⁻¹) / 2 - Real.cos (quantumIsingPeriodicAngle n j))) =
      (r / 2) ^ n * (1 - r⁻¹ ^ n) ^ 2 := by
  let z : Real := r⁻¹
  have hr0 : r ≠ 0 := hr.ne'
  have hfactor (j : Nat) :
      (r + r⁻¹) / 2 - Real.cos (quantumIsingPeriodicAngle n j) =
        (r / 2) *
          (1 - 2 * z * Real.cos (quantumIsingPeriodicAngle n j) + z ^ 2) := by
    dsimp [z]
    field_simp [hr0]
    ring
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hnorm :
      (∏ j ∈ Finset.range n,
        (1 - 2 * z * Real.cos (quantumIsingPeriodicAngle n j) + z ^ 2)) =
      Complex.normSq (∏ j ∈ Finset.range n,
        (1 - (z : Complex) * quantumIsingPeriodicRoot n j)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact (normSq_one_sub_real_mul_periodicRoot n j hn z).symm
  rw [hnorm, prod_one_sub_quantumIsingPeriodicRoot n hn (z : Complex)]
  congr 1
  change Complex.normSq (1 - ((r⁻¹ : Real) : Complex) ^ n) =
    (1 - r⁻¹ ^ n) ^ 2
  have hzpow : (((r⁻¹ : Real) : Complex) ^ n) =
      (((r⁻¹ : Real) ^ n : Real) : Complex) := by
    exact_mod_cast rfl
  rw [hzpow, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero,
    zero_mul]
  ring

theorem prod_sub_cos_periodic_le_antiperiodic
    (n : Nat) (hn : n ≠ 0) (r : Real) (hr : 1 ≤ r) :
    (∏ j ∈ Finset.range n,
      ((r + r⁻¹) / 2 - Real.cos (quantumIsingPeriodicAngle n j))) ≤
    ∏ j ∈ Finset.range n,
      ((r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j)) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  rw [prod_sub_cos_quantumIsingPeriodicAngle n hn r hrpos,
    prod_sub_cos_quantumIsingAntiperiodicAngle n hn r hrpos]
  have hz : 0 ≤ r⁻¹ ^ n := by positivity
  have hsq : (1 - r⁻¹ ^ n) ^ 2 ≤ (1 + r⁻¹ ^ n) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq (pow_nonneg (by positivity) _)

end StatMech.FrontierA
