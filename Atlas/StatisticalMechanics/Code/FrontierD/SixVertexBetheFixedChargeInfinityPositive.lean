/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeInfinityNonzero

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

private theorem sum_Ioi_pair_add {n : Nat} (e : Fin n -> Real) :
    (∑ i, ∑ j ∈ Finset.Ioi i, (e i + e j)) =
      (n - 1 : Nat) * ∑ i, e i := by
  classical
  have hfirst :
      (∑ i, ∑ _j ∈ Finset.Ioi i, e i) =
        ∑ i, (n - 1 - i.val : Nat) * e i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
  have hsecond :
      (∑ i, ∑ j ∈ Finset.Ioi i, e j) =
        ∑ j, j.val * e j := by
    calc
      (∑ i, ∑ j ∈ Finset.Ioi i, e j) =
          ∑ i, ∑ j, if i < j then e j else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            have hIoi : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
              ext j
              simp
            rw [hIoi]
            rw [← Finset.sum_filter]
      _ = ∑ j, ∑ i, if i < j then e j else 0 := Finset.sum_comm
      _ = ∑ j, j.val * e j := by
        apply Finset.sum_congr rfl
        intro j _
        have hIio : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by
          ext i
          simp
        rw [← Finset.sum_filter, ← hIio]
        rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio]
  calc
    (∑ i, ∑ j ∈ Finset.Ioi i, (e i + e j)) =
        (∑ i, ∑ _j ∈ Finset.Ioi i, e i) +
          ∑ i, ∑ j ∈ Finset.Ioi i, e j := by
            simp_rw [Finset.sum_add_distrib]
    _ = ∑ i, ((n - 1 - i.val : Nat) * e i + i.val * e i) := by
      rw [hfirst, hsecond, Finset.sum_add_distrib]
    _ = (n - 1 : Nat) * ∑ i, e i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      have hi := i.isLt
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      ring

private theorem centered_root_difference
    {m a b : Nat} (hm : 0 < m) :
    Complex.exp (-Complex.I *
          (Real.pi * ((a + b : Nat) : Real) / (m : Real))) *
        (Complex.exp (Complex.I *
            (2 * Real.pi * (b : Real) / (m : Real))) -
          Complex.exp (Complex.I *
            (2 * Real.pi * (a : Real) / (m : Real)))) =
      (2 * Real.sin
          (Real.pi * ((b : Real) - a) / (m : Real)) : Real) *
        Complex.I := by
  have hmR : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  let A : Real := Real.pi * a / m
  let B : Real := Real.pi * b / m
  have hcenter : Real.pi * ((a + b : Nat) : Real) / (m : Real) = A + B := by
    dsimp [A, B]
    push_cast
    field_simp [hmR]
  have ha : 2 * Real.pi * (a : Real) / (m : Real) = 2 * A := by
    dsimp [A]
    ring
  have hb : 2 * Real.pi * (b : Real) / (m : Real) = 2 * B := by
    dsimp [B]
    ring
  have hdiff : Real.pi * ((b : Real) - a) / (m : Real) = B - A := by
    dsimp [A, B]
    ring
  have hcenterC' :
      (Real.pi : Complex) * (((a + b : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) =
        (A : Complex) + B := by
    exact_mod_cast hcenter
  have haC :
      (2 : Complex) * Real.pi * (((a : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) = 2 * (A : Complex) := by
    exact_mod_cast ha
  have hbC :
      (2 : Complex) * Real.pi * (((b : Nat) : Real) : Complex) /
          (((m : Nat) : Real) : Complex) = 2 * (B : Complex) := by
    exact_mod_cast hb
  rw [hcenterC', haC, hbC, hdiff]
  rw [show (A : Complex) + B = ((A + B : Real) : Complex) by
    push_cast
    rfl]
  rw [show (2 : Complex) * B = ((2 * B : Real) : Complex) by
    push_cast
    rfl]
  rw [show (2 : Complex) * A = ((2 * A : Real) : Complex) by
    push_cast
    rfl]
  rw [show -Complex.I * ((A + B : Real) : Complex) =
      (-(A + B : Real) : Complex) * Complex.I by push_cast; ring]
  rw [show Complex.I * ((2 * B : Real) : Complex) =
      ((2 * B : Real) : Complex) * Complex.I by ring]
  rw [show Complex.I * ((2 * A : Real) : Complex) =
      ((2 * A : Real) : Complex) * Complex.I by ring]
  rw [← Complex.ofReal_neg]
  simp only [Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_add, Real.sin_add]
  rw [Real.cos_two_mul, Real.sin_two_mul, Real.cos_two_mul, Real.sin_two_mul]
  rw [Real.sin_sub]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one,
      zero_mul, zero_add, add_zero, sub_zero, neg_mul]
  · ring_nf
    calc
      -(Real.cos A * Real.cos B * Real.sin A ^ 2 * 2) +
            Real.cos A * Real.cos B * Real.sin B ^ 2 * 2 +
            Real.cos A * Real.cos B ^ 3 * 2 -
          Real.cos A ^ 3 * Real.cos B * 2 =
          2 * Real.cos A * Real.cos B *
            ((Real.sin B ^ 2 + Real.cos B ^ 2) -
              (Real.sin A ^ 2 + Real.cos A ^ 2)) := by ring
      _ = 0 := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring
  · ring_nf
    calc
      Real.cos A * Real.sin A ^ 2 * Real.sin B * 2 +
            Real.cos A ^ 3 * Real.sin B * 2 -
            Real.cos B * Real.sin A * Real.sin B ^ 2 * 2 -
          Real.cos B ^ 3 * Real.sin A * 2 =
          2 * Real.cos A * Real.sin B *
              (Real.sin A ^ 2 + Real.cos A ^ 2) -
            2 * Real.cos B * Real.sin A *
              (Real.sin B ^ 2 + Real.cos B ^ 2) := by ring
      _ = Real.cos A * Real.sin B * 2 -
          Real.cos B * Real.sin A * 2 := by
            rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]
            ring



def sixVertexFixedChargeLimitingSineProduct (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Real :=
  ∏ i, ∏ j ∈ Finset.Ioi i,
    2 * Real.sin
      (Real.pi *
        ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
          sixVertexFixedChargeAlternantExponent r k x i) /
        (sixVertexFixedChargeBetheComplementCount r k : Real))


def sixVertexFixedChargeBethePairCount (r k : Nat) : Nat :=
  ∑ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
    (Finset.Ioi i).card

private theorem sixVertexFixedChargeLimitingCenterProduct_eq_pairProduct
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    (∏ i, sixVertexFixedChargeLimitingPhaseCenter r k ^
        sixVertexFixedChargeAlternantExponent r k x i) =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        Complex.exp (-Complex.I *
          (Real.pi *
            ((sixVertexFixedChargeAlternantExponent r k x i +
              sixVertexFixedChargeAlternantExponent r k x j : Nat) : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) := by
  let n := sixVertexFixedChargeBetheParticleCount r k
  let m := sixVertexFixedChargeBetheComplementCount r k
  let e := sixVertexFixedChargeAlternantExponent r k x
  simp_rw [sixVertexFixedChargeLimitingPhaseCenter, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  simp_rw [← Complex.exp_sum]
  congr 1
  have hm : (m : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFixedChargeBetheComplementCount_pos r k).ne'
  have hsum := sum_Ioi_pair_add (fun i => (e i : Real))
  dsimp only [n, m, e] at hsum
  have hsumC := congrArg (fun t : Real => (t : Complex)) hsum
  push_cast at hsumC
  calc
    (∑ i, (sixVertexFixedChargeAlternantExponent r k x i : Complex) *
        (-Complex.I *
          (Real.pi *
            (sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) /
              (sixVertexFixedChargeBetheComplementCount r k : Real)))) =
      (-Complex.I *
          (Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real))) *
        (((sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) : Complex) *
          ∑ i, (sixVertexFixedChargeAlternantExponent r k x i : Complex)) := by
            rw [← Finset.sum_mul]
            push_cast
            ring
    _ = (-Complex.I *
          (Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real))) *
        (∑ i, ∑ j ∈ Finset.Ioi i,
          ((sixVertexFixedChargeAlternantExponent r k x i : Complex) +
            (sixVertexFixedChargeAlternantExponent r k x j : Complex))) := by
              rw [hsumC]
    _ = ∑ i, ∑ j ∈ Finset.Ioi i,
        -Complex.I *
          (Real.pi *
            ((sixVertexFixedChargeAlternantExponent r k x i +
              sixVertexFixedChargeAlternantExponent r k x j : Nat) : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              push_cast
              field_simp [hm]

theorem sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      Complex.I ^ sixVertexFixedChargeBethePairCount r k *
        sixVertexFixedChargeLimitingSineProduct r k x := by
  rw [sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde,
    Matrix.det_vandermonde,
    sixVertexFixedChargeLimitingCenterProduct_eq_pairProduct]
  have hIpow : Complex.I ^ sixVertexFixedChargeBethePairCount r k =
      ∏ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
        ∏ _j ∈ Finset.Ioi i, Complex.I := by
    unfold sixVertexFixedChargeBethePairCount
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_const]
  rw [hIpow]
  have hsineCast :
      (sixVertexFixedChargeLimitingSineProduct r k x : Complex) =
        ∏ i, ∏ j ∈ Finset.Ioi i,
          ((2 * Real.sin
            (Real.pi *
              ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
                sixVertexFixedChargeAlternantExponent r k x i) /
              (sixVertexFixedChargeBetheComplementCount r k : Real)) : Real) :
            Complex) := by
    unfold sixVertexFixedChargeLimitingSineProduct
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Complex.ofReal_prod]
  rw [hsineCast]
  conv_lhs => rw [← Finset.prod_mul_distrib]
  conv_rhs => rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  conv_lhs => rw [← Finset.prod_mul_distrib]
  conv_rhs => rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hm := sixVertexFixedChargeBetheComplementCount_pos r k
  simp_rw [sixVertexFixedChargeAlternantPoint,
    sixVertexFixedChargeLimitingPhaseStep, ← Complex.exp_nat_mul]
  rw [show (sixVertexFixedChargeAlternantExponent r k x j : Complex) *
        (Complex.I *
          (2 * Real.pi /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) =
      Complex.I *
        (2 * Real.pi *
          (sixVertexFixedChargeAlternantExponent r k x j : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) by
      push_cast
      ring]
  rw [show (sixVertexFixedChargeAlternantExponent r k x i : Complex) *
        (Complex.I *
          (2 * Real.pi /
            (sixVertexFixedChargeBetheComplementCount r k : Real))) =
      Complex.I *
        (2 * Real.pi *
          (sixVertexFixedChargeAlternantExponent r k x i : Real) /
            (sixVertexFixedChargeBetheComplementCount r k : Real)) by
      push_cast
      ring]
  rw [centered_root_difference hm]
  push_cast
  ring

theorem sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    0 < sixVertexFixedChargeLimitingSineProduct r k x := by
  unfold sixVertexFixedChargeLimitingSineProduct
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have heij :=
    strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent r k x hx hij
  have heijR :
      (sixVertexFixedChargeAlternantExponent r k x i : Real) <
        (sixVertexFixedChargeAlternantExponent r k x j : Real) := by
    exact_mod_cast heij
  have hdiff : (0 : Real) <
      (sixVertexFixedChargeAlternantExponent r k x j : Real) -
        (sixVertexFixedChargeAlternantExponent r k x i : Real) := by
    linarith
  have hspan := sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement
    r k x hx j i
  rw [abs_of_pos hdiff] at hspan
  have hm : (0 : Real) < sixVertexFixedChargeBetheComplementCount r k := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have harg0 : 0 < Real.pi *
      ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
        sixVertexFixedChargeAlternantExponent r k x i) /
      (sixVertexFixedChargeBetheComplementCount r k : Real) := by
    exact div_pos (mul_pos Real.pi_pos hdiff) hm
  have hargpi : Real.pi *
      ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
        sixVertexFixedChargeAlternantExponent r k x i) /
      (sixVertexFixedChargeBetheComplementCount r k : Real) < Real.pi := by
    apply (div_lt_iff₀ hm).2
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi harg0 hargpi)



theorem sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    0 < ((-Complex.I) ^
        sixVertexFixedChargeBethePairCount r k *
      sixVertexFixedChargeLimitingWave r k x).re := by
  rw [sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct]
  rw [← mul_assoc, ← mul_pow]
  norm_num
  simpa using sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent
    r k x hx

end

end StatMech.FrontierD
