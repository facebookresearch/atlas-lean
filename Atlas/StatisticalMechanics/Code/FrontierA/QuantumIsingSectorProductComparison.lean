/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingFiniteSpectralBridge
import Code.FrontierA.QuantumIsingPeriodicProduct
import Code.FrontierA.QuantumIsingReducedParameterBounds
import Code.FrontierA.QuantumIsingAntiperiodicReduction
import Code.FrontierA.QuantumIsingArfSandwich










open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingReducedSectorProduct
    (beta h : Real) (L : Nat) (a b : Fin 2) : Real :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    2 * (1 - (beta * h / (2 * L)) ^ 2) *
      (quantumIsingTrotterReducedParameter beta h L
          (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) -
        Real.cos (2 * Real.pi * (j + (b.val : Real) / 2) / L))

theorem quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingNormalizedSpinSector beta h L a b ^ 2 =
      (quantumIsingReducedSectorProduct beta h L a b : Complex) := by
  rw [quantumIsingNormalizedSpinSector_sq_eq_reducedProduct
    beta h L a b hx hx1]
  let F : Nat → Nat → Complex := fun i j =>
    (2 : Complex) *
      (1 - ((beta : Complex) * (h : Complex) / (2 * (L : Complex))) ^ 2) *
      (((quantumIsingTrotterReducedParameter beta h L
          (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) : Real) :
            Complex) -
        (Real.cos (2 * Real.pi * (j + (b.val : Real) / 2) / L) : Complex))
  change (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) = _
  rw [prod_zmod_prod_eq_prod_range L F]
  unfold quantumIsingReducedSectorProduct
  dsimp only [F]
  norm_cast

theorem quantumIsingReducedSectorProduct_nonneg
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (hbeta : 0 < beta)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    0 ≤ quantumIsingReducedSectorProduct beta h L a b := by
  unfold quantumIsingReducedSectorProduct
  apply Finset.prod_nonneg
  intro i hi
  apply Finset.prod_nonneg
  intro j hj
  have hL : 0 < (2 * (L : Real)) := by
    have := Fact.out (p := 2 < L)
    positivity
  have ht : 0 < beta / (2 * L) := div_pos hbeta hL
  have hA := one_le_quantumIsingTrotterReducedParameter beta h L
    (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) ht hx hx1
  have hcos := Real.cos_le_one
    (2 * Real.pi * (j + (b.val : Real) / 2) / L)
  have hc : 0 ≤ 2 * (1 - (beta * h / (2 * L)) ^ 2) := by
    have : (beta * h / (2 * L)) ^ 2 < 1 := by nlinarith
    positivity
  exact mul_nonneg hc (sub_nonneg.mpr (hcos.trans hA))

private theorem spectralRoot_one_le {A : Real} (hA : 1 ≤ A) :
    1 ≤ quantumIsingSpectralRoot A := by
  unfold quantumIsingSpectralRoot
  have := Real.sqrt_nonneg (A ^ 2 - 1)
  linarith

theorem quantumIsingReducedSectorProduct_periodic_le_antiperiodic
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a : Fin 2)
    (hbeta : 0 < beta)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingReducedSectorProduct beta h L a 0 ≤
      quantumIsingReducedSectorProduct beta h L a 1 := by
  unfold quantumIsingReducedSectorProduct
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.prod_nonneg fun j hj => by
      have hL : 0 < (2 * (L : Real)) := by
        have := Fact.out (p := 2 < L)
        positivity
      have ht : 0 < beta / (2 * L) := div_pos hbeta hL
      have hA := one_le_quantumIsingTrotterReducedParameter beta h L
        (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) ht hx hx1
      have hcos := Real.cos_le_one
        (2 * Real.pi * (j + ((0 : Fin 2).val : Real) / 2) / L)
      have hc : 0 ≤ 2 * (1 - (beta * h / (2 * L)) ^ 2) := by
        have : (beta * h / (2 * L)) ^ 2 < 1 := by nlinarith
        positivity
      exact mul_nonneg hc (sub_nonneg.mpr (hcos.trans hA))
  · intro i hi
    let A := quantumIsingTrotterReducedParameter beta h L
      (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)
    let r := quantumIsingSpectralRoot A
    let c := 2 * (1 - (beta * h / (2 * L)) ^ 2)
    have hL0 : L ≠ 0 := by have := Fact.out (p := 2 < L); omega
    have ht : 0 < beta / (2 * L) := div_pos hbeta (by positivity)
    have hA : 1 ≤ A := one_le_quantumIsingTrotterReducedParameter
      beta h L _ ht hx hx1
    have hr : 1 ≤ r := spectralRoot_one_le hA
    have hrepr : (r + r⁻¹) / 2 = A :=
      quantumIsingSpectralRoot_add_inv hA
    have hp := prod_sub_cos_periodic_le_antiperiodic L hL0 r hr
    rw [hrepr] at hp
    have hc : 0 ≤ c ^ L := pow_nonneg (by dsimp [c]; nlinarith) _
    have hp' := mul_le_mul_of_nonneg_left hp hc
    have hzero (j : Nat) :
        2 * Real.pi * (j + ((0 : Fin 2).val : Real) / 2) / L =
          quantumIsingPeriodicAngle L j := by
      unfold quantumIsingPeriodicAngle
      norm_num
      ring
    have hone (j : Nat) :
        2 * Real.pi * (j + ((1 : Fin 2).val : Real) / 2) / L =
          quantumIsingAntiperiodicAngle L j := by
      unfold quantumIsingAntiperiodicAngle
      norm_num
      ring
    rw [mul_pow] at hp'
    simpa only [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, hzero, hone, A, c] using hp'

theorem quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a : Fin 2)
    (hbeta : 0 < beta)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    ‖quantumIsingNormalizedSpinSector beta h L a 0‖ ≤
      ‖quantumIsingNormalizedSpinSector beta h L a 1‖ := by
  have hs0 := quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct
    beta h L a 0 hx hx1
  have hs1 := quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct
    beta h L a 1 hx hx1
  have hp := quantumIsingReducedSectorProduct_periodic_le_antiperiodic
    beta h L a hbeta hx hx1
  have hp0 := quantumIsingReducedSectorProduct_nonneg
    beta h L a 0 hbeta hx hx1
  have hp1 := quantumIsingReducedSectorProduct_nonneg
    beta h L a 1 hbeta hx hx1
  have hn0 := congrArg norm hs0
  have hn1 := congrArg norm hs1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0] at hn0
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp1] at hn1
  nlinarith [norm_nonneg (quantumIsingNormalizedSpinSector beta h L a 0),
    norm_nonneg (quantumIsingNormalizedSpinSector beta h L a 1)]



theorem quantumIsingReducedSectorProduct_spatialPeriodic_le_antiperiodic
    (beta h : Real) (L : Nat) [Fact (2 < L)] (b : Fin 2)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingReducedSectorProduct beta h L 0 b ≤
      quantumIsingReducedSectorProduct beta h L 1 b := by
  have hL0 : L ≠ 0 := by have := Fact.out (p := 2 < L); omega
  have hL : 0 < (L : Real) := by positivity
  let t := beta / (2 * (L : Real))
  let x := beta * h / (2 * (L : Real))
  let D := 2 * (1 - x ^ 2)
  let C := Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2))
  let B := Real.sinh t * (2 * x / (1 - x ^ 2))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hden : 0 < 1 - x ^ 2 := by dsimp only [x]; nlinarith
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (Real.sinh_pos_iff.mpr ht)
      (div_pos (mul_pos (by norm_num) hx) hden)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  unfold quantumIsingReducedSectorProduct
  conv_lhs => rw [Finset.prod_comm]
  conv_rhs => rw [Finset.prod_comm]
  apply Finset.prod_le_prod
  · intro j hj
    apply Finset.prod_nonneg
    intro i hi
    have hA := one_le_quantumIsingTrotterReducedParameter beta h L
      (2 * Real.pi * (i + (((0 : Fin 2).val : Real) / 2)) / L - Real.pi)
      (by dsimp only [t] at ht; exact ht) hx hx1
    exact mul_nonneg hD
      (sub_nonneg.mpr (Real.cos_le_one _ |>.trans hA))
  · intro j hj
    let q := 2 * Real.pi * (j + (b.val : Real) / 2) / L
    let R := (C - Real.cos q) / B
    let r := quantumIsingSpectralRoot R
    have hbase := one_le_quantumIsingTrotterReducedParameter
      beta h L Real.pi (by dsimp only [t] at ht; exact ht) hx hx1
    have hCB : 1 ≤ C - B := by
      simpa only [quantumIsingTrotterReducedParameter, t, x, C, B,
        Real.cos_pi, mul_neg, mul_one] using hbase
    have hR : 1 ≤ R := by
      dsimp only [R]
      rw [le_div_iff₀ hB]
      nlinarith [Real.cos_le_one q]
    have hr : 1 ≤ r := spectralRoot_one_le hR
    have hrepr : (r + r⁻¹) / 2 = R :=
      quantumIsingSpectralRoot_add_inv hR
    have hp := prod_sub_cos_periodic_le_antiperiodic L hL0 r hr
    rw [hrepr] at hp
    let K := D * B
    have hK : 0 ≤ K := mul_nonneg hD hB.le
    have hAform (p : Real) :
        quantumIsingTrotterReducedParameter beta h L p =
          C + B * Real.cos p := by
      rfl
    have hzero (i : Nat) :
        D * (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (((0 : Fin 2).val : Real) / 2)) / L -
                Real.pi) - Real.cos q) =
          K * (R - Real.cos (quantumIsingPeriodicAngle L i)) := by
      have hangle :
          2 * Real.pi * (i + (((0 : Fin 2).val : Real) / 2)) / L -
              Real.pi = quantumIsingPeriodicAngle L i - Real.pi := by
        unfold quantumIsingPeriodicAngle
        norm_num
        ring
      rw [hAform, hangle, Real.cos_sub_pi]
      dsimp only [K, R]
      field_simp [hB.ne']
      ring
    have hone (i : Nat) :
        D * (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (((1 : Fin 2).val : Real) / 2)) / L -
                Real.pi) - Real.cos q) =
          K * (R - Real.cos (quantumIsingAntiperiodicAngle L i)) := by
      have hangle :
          2 * Real.pi * (i + (((1 : Fin 2).val : Real) / 2)) / L -
              Real.pi = quantumIsingAntiperiodicAngle L i - Real.pi := by
        unfold quantumIsingAntiperiodicAngle
        norm_num
        ring
      rw [hAform, hangle, Real.cos_sub_pi]
      dsimp only [K, R]
      field_simp [hB.ne']
      ring
    simp_rw [show 2 * (1 - (beta * h / (2 * (L : Real))) ^ 2) = D by rfl]
    simp_rw [show 2 * Real.pi * (j + (b.val : Real) / 2) / (L : Real) = q by rfl]
    simp_rw [hzero, hone, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    exact mul_le_mul_of_nonneg_left hp (pow_nonneg hK _)

theorem quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic
    (beta h : Real) (L : Nat) [Fact (2 < L)] (b : Fin 2)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    ‖quantumIsingNormalizedSpinSector beta h L 0 b‖ ≤
      ‖quantumIsingNormalizedSpinSector beta h L 1 b‖ := by
  have hp := quantumIsingReducedSectorProduct_spatialPeriodic_le_antiperiodic
    beta h L b hbeta hh hx hx1
  have hs0 := quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct
    beta h L 0 b hx hx1
  have hs1 := quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct
    beta h L 1 b hx hx1
  have hp0 := quantumIsingReducedSectorProduct_nonneg
    beta h L 0 b hbeta hx hx1
  have hp1 := quantumIsingReducedSectorProduct_nonneg
    beta h L 1 b hbeta hx hx1
  have hn0 := congrArg norm hs0
  have hn1 := congrArg norm hs1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0] at hn0
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp1] at hn1
  nlinarith [norm_nonneg (quantumIsingNormalizedSpinSector beta h L 0 b),
    norm_nonneg (quantumIsingNormalizedSpinSector beta h L 1 b)]

theorem arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L) =
      ‖quantumIsingNormalizedSpinSector beta h L 1 1‖ := by
  have ht0 := quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic
    beta h L 0 hbeta hx hx1
  have ht1 := quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic
    beta h L 1 hbeta hx hx1
  have hs0 := quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic
    beta h L 0 hbeta hh hx hx1
  have hs1 := quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic
    beta h L 1 hbeta hh hx hx1
  unfold arfSectorNormMax
  rw [max_eq_left hs1, max_eq_left hs0, max_eq_left ht1]

end StatMech.FrontierA
