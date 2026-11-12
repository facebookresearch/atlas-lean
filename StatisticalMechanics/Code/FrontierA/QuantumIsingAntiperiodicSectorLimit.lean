/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingUniformMode
import Code.Onsager.RiemannPeriodicVarying









open scoped BigOperators
open Filter

namespace StatMech.FrontierA

open StatMech.Onsager

private theorem spectralRoot_one_le_generic {A : Real} (hA : 1 ≤ A) :
    1 ≤ quantumIsingSpectralRoot A := by
  unfold quantumIsingSpectralRoot
  linarith [Real.sqrt_nonneg (A ^ 2 - 1)]

theorem quantumIsingNormalizedSpinSector_a_one_sq_eq_spectralRootProduct
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a : Fin 2)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingNormalizedSpinSector beta h L a 1 ^ 2 =
      ∏ i ∈ Finset.range L,
        ((((1 - (beta * h / (2 * L)) ^ 2) *
            quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi))) ^ L *
          (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)))⁻¹ ^ L) ^ 2 :
          Real) : Complex) := by
  have hL0 : L ≠ 0 := by have := (Fact.out : 2 < L); omega
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  rw [quantumIsingNormalizedSpinSector_sq_eq_reducedProduct
    beta h L a 1 (by positivity) hx1]
  norm_num only [Fin.val_one']
  change (∏ z : ZMod L × ZMod L,
      (fun i j : Nat ↦
        (2 * (1 - (beta * h / (2 * L)) ^ 2) *
          (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) -
            Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L)) : Complex))
        z.1.val z.2.val) = _
  rw [prod_zmod_prod_eq_prod_range L (fun i j : Nat ↦
    (2 * (1 - (beta * h / (2 * L)) ^ 2) *
      (quantumIsingTrotterReducedParameter beta h L
          (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) -
        Real.cos (2 * Real.pi * (j + (1 : Real) / 2) / L)) : Complex))]
  apply Finset.prod_congr rfl
  intro i hi
  let A := quantumIsingTrotterReducedParameter beta h L
    (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)
  let r := quantumIsingSpectralRoot A
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact quantumIsingTrotterReducedParameter_one_le beta h L _
      hbeta.le hh.le hL hx1
  have hr : 1 ≤ r := by
    unfold r
    exact spectralRoot_one_le_generic hA
  have hrepr : (r + r⁻¹) / 2 = A :=
    quantumIsingSpectralRoot_add_inv hA
  have htime := prod_sub_cos_quantumIsingAntiperiodicAngle L hL0 r
    (lt_of_lt_of_le zero_lt_one hr)
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

theorem two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a : Fin 2)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L a 1‖ =
      ∑ i ∈ Finset.range L,
        ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
          (L : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)) +
          2 * Real.log
            (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)))⁻¹ ^ L)) := by
  let S := quantumIsingNormalizedSpinSector beta h L a 1
  let D := 1 - (beta * h / (2 * L)) ^ 2
  let A : Nat → Real := fun i ↦ quantumIsingTrotterReducedParameter beta h L
    (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)
  let r : Nat → Real := fun i ↦ quantumIsingSpectralRoot (A i)
  let B : Nat → Real := fun i ↦ (D * r i) ^ L * (1 + (r i)⁻¹ ^ L) ^ 2
  have hL : 0 < L := by have := (Fact.out : 2 < L); omega
  have hD : 0 < D := by
    dsimp only [D]
    have hx : 0 < beta * h / (2 * L) := by positivity
    nlinarith
  have hr (i : Nat) (hi : i ∈ Finset.range L) : 1 ≤ r i := by
    apply spectralRoot_one_le_generic
    dsimp only [r, A]
    exact quantumIsingTrotterReducedParameter_one_le beta h L _
      hbeta.le hh.le hL hx1
  have hB (i : Nat) (hi : i ∈ Finset.range L) : 0 < B i := by
    dsimp only [B]
    have hri : 0 < r i := lt_of_lt_of_le zero_lt_one (hr i hi)
    positivity
  have hsquare : S ^ 2 =
      ∏ i ∈ Finset.range L, ((B i : Real) : Complex) := by
    exact quantumIsingNormalizedSpinSector_a_one_sq_eq_spectralRootProduct
      beta h L a hbeta hh hx1
  have hnorm : ‖S‖ ^ 2 = ∏ i ∈ Finset.range L, B i := by
    calc
      ‖S‖ ^ 2 = ‖S ^ 2‖ := by rw [norm_pow]
      _ = ‖∏ i ∈ Finset.range L, ((B i : Real) : Complex)‖ := by rw [hsquare]
      _ = ∏ i ∈ Finset.range L, B i := by
        rw [norm_prod]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hB i hi)]
  have hprod : 0 < ∏ i ∈ Finset.range L, B i :=
    Finset.prod_pos fun i hi ↦ hB i hi
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
      have hri : 0 < r i := lt_of_lt_of_le zero_lt_one (hr i hi)
      have hDr : D * r i ≠ 0 := mul_ne_zero hD.ne' hri.ne'
      have hcorr : 1 + (r i)⁻¹ ^ L ≠ 0 := by positivity
      dsimp only [B]
      rw [Real.log_mul (pow_ne_zero _ hDr) (pow_ne_zero _ hcorr),
        Real.log_pow, Real.log_pow, Real.log_mul hD.ne' hri.ne']
      dsimp only [r, A, D]
      rw [log_quantumIsingSpectralRoot]
      ring

theorem two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a : Fin 2)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    (2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L a 1‖) / L =
      (1 / (L : Real)) * ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (a.val : Real) / 2) / L - Real.pi) := by
  rw [two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one
    beta h L a hbeta hh hx1]
  have hsum :
      (∑ k ∈ Finset.range L,
        ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
          (L : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (k + (a.val : Real) / 2) / L - Real.pi)) +
          2 * Real.log
            (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (k + (a.val : Real) / 2) / L - Real.pi)))⁻¹ ^ L))) =
      ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (a.val : Real) / 2) / L - Real.pi) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (quantumIsingTrotterModeContribution_eq_spectralRoot
      beta h L hbeta hh hx1 _).symm
  rw [hsum]
  ring

noncomputable def quantumIsingZeroOneSectorLogDensity
    (beta h : Real) (n : Nat) : Real := by
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  exact (2 * Real.log
    ‖quantumIsingNormalizedSpinSector beta h (n + 3) 0 1‖) / (n + 3)

theorem quantumIsingZeroOneSectorLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingZeroOneSectorLogDensity beta h) atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hleft := StatMech.Onsager.ons_riemann_periodic_shifted_average_of_tendstoUniformly
    (quantumIsingTrotterModeContribution beta h)
    (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
    (continuous_quantumIsingTrotterModeLimit beta h)
    (periodic_quantumIsingTrotterModeLimit beta h)
    (quantumIsingTrotterModeContribution_tendstoUniformly beta h hbeta hh)
  have hxlim : Tendsto (fun L : Nat ↦ beta * h / (2 * (L : Real)))
      atTop (nhds 0) := by
    have hzero := tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)
    convert hzero using 1
    funext L
    ring
  have hxlt : ∀ᶠ L : Nat in atTop,
      beta * h / (2 * (L : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  have hleftShift := hleft.comp (tendsto_add_atTop_nat 3)
  apply hleftShift.congr'
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hxlt] with n hx1
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  dsimp only [Function.comp_apply]
  change (1 / ((n + 3 : Nat) : Real)) *
      ∑ k ∈ Finset.range (n + 3),
        quantumIsingTrotterModeContribution beta h (n + 3)
          (2 * Real.pi * k / ((n + 3 : Nat) : Real) - Real.pi) =
    quantumIsingZeroOneSectorLogDensity beta h n
  unfold quantumIsingZeroOneSectorLogDensity
  simpa only [Fin.val_zero, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
    zero_div, add_zero] using
    (two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage
      beta h (n + 3) 0 hbeta hh hx1).symm

end StatMech.FrontierA
