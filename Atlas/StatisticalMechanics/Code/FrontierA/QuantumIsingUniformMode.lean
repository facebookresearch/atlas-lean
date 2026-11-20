/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingUniformArcosh
import Code.FrontierA.QuantumIsingSectorProductReduction
import Code.FrontierA.QuantumIsingScalarNormalizationLimit
import Code.Onsager.RiemannPeriodicMidpoint
import Mathlib.Analysis.Calculus.MeanValue










open Filter Set
open scoped Topology BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingRapidityCorrection (x : Real) : Real :=
  x + 2 * Real.log (1 + Real.exp (-x))

theorem quantumIsingRapidityCorrection_eq_cosh (x : Real) :
    quantumIsingRapidityCorrection x =
      2 * Real.log 2 + 2 * Real.log (Real.cosh (x / 2)) := by
  have hprodOne :
      Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hprodNeg :
      Real.exp (-x / 2) * Real.exp (-(x / 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor :
      1 + Real.exp (-x) =
        2 * Real.exp (-x / 2) * Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    symm
    calc
      2 * Real.exp (-x / 2) *
          ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) =
          Real.exp (-x / 2) * Real.exp (x / 2) +
            Real.exp (-x / 2) * Real.exp (-(x / 2)) := by ring
      _ = 1 + Real.exp (-x) := by rw [hprodOne, hprodNeg]
  have hlog : Real.log (1 + Real.exp (-x)) =
      Real.log 2 + Real.log (Real.exp (-x / 2)) +
        Real.log (Real.cosh (x / 2)) := by
    rw [hfactor,
      Real.log_mul
        (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))
        (Real.cosh_pos _).ne',
      Real.log_mul (by norm_num) (Real.exp_ne_zero _)]
  unfold quantumIsingRapidityCorrection
  rw [hlog, Real.log_exp]
  ring

theorem quantumIsingRapidityCorrection_hasDerivAt (x : Real) :
    HasDerivAt quantumIsingRapidityCorrection (Real.tanh (x / 2)) x := by
  have heq : quantumIsingRapidityCorrection =
      fun y ↦ 2 * Real.log 2 + 2 * Real.log (Real.cosh (y / 2)) :=
    funext quantumIsingRapidityCorrection_eq_cosh
  rw [heq]
  convert (Real.hasDerivAt_log (Real.cosh_pos (x / 2)).ne').comp x
      ((Real.hasDerivAt_cosh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)) |>.const_mul 2 |>.const_add
        (2 * Real.log 2) using 1 <;>
    rw [Real.tanh_eq_sinh_div_cosh] <;> ring

theorem quantumIsingRapidityCorrection_lipschitz :
    LipschitzWith 1 quantumIsingRapidityCorrection := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (quantumIsingRapidityCorrection_hasDerivAt x).differentiableAt
  · intro x
    rw [(quantumIsingRapidityCorrection_hasDerivAt x).deriv]
    simpa only [Real.nnnorm_of_nonneg (abs_nonneg _), NNReal.coe_one,
      Real.norm_eq_abs] using (Real.abs_tanh_lt_one (x / 2)).le

noncomputable def quantumIsingModeScalarNormalization
    (beta h : Real) (n : Nat) : Real :=
  (n + 1 : Real) * Real.log
    (1 - (beta * h / (2 * (n + 1 : Real))) ^ 2)

theorem quantumIsingModeScalarNormalization_tendsto_zero
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingModeScalarNormalization beta h) atTop (nhds 0) := by
  simpa only [quantumIsingModeScalarNormalization] using
    quantumIsingTrotterScalarNormalization_tendsto_zero beta h hbeta hh

noncomputable def quantumIsingShiftedTrotterModeContribution
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  quantumIsingModeScalarNormalization beta h n +
    quantumIsingRapidityCorrection (quantumIsingScaledArcosh beta h n k)

theorem quantumIsingShiftedTrotterModeContribution_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (quantumIsingShiftedTrotterModeContribution beta h)
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
  have hrapid := quantumIsingScaledArcosh_tendstoUniformly_dispersion
    beta h hbeta hh
  have hcorr := quantumIsingRapidityCorrection_lipschitz.uniformContinuous
    |>.comp_tendstoUniformly hrapid
  have hnorm := (quantumIsingModeScalarNormalization_tendsto_zero
    beta h hbeta hh).tendstoUniformly_const (α := Real)
  have hsum := hnorm.add hcorr
  convert hsum using 1
  · funext k
    rw [Pi.add_apply, zero_add, Function.comp_apply,
      quantumIsingRapidityCorrection_eq_cosh]
    unfold quantumIsingModeLog
    congr 3
    ring

noncomputable def quantumIsingTrotterModeContribution
    (beta h : Real) (L : Nat) (k : Real) : Real :=
  if L = 0 then 0 else
    (L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
      quantumIsingRapidityCorrection
        ((L : Real) * Real.arcosh
          (quantumIsingTrotterReducedParameter beta h L k))

theorem quantumIsingTrotterModeContribution_succ
    (beta h : Real) (n : Nat) (k : Real) :
    quantumIsingTrotterModeContribution beta h (n + 1) k =
      quantumIsingShiftedTrotterModeContribution beta h n k := by
  simp only [quantumIsingTrotterModeContribution, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, quantumIsingShiftedTrotterModeContribution,
    quantumIsingModeScalarNormalization, quantumIsingScaledArcosh]
  norm_num only [Nat.cast_add, Nat.cast_one]

theorem quantumIsingTrotterModeContribution_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (quantumIsingTrotterModeContribution beta h)
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
  have hshift := quantumIsingShiftedTrotterModeContribution_tendstoUniformly
    beta h hbeta hh
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    ((Metric.tendstoUniformly_iff.mp hshift) epsilon hepsilon))
  rw [eventually_atTop]
  refine ⟨N + 1, fun L hL k ↦ ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.zero_lt_succ N) hL
  have hpred : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
  have hpredN : N ≤ L - 1 := by omega
  rw [← hpred, quantumIsingTrotterModeContribution_succ]
  exact hN (L - 1) hpredN k

theorem continuous_quantumIsingTrotterModeLimit (beta h : Real) :
    Continuous (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) :=
  continuous_const.add (continuous_const.mul
    (continuous_quantumIsingModeLog beta h))

theorem periodic_quantumIsingTrotterModeLimit (beta h : Real) :
    Function.Periodic
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
      (2 * Real.pi) := by
  intro k
  dsimp only
  rw [periodic_quantumIsingModeLog beta h k]

theorem quantumIsingTrotterModeContribution_midpoint_average_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun L : Nat ↦
      (1 / (L : Real)) * ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi))
      atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hmid := ons_riemann_periodic_midpoint_average_of_tendstoUniformly
    (quantumIsingTrotterModeContribution beta h)
    (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
    (continuous_quantumIsingTrotterModeLimit beta h)
    (periodic_quantumIsingTrotterModeLimit beta h)
    (quantumIsingTrotterModeContribution_tendstoUniformly beta h hbeta hh)
  exact hmid

theorem quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh
    {A : Real} (hA : 1 ≤ A) (L : Nat) :
    (quantumIsingSpectralRoot A)⁻¹ ^ L =
      Real.exp (-(L : Real) * Real.arcosh A) := by
  have hroot : quantumIsingSpectralRoot A =
      Real.exp (Real.arcosh A) := by
    rw [Real.exp_arcosh hA]
    rfl
  rw [hroot, ← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring

theorem quantumIsingTrotterModeContribution_eq_spectralRoot
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) (k : Real) :
    quantumIsingTrotterModeContribution beta h L k =
      (L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
        (L : Real) * Real.arcosh
          (quantumIsingTrotterReducedParameter beta h L k) +
        2 * Real.log
          (1 + (quantumIsingSpectralRoot
            (quantumIsingTrotterReducedParameter beta h L k))⁻¹ ^ L) := by
  have hL : 0 < L := by have := (Fact.out : 2 < L); omega
  have hA : 1 ≤ quantumIsingTrotterReducedParameter beta h L k :=
    quantumIsingTrotterReducedParameter_one_le beta h L k
      hbeta.le hh.le hL hx1
  rw [quantumIsingTrotterModeContribution, if_neg hL.ne',
    quantumIsingRapidityCorrection]
  rw [quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh hA]
  ring

theorem two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    (2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L 1 1‖) / L =
      (1 / (L : Real)) * ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi) := by
  rw [two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven
    beta h L hbeta hh hx1]
  have hsum :
      (∑ k ∈ Finset.range L,
        ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
          (L : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi)) +
          2 * Real.log
            (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L))) =
      ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (quantumIsingTrotterModeContribution_eq_spectralRoot
      beta h L hbeta hh hx1 _).symm
  rw [hsum]
  ring

noncomputable def quantumIsingElevenSectorLogDensity
    (beta h : Real) (n : Nat) : Real := by
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  exact (2 * Real.log
    ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖) / (n + 3)

theorem quantumIsingElevenSectorLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingElevenSectorLogDensity beta h) atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hmid := quantumIsingTrotterModeContribution_midpoint_average_tendsto
    beta h hbeta hh
  have hxlim : Tendsto (fun L : Nat ↦ beta * h / (2 * (L : Real)))
      atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)
    convert h using 1
    funext L
    ring
  have hxlt : ∀ᶠ L : Nat in atTop, beta * h / (2 * (L : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  have hmidShift := hmid.comp (tendsto_add_atTop_nat 3)
  apply hmidShift.congr'
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hxlt] with n hx1
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  dsimp only [Function.comp_apply]
  change (1 / ((n + 3 : Nat) : Real)) *
      ∑ k ∈ Finset.range (n + 3),
        quantumIsingTrotterModeContribution beta h (n + 3)
          (2 * Real.pi * (k + (1 : Real) / 2) /
            ((n + 3 : Nat) : Real) - Real.pi) =
    quantumIsingElevenSectorLogDensity beta h n
  unfold quantumIsingElevenSectorLogDensity
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage
      beta h (n + 3) hbeta hh hx1).symm

end StatMech.FrontierA
