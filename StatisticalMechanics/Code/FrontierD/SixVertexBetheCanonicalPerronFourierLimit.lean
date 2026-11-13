/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronFourier
import Code.FrontierD.SixVertexBetheCanonicalPerronAbelLimit
import Mathlib.Analysis.Normed.Group.Tannery









open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexRegularizedRapidityDelta
    {ι : Type*} {l : Filter ι} {epsilon : ι → Real} {lam : Real}
    (hepsilon : Tendsto epsilon l (nhds 0)) :
    Tendsto (fun i => sixVertexRegularizedRapidityDelta lam (epsilon i))
      l (nhds 1) := by
  have hnum : Tendsto (fun i =>
      2 * (Real.cosh lam + 1) + epsilon i * Real.cosh lam) l
      (nhds (2 * (Real.cosh lam + 1))) := by
    simpa using tendsto_const_nhds.add (hepsilon.mul_const (Real.cosh lam))
  have hden : Tendsto (fun i =>
      sixVertexRegularizedRapidityB lam (epsilon i)) l
      (nhds (2 * (Real.cosh lam + 1))) := by
    unfold sixVertexRegularizedRapidityB
    simpa using tendsto_const_nhds.add hepsilon
  have hne : 2 * (Real.cosh lam + 1) ≠ 0 := by positivity
  have hdiv := hnum.div hden hne
  simpa [sixVertexRegularizedRapidityDelta, div_self hne] using hdiv

theorem tendsto_sixVertexRegularizedRapidityRadius
    {ι : Type*} {l : Filter ι} {epsilon : ι → Real} {lam : Real}
    (hepsilon : Tendsto epsilon l (nhds 0))
    (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i) (hlam : 0 < lam) :
    Tendsto (fun i => sixVertexRegularizedRapidityRadius lam (epsilon i))
      l (nhds 1) := by
  have hdelta := tendsto_sixVertexRegularizedRapidityDelta
    (lam := lam) hepsilon
  have hdeltaMem : ∀ᶠ i in l,
      sixVertexRegularizedRapidityDelta lam (epsilon i) ∈ Set.Ici 1 := by
    filter_upwards [hepsilonPos] with i hi
    exact (one_lt_sixVertexRegularizedRapidityDelta hlam hi).le
  have hdeltaWithin : Tendsto
      (fun i => sixVertexRegularizedRapidityDelta lam (epsilon i)) l
      (nhdsWithin 1 (Set.Ici 1)) :=
    tendsto_nhdsWithin_iff.2 ⟨hdelta, hdeltaMem⟩
  have harcosh : Tendsto (fun i => Real.arcosh
      (sixVertexRegularizedRapidityDelta lam (epsilon i))) l (nhds 0) := by
    have hcont := Real.continuousOn_arcosh.continuousWithinAt
      (show (1 : Real) ∈ Set.Ici 1 by simp)
    simpa using hcont.tendsto.comp hdeltaWithin
  unfold sixVertexRegularizedRapidityRadius
  simpa using (Real.continuous_exp.continuousAt.tendsto.comp harcosh.neg)

theorem tendsto_sixVertexRegularizedRapidityConstant
    {ι : Type*} {l : Filter ι} {epsilon : ι → Real} {lam : Real}
    (hepsilon : Tendsto epsilon l (nhds 0))
    (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i) (hlam : 0 < lam) :
    Tendsto (fun i => sixVertexRegularizedRapidityConstant lam (epsilon i))
      l (nhds lam) := by
  apply (tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero
    hlam).comp
  exact tendsto_nhdsWithin_iff.2 ⟨hepsilon, hepsilonPos⟩

theorem tendsto_sixVertexAbelRootDensitySeries
    {ι : Type*} {l : Filter ι} {r : ι → Real} {lam : Real}
    (hlam : 0 < lam) (hr : Tendsto r l (nhds 1))
    (hrMem : ∀ᶠ i in l, r i ∈ Set.Icc 0 1) :
    Tendsto (fun i => ∑' n : Nat,
      sixVertexAbelRootDensitySeriesTerm lam (r i) n) l
      (nhds (∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam 1 n)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_sixVertexFourierRootDensityMajorant hlam)
  · intro n
    unfold sixVertexAbelRootDensitySeriesTerm
    exact ((hr.pow (n + 1)).div_const
      ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam)))
  · filter_upwards [hrMem] with i hi
    intro n
    have hrpow : |r i| ^ (n + 1) ≤ 1 := by
      rw [abs_of_nonneg hi.1]
      simpa using pow_le_one₀ hi.1 hi.2
    have hm : (1 : Real) ≤ n + 1 := by norm_num
    have hcosh : 0 < Real.cosh ((n + 1 : Real) * lam) := Real.cosh_pos _
    have hsech := norm_sixVertexFourierRootDensityTerm_le hlam n 0
    simp only [sixVertexFourierRootDensityTerm, mul_zero, Real.cos_zero,
      one_div] at hsech
    rw [norm_inv, Real.norm_of_nonneg hcosh.le] at hsech
    rw [sixVertexAbelRootDensitySeriesTerm, Real.norm_eq_abs,
      abs_div, abs_pow,
      abs_of_pos (mul_pos (by positivity) hcosh)]
    calc
      |r i| ^ (n + 1) /
          ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))
        ≤ 1 / Real.cosh ((n + 1 : Real) * lam) := by
          rw [div_le_iff₀ (mul_pos (by positivity) hcosh)]
          field_simp [hcosh.ne']
          exact hrpow.trans hm
      _ ≤ sixVertexFourierRootDensityMajorant lam n := by
        simpa [div_eq_mul_inv] using hsech

theorem summable_sixVertexAbelRootDensitySeriesTerm_one
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexAbelRootDensitySeriesTerm lam 1) := by
  apply (summable_sixVertexFourierRootDensityMajorant hlam).of_norm_bounded
  intro n
  have hm : (1 : Real) <= n + 1 := by norm_num
  have hcosh : 0 < Real.cosh ((n + 1 : Real) * lam) := Real.cosh_pos _
  have hsech := norm_sixVertexFourierRootDensityTerm_le hlam n 0
  simp only [sixVertexFourierRootDensityTerm, mul_zero, Real.cos_zero,
    one_div] at hsech
  rw [norm_inv, Real.norm_of_nonneg hcosh.le] at hsech
  rw [sixVertexAbelRootDensitySeriesTerm, one_pow, Real.norm_eq_abs,
    abs_div, abs_one, abs_of_pos (mul_pos (by positivity) hcosh)]
  calc
    1 / ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam)) <=
        1 / Real.cosh ((n + 1 : Real) * lam) := by
      rw [div_le_iff₀ (mul_pos (by positivity) hcosh)]
      field_simp [hcosh.ne']
      exact hm
    _ <= sixVertexFourierRootDensityMajorant lam n := by
      simpa [div_eq_mul_inv] using hsech

theorem sixVertexAbelRootDensitySeriesTerm_one_sub_radius_eq
    {lam : Real} (n : Nat) :
    sixVertexAbelRootDensitySeriesTerm lam 1 n -
        sixVertexAbelRootDensitySeriesTerm lam
          (sixVertexFreeEnergyRapidityRadius lam) n =
      2 * sixVertexFreeEnergySeriesTerm lam n := by
  rw [← sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm lam n]
  unfold sixVertexAbelRootDensitySeriesTerm
    sixVertexFreeEnergyRapidityRadius
    sixVertexFreeEnergyPairedFourierTerm
    sixVertexFreeEnergyKernelFourierCoeff
    sixVertexRootDensityFourierCoeff
  rw [show Real.exp (-2 * lam) ^ (n + 1) =
      Real.exp (-2 * (n + 1 : Real) * lam) by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring]
  field_simp [(Real.cosh_pos ((n + 1 : Real) * lam)).ne']
  <;> ring

theorem tendsto_sixVertexRegularizedRapidityFourierValue
    {ι : Type*} {l : Filter ι} {epsilon : ι → Real} {lam : Real}
    (hepsilon : Tendsto epsilon l (nhds 0))
    (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i) (hlam : 0 < lam) :
    Tendsto (fun i => sixVertexRegularizedRapidityFourierValue lam (epsilon i))
      l (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r : ι → Real := fun i =>
    sixVertexRegularizedRapidityRadius lam (epsilon i)
  have hr := tendsto_sixVertexRegularizedRapidityRadius
    hepsilon hepsilonPos hlam
  have hrMem : ∀ᶠ i in l, r i ∈ Set.Icc 0 1 := by
    filter_upwards [hepsilonPos] with i hi
    exact ⟨(sixVertexRegularizedRapidityRadius_mem_Ioo hlam hi).1.le,
      (sixVertexRegularizedRapidityRadius_mem_Ioo hlam hi).2.le⟩
  have hseries := tendsto_sixVertexAbelRootDensitySeries hlam hr hrMem
  have hconstant := (tendsto_sixVertexRegularizedRapidityConstant
    hepsilon hepsilonPos hlam).div_const 2
  have hvalue := (hconstant.add (hseries.const_mul (1 / 2 : Real))).sub_const
    ((1 / 2 : Real) * ∑' n : Nat,
      sixVertexAbelRootDensitySeriesTerm lam q n)
  have hqMem := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hqAbs : |q| < 1 := by
    rw [abs_of_pos hqMem.1]
    exact hqMem.2
  have hQ := summable_sixVertexAbelRootDensitySeriesTerm
    (lam := lam) hqAbs
  have hvalue' : Tendsto
      (fun i => sixVertexRegularizedRapidityFourierValue lam (epsilon i)) l
      (nhds (lam / 2 + (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n))) := by
    apply hvalue.congr'
    filter_upwards [hepsilonPos] with i hi
    have hri := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hi
    have hriAbs :
        |sixVertexRegularizedRapidityRadius lam (epsilon i)| < 1 := by
      rw [abs_of_pos hri.1]
      exact hri.2
    have hRi := summable_sixVertexAbelRootDensitySeriesTerm
      (lam := lam) hriAbs
    unfold sixVertexRegularizedRapidityFourierValue
    dsimp only [q, r]
    rw [hRi.tsum_sub hQ]
    ring
  have hOne := summable_sixVertexAbelRootDensitySeriesTerm_one hlam
  have hdiff :
      (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) =
        ∑' n : Nat, 2 * sixVertexFreeEnergySeriesTerm lam n := by
    rw [← hOne.tsum_sub hQ]
    apply tsum_congr
    intro n
    dsimp only [q]
    exact sixVertexAbelRootDensitySeriesTerm_one_sub_radius_eq n
  have hseriesValue :
      (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) =
        sixVertexFreeEnergySeries lam := by
    rw [show (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) =
        (1 / 2 : Real) *
          ((∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
            ∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) by ring,
      hdiff, tsum_mul_left]
    unfold sixVertexFreeEnergySeries
    ring
  unfold sixVertexAntiferroelectricFreeEnergyValue
  have hlimitEq :
      lam / 2 + (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) =
      lam / 2 + sixVertexFreeEnergySeries lam := by
    rw [show lam / 2 + (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) =
      lam / 2 + ((1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam 1 n) -
        (1 / 2 : Real) *
          (∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n)) by ring,
      hseriesValue]
  rw [← hlimitEq]
  exact hvalue'



theorem tendsto_sixVertexCanonicalPerronRegularizedIntegral_fourierValue
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalPerronRegularizedIntegral hc) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  have hvalue := tendsto_sixVertexRegularizedRapidityFourierValue
    (tendsto_sixVertexCanonicalPerronLogEpsilon hc)
    (eventually_sixVertexCanonicalPerronLogEpsilon_pos hc)
    (sixVertexAntiferroelectricLambda_pos hc)
  apply hvalue.congr'
  filter_upwards [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
      with k hk
  unfold sixVertexCanonicalPerronRegularizedIntegral
  exact (sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue hc hk).symm



theorem tendsto_sixVertexCanonicalPerronRootAverage_fourierValue
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  have herror :=
    tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral hc
  have hintegral :=
    tendsto_sixVertexCanonicalPerronRegularizedIntegral_fourierValue hc
  have hsum := herror.add hintegral
  convert hsum using 1
  · funext k
    ring
  · ring



theorem tendsto_sixVertexCentralWidthRate_fourierValue
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  have hrootAbstract :=
    tendsto_sixVertexCanonicalDensityPerronRootAverage hc
  have hrootExplicit :=
    tendsto_sixVertexCanonicalPerronRootAverage_fourierValue hc
  have hvalue : sixVertexCanonicalDensityPerronRootAverageLimit hc =
      sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c) :=
    tendsto_nhds_unique hrootAbstract hrootExplicit
  simpa [hvalue] using
    (tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit hc)

end

end StatMech.FrontierD
