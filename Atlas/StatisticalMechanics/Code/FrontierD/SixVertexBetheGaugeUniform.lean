/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSechFourier
import Code.FrontierD.SixVertexBetheGaugeAsymptotics
import Code.FrontierD.SixVertexBethePhysicalGaugeBase





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexAnisotropyMagnitude_Icc
    {a b : Real} :
    Continuous (fun t : Set.Icc a b =>
      sixVertexAnisotropyMagnitude t.1) := by
  unfold sixVertexAnisotropyMagnitude sixVertexDelta
  fun_prop

theorem continuous_sixVertexRootDensityScale_Icc
    {a b : Real} :
    Continuous (fun t : Set.Icc a b => sixVertexRootDensityScale t.1) := by
  unfold sixVertexRootDensityScale
  exact Real.continuous_sqrt.comp
    (((continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)).pow 2).sub
      continuous_const)

theorem continuous_sixVertexRootDensityWeightFloor_Icc
    {a b : Real} (ha : 2 < a) :
    Continuous (fun t : Set.Icc a b =>
      (sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) := by
  apply ((continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)).sub
    continuous_const).div continuous_sixVertexRootDensityScale_Icc
  intro t
  exact (sixVertexRootDensityScale_pos (ha.trans_le t.2.1)).ne'

theorem continuous_sixVertexRootDensityContractionRate_Icc
    {a b : Real} (ha : 2 < a) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexRootDensityContractionRate t.1) := by
  have hd := continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)
  have hs := continuous_sixVertexRootDensityScale_Icc (a := a) (b := b)
  have hfloor : Continuous (fun t : Set.Icc a b =>
      sixVertexRootDensityKernelFloor t.1) := by
    unfold sixVertexRootDensityKernelFloor
    dsimp only
    apply (continuous_const.mul hd |>.mul ((hd.sub continuous_const).pow 2)).div
      (hs.mul (continuous_const.mul ((hd.add continuous_const).pow 2) |>.add
        continuous_const))
    intro t
    have hpoly : 0 < 4 * (sixVertexAnisotropyMagnitude t.1 + 1) ^ 2 + 4 := by
      nlinarith [sq_nonneg (sixVertexAnisotropyMagnitude t.1 + 1)]
    exact mul_ne_zero (sixVertexRootDensityScale_pos
      (ha.trans_le t.2.1)).ne' hpoly.ne'
  unfold sixVertexRootDensityContractionRate
  apply continuous_const.sub
  apply (hfloor.mul hs).div (hd.add continuous_const)
  intro t
  change sixVertexAnisotropyMagnitude t.1 + 1 ≠ 0
  linarith [one_lt_sixVertexAnisotropyMagnitude (ha.trans_le t.2.1)]

theorem continuous_sixVertexSymmetricScatteringBoundaryBound_Icc
    {a b : Real} (ha : 2 < a) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexSymmetricScatteringBoundaryBound t.1) := by
  have hd := continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)
  have hs := continuous_sixVertexRootDensityScale_Icc (a := a) (b := b)
  unfold sixVertexSymmetricScatteringBoundaryBound
  apply continuous_const.mul
  apply Real.continuous_arctan.comp
  apply continuous_const.div
    (continuous_const.mul hd |>.mul hs)
  intro t
  have hdpos : 0 < sixVertexAnisotropyMagnitude t.1 := by
    linarith [one_lt_sixVertexAnisotropyMagnitude (ha.trans_le t.2.1)]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hdpos.ne')
    (sixVertexRootDensityScale_pos (ha.trans_le t.2.1)).ne'

theorem continuous_sixVertexFiniteDensityErrorOne_Icc
    {a b lower : Real} (ha : 2 < a) (_hlower : 0 < lower) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexFiniteDensityContinuumErrorOfLower t.1 1 lower) := by
  have hd := continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)
  have hs := continuous_sixVertexRootDensityScale_Icc (a := a) (b := b)
  have hd1 : Continuous (fun t : Set.Icc a b =>
      sixVertexAnisotropyMagnitude t.1 - 1) :=
    hd.sub continuous_const
  have hd1ne : ∀ t : Set.Icc a b,
      sixVertexAnisotropyMagnitude t.1 - 1 ≠ 0 := by
    intro t
    linarith [one_lt_sixVertexAnisotropyMagnitude (ha.trans_le t.2.1)]
  have hQ : Continuous (fun t : Set.Icc a b =>
      4 * (sixVertexAnisotropyMagnitude t.1 - 1) ^ 2) :=
    continuous_const.mul (hd1.pow 2)
  have hQne : ∀ t : Set.Icc a b,
      4 * (sixVertexAnisotropyMagnitude t.1 - 1) ^ 2 ≠ 0 := by
    intro t
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hd1ne t))
  have hkernel : Continuous (fun t : Set.Icc a b =>
      sixVertexRootDensityKernelLipschitzBound t.1) := by
    unfold sixVertexRootDensityKernelLipschitzBound
    dsimp only
    apply ((continuous_const.mul hd |>.mul (hd.add continuous_const)).div hs
      (fun t => (sixVertexRootDensityScale_pos
        (ha.trans_le t.2.1)).ne')).mul
    apply (continuous_const.div hQ hQne).add
    apply ((hd.add continuous_const).mul
      (continuous_const.mul (hd.add continuous_const) |>.add
        continuous_const)).div (hQ.pow 2)
    intro t
    exact pow_ne_zero 2 (hQne t)
  have huniform : Continuous (fun t : Set.Icc a b =>
      sixVertexFiniteRootDensityUniformBound t.1) := by
    unfold sixVertexFiniteRootDensityUniformBound
    apply (continuous_const.add (hd.div hd1 hd1ne)).div continuous_const
    intro _
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  unfold sixVertexFiniteDensityContinuumErrorOfLower
  apply ((((hkernel.mul huniform).mul continuous_const).mul
    continuous_const).div continuous_const)
  intro _
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

theorem continuous_sixVertexJacobianTotalErrorOne_Icc
    {a b lower : Real} (ha : 2 < a) (_hlower : 0 < lower) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexSymmetricJacobianTotalErrorOfLower t.1 1 lower) := by
  have hd := continuous_sixVertexAnisotropyMagnitude_Icc (a := a) (b := b)
  have hd1 : Continuous (fun t : Set.Icc a b =>
      sixVertexAnisotropyMagnitude t.1 - 1) :=
    hd.sub continuous_const
  have hd1ne : ∀ t : Set.Icc a b,
      sixVertexAnisotropyMagnitude t.1 - 1 ≠ 0 := by
    intro t
    linarith [one_lt_sixVertexAnisotropyMagnitude (ha.trans_le t.2.1)]
  have htheta : Continuous (fun t : Set.Icc a b =>
      sixVertexThetaLeftKernelLipschitzBound t.1) := by
    unfold sixVertexThetaLeftKernelLipschitzBound
    dsimp only
    apply (continuous_const.mul hd |>.mul (hd.add continuous_const) |>.mul
      (continuous_const.mul (hd.add continuous_const) |>.add
        continuous_const)).div
      (continuous_const.mul (hd1.pow 4))
    intro t
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 (hd1ne t))
  have hfinite : Continuous (fun t : Set.Icc a b =>
      (sixVertexFiniteRootDensityLipschitzConstant t.1 : Real)) := by
    unfold sixVertexFiniteRootDensityLipschitzConstant
    exact NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
      (htheta.div continuous_const (fun _ =>
        mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  have hscatter : Continuous (fun t : Set.Icc a b =>
      (sixVertexSymmetricScatteringLipschitzConstant t.1 : Real)) := by
    unfold sixVertexSymmetricScatteringLipschitzConstant
    exact NNReal.continuous_coe.comp
      (continuous_const.mul (continuous_real_toNNReal.comp htheta))
  have hratio : Continuous (fun t : Set.Icc a b =>
      sixVertexAnisotropyMagnitude t.1 /
        (sixVertexAnisotropyMagnitude t.1 - 1)) :=
    hd.div hd1 hd1ne
  have hdiag : Continuous (fun t : Set.Icc a b =>
      sixVertexSymmetricJacobianDiagonalErrorOfLower t.1 1 lower) := by
    unfold sixVertexSymmetricJacobianDiagonalErrorOfLower
    exact ((((continuous_const.mul continuous_const).mul hfinite).mul
      (continuous_const.pow 2)).add
        ((continuous_const.mul hratio).mul continuous_const))
  have hoff : Continuous (fun t : Set.Icc a b =>
      sixVertexSymmetricJacobianOffDiagonalErrorOfLower t.1 1 lower) := by
    unfold sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    exact (((continuous_const.mul hscatter).add
      (continuous_const.mul hratio)).mul continuous_const)
  unfold sixVertexSymmetricJacobianTotalErrorOfLower
  exact hdiag.add hoff

theorem sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div
    (c lower : Real) {N : Nat} (hN : 0 < N) :
    sixVertexFiniteDensityContinuumErrorOfLower c N lower =
      sixVertexFiniteDensityContinuumErrorOfLower c 1 lower / N := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexFiniteDensityContinuumErrorOfLower
  field_simp [hN0]
  ring

theorem sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div
    (c lower : Real) {N : Nat} (hN : 0 < N) :
    sixVertexSymmetricJacobianTotalErrorOfLower c N lower =
      sixVertexSymmetricJacobianTotalErrorOfLower c 1 lower / N := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexSymmetricJacobianTotalErrorOfLower
    sixVertexSymmetricJacobianDiagonalErrorOfLower
    sixVertexSymmetricJacobianOffDiagonalErrorOfLower
  field_simp [hN0]
  ring



theorem exists_uniform_sixVertexDensityGaugeNumericalMargins
    {a b rhoLower : Real} (ha : 2 < a) (hab : a ≤ b)
    (hrhoLower : 0 < rhoLower) :
    ∃ inner outer : Real,
      inner < outer ∧
      (∀ t : Set.Icc a b, outer ≤ rhoLower *
        ((sixVertexAnisotropyMagnitude t.1 - 1) /
          sixVertexRootDensityScale t.1) / 2) ∧
      ∀ᶠ N : Nat in atTop, ∀ t : Set.Icc a b,
        sixVertexRootDensityContractionRate t.1 * outer +
            sixVertexFiniteDensityContinuumErrorOfLower
              t.1 N (rhoLower / 2) ≤ inner ∧
          sixVertexSymmetricScatteringBoundaryBound t.1 +
              2 * sixVertexSymmetricJacobianTotalErrorOfLower
                t.1 N (rhoLower / 2) < 2 * Real.pi := by
  let T := Set.Icc a b
  let t₀ : T := ⟨a, le_rfl, hab⟩
  let w : T → Real := fun t =>
    (sixVertexAnisotropyMagnitude t.1 - 1) /
      sixVertexRootDensityScale t.1
  let rate : T → Real := fun t => sixVertexRootDensityContractionRate t.1
  let boundary : T → Real := fun t =>
    sixVertexSymmetricScatteringBoundaryBound t.1
  let densityError : T → Real := fun t =>
    sixVertexFiniteDensityContinuumErrorOfLower t.1 1 (rhoLower / 2)
  let jacobianError : T → Real := fun t =>
    sixVertexSymmetricJacobianTotalErrorOfLower t.1 1 (rhoLower / 2)
  have hw : Continuous w :=
    continuous_sixVertexRootDensityWeightFloor_Icc ha
  have hrate : Continuous rate :=
    continuous_sixVertexRootDensityContractionRate_Icc ha
  have hboundary : Continuous boundary :=
    continuous_sixVertexSymmetricScatteringBoundaryBound_Icc ha
  have hdensity : Continuous densityError :=
    continuous_sixVertexFiniteDensityErrorOne_Icc ha (by positivity)
  have hjacobian : Continuous jacobianError :=
    continuous_sixVertexJacobianTotalErrorOne_Icc ha (by positivity)
  obtain ⟨tw, _, htw⟩ := isCompact_univ.exists_isMinOn
    ⟨t₀, Set.mem_univ _⟩ hw.continuousOn
  obtain ⟨tr, _, htr⟩ := isCompact_univ.exists_isMaxOn
    ⟨t₀, Set.mem_univ _⟩ hrate.continuousOn
  obtain ⟨tb, _, htb⟩ := isCompact_univ.exists_isMaxOn
    ⟨t₀, Set.mem_univ _⟩ hboundary.continuousOn
  obtain ⟨te, _, hte⟩ := isCompact_univ.exists_isMaxOn
    ⟨t₀, Set.mem_univ _⟩ hdensity.continuousOn
  obtain ⟨tj, _, htj⟩ := isCompact_univ.exists_isMaxOn
    ⟨t₀, Set.mem_univ _⟩ hjacobian.continuousOn
  have hwpos : 0 < w tw := by
    dsimp [w]
    exact div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude
        (ha.trans_le tw.2.1)))
      (sixVertexRootDensityScale_pos (ha.trans_le tw.2.1))
  have hrange : rate tr < 1 :=
    (sixVertexRootDensityContractionRate_mem_Ico
      (ha.trans_le tr.2.1)).2
  have hboundaryRange : boundary tb < 2 * Real.pi :=
    sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
  let outer := rhoLower * w tw / 4
  let inner := ((rate tr + 1) / 2) * outer
  have houterPos : 0 < outer := by
    dsimp [outer]
    positivity
  have hinnerOuter : inner < outer := by
    dsimp [inner]
    nlinarith
  have houter : ∀ t : T, outer ≤ rhoLower * w t / 2 := by
    intro t
    have hmin := htw (Set.mem_univ t)
    change w tw ≤ w t at hmin
    have hwt : 0 < w t := hwpos.trans_le hmin
    dsimp [outer]
    calc
      rhoLower * w tw / 4 ≤ rhoLower * w t / 4 := by gcongr
      _ ≤ rhoLower * w t / 2 := by nlinarith [mul_pos hrhoLower hwt]
  have hdensityTendsto : Tendsto (fun N : Nat => densityError te / N)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hjacobianTendsto : Tendsto (fun N : Nat => jacobianError tj / N)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hrateGap : 0 < inner - rate tr * outer := by
    dsimp [inner]
    nlinarith
  have hboundaryGap : 0 < (2 * Real.pi - boundary tb) / 2 := by
    linarith
  have hdensityEventually : ∀ᶠ N : Nat in atTop,
      densityError te / N < inner - rate tr * outer :=
    hdensityTendsto.eventually (Iio_mem_nhds hrateGap)
  have hjacobianEventually : ∀ᶠ N : Nat in atTop,
      jacobianError tj / N < (2 * Real.pi - boundary tb) / 2 :=
    hjacobianTendsto.eventually (Iio_mem_nhds hboundaryGap)
  refine ⟨inner, outer, hinnerOuter, ?_, ?_⟩
  · intro t
    simpa only [w] using houter t
  · filter_upwards [eventually_gt_atTop 0, hdensityEventually,
      hjacobianEventually] with N hN hE hJ
    intro t
    have hrateLe : rate t ≤ rate tr := htr (Set.mem_univ t)
    have hboundaryLe : boundary t ≤ boundary tb := htb (Set.mem_univ t)
    have hdensityLe : densityError t ≤ densityError te := hte (Set.mem_univ t)
    have hjacobianLe : jacobianError t ≤ jacobianError tj := htj (Set.mem_univ t)
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hdensityDiv : densityError t / N ≤ densityError te / N := by
      exact div_le_div_of_nonneg_right hdensityLe hNreal.le
    have hjacobianDiv : jacobianError t / N ≤ jacobianError tj / N := by
      exact div_le_div_of_nonneg_right hjacobianLe hNreal.le
    rw [sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div
      t.1 (rhoLower / 2) hN]
    rw [sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div
      t.1 (rhoLower / 2) hN]
    constructor
    · dsimp [rate] at hrateLe
      dsimp [densityError] at hdensityDiv
      nlinarith
    · dsimp [boundary] at hboundaryLe
      dsimp [jacobianError] at hjacobianDiv
      nlinarith

theorem tendsto_sixVertexHalfFilledContinuationGauge
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (fun k =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexHalfFilledBetheContinuationPoint ha hc k))
      atTop (nhds 0) := by
  exact tendsto_sixVertexHalfFilledContinuationGauge_fourierPhysical
    ha hc htail

theorem exists_uniform_sixVertexDensityGaugeMargins_fourWidth
    {a b rhoLower : Real} (ha : 2 < a) (hab : a ≤ b)
    (hrhoLower : 0 < rhoLower) :
    ∃ inner outer : Real,
      inner < outer ∧
      (∀ t : Set.Icc a b, outer ≤ rhoLower *
        ((sixVertexAnisotropyMagnitude t.1 - 1) /
          sixVertexRootDensityScale t.1) / 2) ∧
      ∀ᶠ k : Nat in atTop, ∀ t : Set.Icc a b,
        sixVertexRootDensityContractionRate t.1 * outer +
            sixVertexFiniteDensityContinuumErrorOfLower t.1
              (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner ∧
          sixVertexSymmetricScatteringBoundaryBound t.1 +
              2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1
                (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi := by
  obtain ⟨inner, outer, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins ha hab hrhoLower
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  exact ⟨inner, outer, hio, houter, hwidth.eventually hmargins⟩

end

end StatMech.FrontierD
