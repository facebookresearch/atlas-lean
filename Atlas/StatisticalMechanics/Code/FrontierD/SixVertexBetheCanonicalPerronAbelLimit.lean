/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronFourier









open Filter Set Topology

namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexRegularizedRapidityDelta_nhdsWithin_zero
    (lam : Real) :
    Tendsto (sixVertexRegularizedRapidityDelta lam)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hden : 2 * (Real.cosh lam + 1) ≠ 0 := by
    have hcosh : 1 ≤ Real.cosh lam := Real.one_le_cosh lam
    positivity
  have hcont : ContinuousAt (sixVertexRegularizedRapidityDelta lam) 0 := by
    unfold sixVertexRegularizedRapidityDelta
      sixVertexRegularizedRapidityB
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · simpa using hden
  simpa [sixVertexRegularizedRapidityDelta,
    sixVertexRegularizedRapidityB, hden] using
      hcont.tendsto.mono_left inf_le_left

theorem tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexRegularizedRapidityRadius lam)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hdelta := tendsto_sixVertexRegularizedRapidityDelta_nhdsWithin_zero lam
  have hdeltaWithin :
      Tendsto (sixVertexRegularizedRapidityDelta lam)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 1 (Ici 1)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hdelta, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact (one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon).le
  have harcosh :
      Tendsto (fun epsilon => Real.arcosh
          (sixVertexRegularizedRapidityDelta lam epsilon))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    convert ((Real.continuousOn_arcosh 1 (by simp)).tendsto.comp
      hdeltaWithin) using 1
    simp [Real.arcosh_zero]
  simpa [sixVertexRegularizedRapidityRadius] using
    (Real.continuous_exp.continuousAt.tendsto.comp harcosh.neg)

theorem tendsto_sixVertexCanonicalPerronRapidityRadius
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexRegularizedRapidityRadius
        (sixVertexAntiferroelectricLambda c)
        (sixVertexCanonicalPerronLogEpsilon hc k))
      atTop (nhds 1) := by
  apply (tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero
    (sixVertexAntiferroelectricLambda_pos hc)).comp
  exact tendsto_nhdsWithin_iff.2 ⟨
    tendsto_sixVertexCanonicalPerronLogEpsilon hc,
    eventually_sixVertexCanonicalPerronLogEpsilon_pos hc⟩

theorem tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexRegularizedRapidityConstant lam)
      (nhdsWithin 0 (Ioi 0)) (nhds lam) := by
  let A : Real := 2 * (Real.cosh lam + 1)
  have hA : 0 < A := by
    dsimp [A]
    have hcosh : 1 ≤ Real.cosh lam := Real.one_le_cosh lam
    positivity
  have hepsilon : Tendsto (fun epsilon : Real => epsilon)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hB : Tendsto (sixVertexRegularizedRapidityB lam)
      (nhdsWithin 0 (Ioi 0)) (nhds A) := by
    simpa [sixVertexRegularizedRapidityB, A] using
      (tendsto_const_nhds.add hepsilon)
  have hlogB := hB.log hA.ne'
  have hr := tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero hlam
  have hlogR := (hr.const_mul 2).log (by norm_num)
  let q := sixVertexFreeEnergyRapidityRadius lam
  have hlogA : Tendsto (fun _ : Real => Real.log A)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.log A)) := tendsto_const_nhds
  have hlogQ : Tendsto (fun _ : Real => Real.log (2 * q))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.log (2 * q))) := tendsto_const_nhds
  have hcombined : Tendsto (fun epsilon => (1 / 2 : Real) *
      (Real.log A - Real.log (sixVertexRegularizedRapidityB lam epsilon) -
        Real.log (2 * q) +
        Real.log (2 * sixVertexRegularizedRapidityRadius lam epsilon)))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / 2 : Real) *
        (Real.log A - Real.log A - Real.log (2 * q) + Real.log (2 * 1)))) :=
    (((hlogA.sub hlogB).sub hlogQ).add hlogR).const_mul (1 / 2 : Real)
  have hvalue : (1 / 2 : Real) *
      (Real.log A - Real.log A - Real.log (2 * q) + Real.log (2 * 1)) =
      lam := by
    dsimp [A]
    have hq : sixVertexFreeEnergyRapidityRadius lam ≠ 0 := by
      unfold sixVertexFreeEnergyRapidityRadius
      positivity
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hq]
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (by norm_num : (1 : Real) ≠ 0)]
    simp [sixVertexFreeEnergyRapidityRadius, Real.log_exp]
  simpa only [sixVertexRegularizedRapidityConstant, q, hvalue] using hcombined

theorem tendsto_sixVertexCanonicalPerronRapidityConstant
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexRegularizedRapidityConstant
        (sixVertexAntiferroelectricLambda c)
        (sixVertexCanonicalPerronLogEpsilon hc k))
      atTop (nhds (sixVertexAntiferroelectricLambda c)) := by
  apply (tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero
    (sixVertexAntiferroelectricLambda_pos hc)).comp
  exact tendsto_nhdsWithin_iff.2 ⟨
    tendsto_sixVertexCanonicalPerronLogEpsilon hc,
    eventually_sixVertexCanonicalPerronLogEpsilon_pos hc⟩

end

end StatMech.FrontierD
