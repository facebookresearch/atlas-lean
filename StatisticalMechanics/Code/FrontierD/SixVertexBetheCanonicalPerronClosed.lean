/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit








open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexCanonicalPerronRegularizedFourierValue
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexRegularizedRapidityFourierValue
        (sixVertexAntiferroelectricLambda c)
        (sixVertexCanonicalPerronLogEpsilon hc k)) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) :=
  tendsto_sixVertexRegularizedRapidityFourierValue
    (tendsto_sixVertexCanonicalPerronLogEpsilon hc)
    (eventually_sixVertexCanonicalPerronLogEpsilon_pos hc)
    (sixVertexAntiferroelectricLambda_pos hc)

theorem tendsto_sixVertexCanonicalPerronRegularizedIntegral
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalPerronRegularizedIntegral hc) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  apply (tendsto_sixVertexCanonicalPerronRegularizedFourierValue hc).congr'
  filter_upwards [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
    with k hk
  unfold sixVertexCanonicalPerronRegularizedIntegral
  exact (sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue hc hk).symm

theorem tendsto_sixVertexCanonicalPerronRootAverage_freeEnergy
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexSymmetricBetheRootAverage c
        (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  have hsub :=
    tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral hc
  have hint := tendsto_sixVertexCanonicalPerronRegularizedIntegral hc
  convert hsub.add hint using 1
  · funext k
    ring
  · ring

theorem tendsto_sixVertexCanonicalDensityPerronEmpiricalLog_freeEnergy
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexBetheLogObservable c)) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  apply (tendsto_sixVertexCanonicalPerronRootAverage_freeEnergy hc).congr'
  filter_upwards [] with k
  exact (sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage
    hc k).symm

theorem tendsto_sixVertexCentralWidthRate_canonicalPerron
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) :=
  (sixVertexCentralWidthRate_tendsto_iff_canonicalDensityEmpiricalLog hc).2
    (tendsto_sixVertexCanonicalDensityPerronEmpiricalLog_freeEnergy hc)



theorem sixVertexBalanced_iteratedLimit_of_canonicalPerron
    {c : Real} (hc : 2 < c) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) :=
  (sixVertexBalanced_iteratedLimit_iff_widthRate (by linarith)).2
    (tendsto_sixVertexCentralWidthRate_canonicalPerron hc)

end

end StatMech.FrontierD
