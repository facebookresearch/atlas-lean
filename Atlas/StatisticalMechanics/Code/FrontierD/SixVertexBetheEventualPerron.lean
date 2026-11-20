/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFourierEvaluation

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def SixVertexEventuallyHasSymmetricBetheIdentification
    {c : Real} (hc : 2 < c) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexLambdaAlongFour c 0 k =
      sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k)

theorem sixVertexEventuallyHasSymmetricBetheIdentification_of_all
    {c : Real} (hc : 2 < c)
    (h : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc)) :
    SixVertexEventuallyHasSymmetricBetheIdentification hc :=
  Eventually.of_forall h

theorem sixVertexEventuallyHasSymmetricBetheIdentification_of_positivePhase
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
    SixVertexEventuallyHasSymmetricBetheIdentification hc :=
  sixVertexEventuallyHasSymmetricBetheIdentification_of_all hc
    (sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase
      hc hphase)



theorem sixVertexCentralWidthRate_eventuallyEq_candidateRate
    {c : Real} (hc : 2 < c)
    (hperron : SixVertexEventuallyHasSymmetricBetheIdentification hc) :
    sixVertexCentralWidthRate c =ᶠ[atTop]
      sixVertexHalfFilledBetheCandidateRate hc := by
  filter_upwards [hperron] with k hk
  unfold sixVertexCentralWidthRate sixVertexHalfFilledBetheCandidateRate
  rw [hk]



theorem sixVertexBalanced_iteratedLimit_of_eventualPerron_of_rootDensityFourier
    {c : Real} (hc : 2 < c)
    (hperron : SixVertexEventuallyHasSymmetricBetheIdentification hc)
    (hbulk : SixVertexSelectedBulkMatchesRootDensityFourier hc) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) := by
  have hbulkAsymptotic : SixVertexSelectedBulkFreeEnergyAsymptotic hc :=
    (sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier
      hc).2 hbulk
  have hbulkNorm : Tendsto (fun k ↦
      sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) :=
    (sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution hc).1
      hbulkAsymptotic
  have hcandidate : Tendsto (sixVertexHalfFilledBetheCandidateRate hc) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) :=
    (sixVertexHalfFilledBetheCandidateRate_tendsto_iff_bulkLog2 hc).2 hbulkNorm
  have hwidth : Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) :=
    hcandidate.congr'
      (sixVertexCentralWidthRate_eventuallyEq_candidateRate hc hperron).symm
  exact (sixVertexBalanced_iteratedLimit_iff_widthRate (by linarith)).2 hwidth

end

end StatMech.FrontierD
