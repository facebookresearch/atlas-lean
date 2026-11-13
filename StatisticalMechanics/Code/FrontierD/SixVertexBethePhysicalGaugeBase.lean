/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSechFourier
import Code.FrontierD.SixVertexBetheGaugeAsymptotics





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierPhysicalDensityMap
    {c : Real} (hc : 2 < c) : C(Real, Real) :=
  ⟨sixVertexFourierPhysicalDensity c hc,
    continuous_sixVertexFourierPhysicalDensity hc⟩

theorem sixVertexWeightedFiniteDensityGauge_halfFilled_eq_tailDistance
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) :
    sixVertexWeightedFiniteDensityGauge hc
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexHalfFilledBetheRoots hc k)
        (sixVertexFourierPhysicalDensityMap hc) =
      dist (sixVertexSelectedWeightedDensityMap hc k)
        (sixVertexTailWeightedDensityLimitMap hc htail) := by
  let D := sixVertexWeightedFiniteDensityDifference hc
    (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
    (sixVertexHalfFilledBetheRoots hc k)
    (sixVertexFourierPhysicalDensityMap hc)
  let selected := sixVertexSelectedWeightedDensityMap hc k
  let tail := sixVertexTailWeightedDensityLimitMap hc htail
  have hselected (x : Real) :
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x =
        sixVertexSelectedFiniteRootDensity hc k x := by
    exact (sixVertexSelectedFiniteRootDensity_eq_halfFilled hc k x).symm
  have hD : D = selected - tail := by
    apply ContinuousMap.ext
    intro x
    dsimp only [D, selected, tail,
      sixVertexWeightedFiniteDensityDifference,
      sixVertexFourierPhysicalDensityMap,
      sixVertexSelectedWeightedDensityMap,
      ContinuousMap.sub_apply]
    rw [← sixVertexRootDensityWeight_mul_tailRootDensity_of_mem
      hc htail x.2]
    rw [sixVertexTailRootDensity_eq_fourierPhysicalDensity hc htail x.1 x.2]
    simp only [ContinuousMap.coe_mk]
    rw [hselected]
    ring
  calc
    sixVertexWeightedFiniteDensityGauge hc
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexHalfFilledBetheRoots hc k)
        (sixVertexFourierPhysicalDensityMap hc) = ‖D‖ := rfl
    _ = ‖selected - tail‖ := congrArg norm hD
    _ = dist selected tail := (dist_eq_norm _ _).symm

theorem sixVertexHalfFilledContinuationGauge_eq_tailDistance
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c₀) (k : Nat) :
    sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) =
      dist (sixVertexSelectedWeightedDensityMap (ha.trans_le hc₀.1) k)
        (sixVertexTailWeightedDensityLimitMap
          (ha.trans_le hc₀.1) htail) := by
  let hc : 2 < c₀ := ha.trans_le hc₀.1
  have hsection : sixVertexContinuumDensitySection
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) =
        sixVertexFourierPhysicalDensityMap hc := by
    ext x
    exact sixVertexFourierPhysicalDensityFamily_apply ha
      (⟨c₀, hc₀⟩, x)
  unfold sixVertexContinuationWeightedFiniteDensityGauge
  rw [hsection]
  exact sixVertexWeightedFiniteDensityGauge_halfFilled_eq_tailDistance
    hc htail k

theorem tendsto_sixVertexHalfFilledContinuationGauge_fourierPhysical
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c₀) :
    Tendsto (fun k : Nat =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k))
      atTop (nhds 0) := by
  have hmap := tendsto_sixVertexSelectedWeightedDensityMap
    (ha.trans_le hc₀.1) htail
  have hdist : Tendsto (fun k : Nat =>
      dist (sixVertexSelectedWeightedDensityMap (ha.trans_le hc₀.1) k)
        (sixVertexTailWeightedDensityLimitMap
          (ha.trans_le hc₀.1) htail)) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hmap
  apply hdist.congr'
  filter_upwards [] with k
  exact (sixVertexHalfFilledContinuationGauge_eq_tailDistance
    ha hc₀ htail k).symm

end

end StatMech.FrontierD
