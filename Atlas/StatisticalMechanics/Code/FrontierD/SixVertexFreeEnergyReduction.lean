/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierD.SixVertexBetheThermodynamicReduction
import Code.FrontierD.SixVertexBetheSymmetricProduct

open Filter Topology

namespace StatMech.FrontierD



def SixVertexBethePerronAsymptotics (c lam : ℝ) : Prop :=
  Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) ∧
    ∀ r : ℕ, 1 ≤ r →
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam))



def SixVertexAntiferroelectricTransferConclusion (c lam : ℝ) : Prop :=
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue lam) ∧
    ∀ r : ℕ, 1 ≤ r →
      Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : ℝ) *
          sixVertexAntiferroelectricGapRate lam)))



theorem sixVertexAntiferroelectricTransferConclusion_iff_bethePerron
    {c lam : ℝ} (hc : 0 < c) :
    SixVertexAntiferroelectricTransferConclusion c lam ↔
      SixVertexBethePerronAsymptotics c lam := by
  constructor
  · rintro ⟨hfree, hgap⟩
    refine ⟨(sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe hc).1
      hfree, ?_⟩
    intro r hr
    exact (sixVertexAntiferroelectricGapFormula_iff_logBethe hc r).1
      (hgap r hr)
  · rintro ⟨hfree, hgap⟩
    refine ⟨(sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe hc).2
      hfree, ?_⟩
    intro r hr
    exact (sixVertexAntiferroelectricGapFormula_iff_logBethe hc r).2
      (hgap r hr)


theorem sixVertexAntiferroelectricTransferConclusion_iff_canonicalBethePerron
    {c : ℝ} (hc : 2 < c) :
    SixVertexAntiferroelectricTransferConclusion c
        (sixVertexAntiferroelectricLambda c) ↔
      SixVertexBethePerronAsymptotics c
        (sixVertexAntiferroelectricLambda c) :=
  sixVertexAntiferroelectricTransferConclusion_iff_bethePerron
    (by linarith)




theorem sixVertexAntiferroelectricTransferConclusion_of_canonicalBethePerron
    {c lam : ℝ} (hc : 2 < c) (hlam : 0 < lam)
    (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2)
    (hbethe : SixVertexBethePerronAsymptotics c
      (sixVertexAntiferroelectricLambda c)) :
    SixVertexAntiferroelectricTransferConclusion c lam := by
  have hlamEq := sixVertexAntiferroelectricLambda_unique hlam hcosh
  rw [hlamEq]
  exact (sixVertexAntiferroelectricTransferConclusion_iff_canonicalBethePerron
    hc).2 hbethe

end StatMech.FrontierD
