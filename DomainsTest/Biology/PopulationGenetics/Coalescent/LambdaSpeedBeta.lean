/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaSpeedBeta

/-!
# Tests for the Beta-coalescent Laplace-exponent asymptotic

The examples restate the pushforward identification for `betaLambda`, the
asymptotic under a pushforward hypothesis, and the named Beta-coalescent form.
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval Real ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSpeedBeta

example (α : ℝ) :
    (MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent.betaLambda α).map ((↑) : I → ℝ) =
      betaMeasure (2 - α) α :=
  map_val_betaLambda α

example {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (Λ : Measure I) [IsFiniteMeasure Λ]
    (hΛ : Λ.map ((↑) : I → ℝ) = betaMeasure (2 - α) α) :
    Tendsto (fun q => psi Λ q / q ^ α) atTop (𝓝 (Gamma α * α * (α - 1))⁻¹) :=
  tendsto_psi_div_rpow_of_map_val_eq_betaMeasure hα1 hα2 Λ hΛ

example {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    [IsFiniteMeasure (MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent.betaLambda α)] :
    Tendsto
      (fun q => psi (MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent.betaLambda α) q /
        q ^ α) atTop (𝓝 (Gamma α * α * (α - 1))⁻¹) :=
  tendsto_psi_div_rpow_betaLambda hα1 hα2

#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.map_val_betaLambda
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.tendsto_psi_div_rpow_of_map_val_eq_betaMeasure
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.tendsto_psi_div_rpow_betaLambda

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSpeedBeta
