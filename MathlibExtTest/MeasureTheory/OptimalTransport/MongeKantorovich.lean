/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.MongeKantorovich

@[expose] public section

open MeasureTheory
open MathlibExt.Analysis.OptimalTransportWanted.Analysis

namespace MathlibExtTest.MeasureTheory.OptimalTransport.MongeKantorovich

/-- Non-vacuity: an optimal coupling of `δ_0` and `δ_1` on `ℝ` for the cost `|x - y|`. -/
example : ∃ π ∈ Couplings (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)),
    ∀ π' ∈ Couplings (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)),
      kantorovichCost (fun z : ℝ × ℝ => edist z.1 z.2) π ≤
        kantorovichCost (fun z : ℝ × ℝ => edist z.1 z.2) π' :=
  monge_kantorovich_exists _ _ _ continuous_edist

/-- The product measure is in `Couplings`, through the bridge with `IsCoupling`. -/
example (μ ν : ProbabilityMeasure ℝ) :
    ((μ.prod ν : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) ∈
      Couplings (μ : Measure ℝ) (ν : Measure ℝ) :=
  (mem_couplings_iff μ ν _).2
    (MathlibExt.MeasureTheory.OptimalTransport.Wasserstein.isCoupling_prod μ ν)

end MathlibExtTest.MeasureTheory.OptimalTransport.MongeKantorovich
