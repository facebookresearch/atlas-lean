/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Kantorovich duality for lower semicontinuous costs: wanted

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.10(i).
The compact, continuous-cost case is proved in
`MathlibExt.MeasureTheory.OptimalTransport.Kantorovich`.
A complete separable metric space with its Borel σ-algebra stands for Villani's Polish space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost)

namespace MathlibExt.MeasureTheory.KantorovichDualityWanted

/-- **Kantorovich duality for lower semicontinuous costs.** Let `X` and `Y` be Polish spaces
with Borel probability measures `μ` and `ν`, and let `c : X × Y → [0, ∞]` be lower
semicontinuous. Then the minimal transport cost `inf_π ∫ c dπ` over couplings `π` of `μ` and `ν`
equals the supremum of `∫ φ dν - ∫ ψ dμ` over bounded continuous `ψ` on `X` and `φ` on `Y` with
`φ(y) - ψ(x) ≤ c(x, y)` for all `x, y` (C. Villani, *Optimal Transport: Old and New*, Springer
2009, Theorem 5.10(i), first equality, in the case `a = b = 0` of the lower bound
`c ≥ a + b`). The supremum is nonnegative (take `ψ = φ = 0`), so it is stated through
`ENNReal.ofReal`. -/
theorem_wanted kantorovich_duality_lsc {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞)
    (hc : LowerSemicontinuous c) :
    ⨅ (π : ProbabilityMeasure (X × Y)) (_ : IsCoupling μ ν π), ∫⁻ z, c z ∂(π : Measure (X × Y)) =
      ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
        (_ : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ c (x, y)),
        ENNReal.ofReal (∫ y, φ y ∂(ν : Measure Y) - ∫ x, ψ x ∂(μ : Measure X))

end MathlibExt.MeasureTheory.KantorovichDualityWanted
