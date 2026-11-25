/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Brenier's theorem: wanted

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 9.4
(Monge problem for quadratic cost), for an absolutely continuous source measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost)

namespace MathlibExt.MeasureTheory.BrenierWanted

/-- **Brenier's theorem** (absolutely continuous source). Let `μ, ν` be probability measures on
`ℝⁿ` with finite second moments, `μ` absolutely continuous with respect to Lebesgue measure.
For the quadratic cost `|x - y|²` there is a measurable map `T` such that the coupling
`π_T = (id, T)_# μ` of `μ` and `ν` is optimal, every optimal coupling equals `π_T`, and `T` is
`μ`-almost everywhere the gradient of a convex function `ψ`: there is an open convex set `U` of
full `μ`-measure on which `ψ` is convex, with `∇ψ(x) = T x` for `μ`-almost every `x`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 9.4, in the absolutely
continuous case named in its statement; there the optimal coupling is characterized by
`y ∈ ∂ψ(x)` for a lower semicontinuous convex `ψ : ℝⁿ → ℝ ∪ {+∞}`. For `μ` absolutely
continuous, `μ`-almost every `x` lies in the interior `U` of the domain of `ψ`, where `ψ` is
finite, convex and differentiable almost everywhere with `∂ψ(x) = {∇ψ(x)}`). -/
theorem_wanted brenier {n : ℕ} (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ2 : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) < ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) < ∞)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Measurable T ∧
      ∃ πT : ProbabilityMeasure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        (πT : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
          (μ : Measure (EuclideanSpace ℝ (Fin n))).map (fun x => (x, T x)) ∧
        IsCoupling μ ν πT ∧
        ∫⁻ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), edist z.1 z.2 ^ (2 : ℝ)
          ∂(πT : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
            transportCost 2 μ ν ∧
        (∀ π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
          IsCoupling μ ν π →
          ∫⁻ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), edist z.1 z.2 ^ (2 : ℝ)
            ∂(π : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
              transportCost 2 μ ν → π = πT) ∧
        ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
          IsOpen U ∧ Convex ℝ U ∧ (μ : Measure (EuclideanSpace ℝ (Fin n))) Uᶜ = 0 ∧
          ConvexOn ℝ U ψ ∧ ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), HasGradientAt ψ (T x) x

end MathlibExt.MeasureTheory.BrenierWanted
