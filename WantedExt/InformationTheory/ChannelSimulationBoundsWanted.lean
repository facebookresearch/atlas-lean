/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.InformationTheory.FiniteChannelSimulation
public import MathlibExt.InformationTheory.FunctionalRepresentation
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Established channel-simulation bounds and semantic bridges

All thirteen declarations are private wanted requests, not proofs or theorem
assumptions. They preserve the pinned catalogue's exact endpoints, the actual
finite-law primary optimizer, and the general Polish/Borel finite-KL domain.
-/

@[expose] public section

universe u v

namespace InformationTheory

open MeasureTheory
open scoped ENNReal

/-- Identification of the finite entropy identity with general Shannon entropy.
Source: constants/32a.md and Li, arXiv:2501.13736v4, general Shannon convention.
The conditional-expectation and quantization comparison remains unproved. -/
private theorem_wanted finiteConditionalEntropyIdentification
    (p : FiniteJointLaw) (q : FiniteExtension p) :
    generalConditionalEntropy
      (⟨q.law.toMeasure, inferInstance⟩ :
        ProbabilityMeasure ((Fin p.nx × Fin p.ny) × Fin q.ns)) =
      ENNReal.ofReal q.conditionalEntropy

/-- Actual-law general strong functional representation at the catalogue endpoint.
Source: constants/32a.md; LEG18, arXiv:1701.02827v4, Theorem 1 and its entropy
interpretation; Li25 general Shannon convention. LEG18v4's main theorem prints
4, not 3.871. This catalogue variant is an unproved request, not a claimed proof. -/
private theorem_wanted strongFunctionalRepresentation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure (X × Y)) (hI : measureMutualInformation μ < ⊤) :
    ∃ (S : Type (max u v)) (mS : MeasurableSpace S),
      letI := mS
      ∃ ν : ProbabilityMeasure ((X × Y) × S), IsGeneralRepresentation μ ν ∧
        generalConditionalEntropy ν ≤ ENNReal.ofReal
          ((measureMutualInformation μ).toReal +
            Real.log ((measureMutualInformation μ).toReal + 1) / Real.log 2 + 3871 / 1000)

/-- Equality of the primary limsup and the independently defined uniform infimum.
Source: constants/32a.md, equivalent alpha/beta description. -/
private theorem_wanted outerConstantIdentification :
    channelSimulationConstant = uniformOuterConstantInfimum

/-- The primary asymptotic upper endpoint is finite.
Source: constants/32a.md, HJMR07/HJMR10/BG14 upper row. -/
private theorem_wanted upperFinite : channelSimulationConstant < ⊤

/-- The catalogue's non-strict 3.871 upper row.
Source: constants/32a.md, LEG18 upper row, distinct from its strict comment. -/
private theorem_wanted strongRepresentationUpper :
    channelSimulationConstant ≤ ((3871 / 1000 : ℝ) : EReal)

/-- The exact decimal 3.732 Poisson-matching upper row.
Source: constants/32a.md, LA21; Li25 Section 5 plot discussion. -/
private theorem_wanted poissonMatchingUpper :
    channelSimulationConstant ≤ ((933 / 250 : ℝ) : EReal)

/-- The exact decimal 3.45 adaptive greedy rejection-sampling upper row.
Source: constants/32a.md, FT23. -/
private theorem_wanted greedyRejectionUpper :
    channelSimulationConstant ≤ ((69 / 20 : ℝ) : EReal)

/-- The exact constant two pointwise-redundancy upper row.
Source: constants/32a.md, Li24a/Li24b; Li25 equation Hu_prev. -/
private theorem_wanted pointwiseRedundancyUpper : channelSimulationConstant ≤ (2 : EReal)

/-- The exact discrete layered-entropy series upper endpoint.
Source: constants/32a.md and Li, arXiv:2501.13736v4, c_c* bound. The k=0
summand is zero, so the series is precisely the source's k≥1 series. -/
private theorem_wanted layeredEntropyUpper :
    channelSimulationConstant ≤
      (((∑' k : ℕ, (2 : ℝ) ^ (-(k : ℤ) - 1) * k * (Real.log k / Real.log 2)) -
        Real.log (1 / Real.log 2) / Real.log 2 : ℝ) : EReal)

/-- The primary asymptotic constant is strictly above negative infinity.
Source: constants/32a.md, BG14 lower row. -/
private theorem_wanted lowerFinite : (⊥ : EReal) < channelSimulationConstant

/-- The exact excess-information lower row -1.
Source: constants/32a.md, LEG18 lower row; LEG18v4 lower-bound construction. -/
private theorem_wanted excessInformationLower : (-1 : EReal) ≤ channelSimulationConstant

/-- The exact symbolic lower row -log₂(log₂ e), not the approximate -0.53.
Source: constants/32a.md and Li, arXiv:2501.13736v4, finite quantization of the
continuous lower construction. -/
private theorem_wanted layeredEntropyLower :
    ((-Real.log (1 / Real.log 2) / Real.log 2 : ℝ) : EReal) ≤ channelSimulationConstant

/-- The strict 3.871 endpoint printed in the catalogue's additional comment.
Source: constants/32a.md, -1≤C32<3.871; not weakened to the upper table row. -/
private theorem_wanted strictRepresentationUpper :
    channelSimulationConstant < ((3871 / 1000 : ℝ) : EReal)

end InformationTheory
