/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Path-space moments of the two-locus coalescence times

`MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent` proves that the backward (first-step)
equations of the two-locus ancestral process of a sample of two have unique solutions, with
`E T_A = 1` and `E (T_A T_B) = 1 + (ρ + 18) / (ρ² + 13ρ + 18)` from the `linked` state
(Hudson 1983; Kaplan & Hudson 1985). The statements recorded here identify these solutions with
expectations over the path process `ctmcPath (twoLocusRate ρ) linked` built in
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`, where the coalescence time at a
locus is the hitting time of the states in which that locus has coalesced. They are stated as
lower Lebesgue integrals of `ℝ≥0∞`-valued hitting times, so no integrability hypothesis is
needed. Together they give `Cov(T_A, T_B) = (ρ + 18) / (ρ² + 13ρ + 18)`.

A proof route: `{T_A > t} = {X t ∉ coalesced A}` because the coalesced states are closed, so
`E (T_A T_B) = ∫∫ P(X s ∉ A, X t ∉ B) ds dt` by Tonelli, and the finite-dimensional
distributions (`ctmcInputMeasure_real_ctmcPath_fdd`) reduce the double integral to integrals of
`exp (t Q)` over the transient states, which the backward equations evaluate.

Sources: R. R. Hudson, "Properties of a neutral allele model with intragenic recombination",
Theor. Popul. Biol. 23 (1983) 183–201; N. L. Kaplan and R. R. Hudson, "The use of sample
genealogies for studying a selectively neutral m-loci model with recombination", Theor. Popul.
Biol. 28 (1985) 382–396; J. R. Norris, *Markov Chains* (1997), §3.3.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentWanted

open MeasureTheory ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent TwoLocusState
open scoped NNReal ENNReal

/-- **Mean coalescence time at one locus, path form**: for the two-locus ancestral process
started from two linked sequences, the hitting time `T_A` of the states where locus `A` has
coalesced has mean `1`. -/
theorem_wanted lintegral_coalescenceTimeA [MeasurableSpace TwoLocusState]
    [DiscreteMeasurableSpace TwoLocusState] {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = 1

/-- **Product moment of the two coalescence times, path form** (Hudson 1983; Kaplan & Hudson
1985): from two linked sequences, `E (T_A T_B) = 1 + (ρ + 18) / (ρ² + 13ρ + 18)`. -/
theorem_wanted lintegral_coalescenceTimeA_mul_coalescenceTimeB [MeasurableSpace TwoLocusState]
    [DiscreteMeasurableSpace TwoLocusState] {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) =
      ENNReal.ofReal (1 + twoLocusCov ρ)

end MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentWanted
