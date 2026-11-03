/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChainConstruction
public import MathlibExt.Biology.PopulationGenetics.WrightFisherChain

/-!
# Finite Wright–Fisher results under the canonical Markov law

The existing `markovChainMeasure` supplies the probability law. The finite-chain
predicate bridge makes the existing conditional Wright–Fisher theorems applicable
without a caller-supplied process or Markov property. No new law is defined here.

`M` counts gene copies and time counts generations. This is the finite chain, not
a continuous diffusion or path-law convergence theorem. Endpoint hitting includes
the one-state `M = 0` case; frequency formulas require `M > 0` because its two
endpoints otherwise coincide.

## References

* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Chapter 3.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Chapter 1.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.FiniteMarkovChain
open MathlibExt.Probability.MarkovChainConstruction

namespace MathlibExt.Biology.PopulationGenetics.WrightFisherChain

/-- The finite Wright–Fisher chain under the canonical Markov law almost surely
reaches an endpoint. The law and chain are not premises supplied by a caller. -/
theorem measure_markovChainMeasure_exists_absorbed (M : ℕ) (i : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel (wrightFisher M)) (Measure.dirac i))
      {ω | ∃ t, ω t = 0 ∨ ω t = Fin.last M} = 1 := by
  exact measure_exists_absorbed
    (isFiniteMarkovChain_markovChainMeasure (wrightFisher M) i)
    (ae_eval_zero_markovChainMeasure (wrightFisher M) i)

/-- Under the canonical finite Wright–Fisher law, the probability of ever fixing
at `M` equals the initial allele frequency `i / M`. -/
theorem measureReal_markovChainMeasure_exists_eq_last {M : ℕ} (hM : 0 < M)
    (i : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel (wrightFisher M)) (Measure.dirac i)).real
      {ω | ∃ t, ω t = Fin.last M} = ((i : ℕ) : ℝ) / M := by
  exact measureReal_exists_eq_last hM
    (isFiniteMarkovChain_markovChainMeasure (wrightFisher M) i)
    (ae_eval_zero_markovChainMeasure (wrightFisher M) i)

/-- Under the canonical finite Wright–Fisher law, the probability of ever losing
the allele at `0` equals `1 - i / M`. -/
theorem measureReal_markovChainMeasure_exists_eq_zero {M : ℕ} (hM : 0 < M)
    (i : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel (wrightFisher M)) (Measure.dirac i)).real
      {ω | ∃ t, ω t = 0} = 1 - ((i : ℕ) : ℝ) / M := by
  exact measureReal_exists_eq_zero hM
    (isFiniteMarkovChain_markovChainMeasure (wrightFisher M) i)
    (ae_eval_zero_markovChainMeasure (wrightFisher M) i)

end MathlibExt.Biology.PopulationGenetics.WrightFisherChain
