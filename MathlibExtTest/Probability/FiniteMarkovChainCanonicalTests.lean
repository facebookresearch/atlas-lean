/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExtTest.Probability.FiniteMarkovChain
public import MathlibExt.Probability.KolmogorovCycleNecessity
public import MathlibExt.Probability.MarkovChainFunctionCK
import Mathlib.Tactic.FinCases

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Finset
open MathlibExt.Probability.FiniteMarkovChain
open MathlibExt.Probability.FiniteMarkovChainTest

namespace MathlibExtTest.Probability.FiniteMarkovChainCanonicalTests

/-- Canonical probability distribution for the original flip transition matrix. -/
noncomputable def flipDistribution : _root_.StochasticMatrix.Distribution 1 where
  val _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

/-- The exact finite-chain matrix also inhabits the canonical reversibility API. -/
theorem canonical_flip_detailedBalance :
    _root_.StochasticMatrix.DetailedBalance flipMatrix flipDistribution := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [flipMatrix, flipDistribution]

/-- An existing, constructed finite witness converts to the canonical general predicate. -/
theorem alternating_isCanonicalChain :
    MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain
      altProcess topFiltration (finiteChainKernel flipMatrix) (Measure.dirac ()) :=
  altChain_isFiniteMarkovChain.toIsMarkovChain

/-- The smallest finite witness also converts without assuming a canonical witness. -/
theorem oneState_isCanonicalChain :
    MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain
      oneStateProcess topFiltration (finiteChainKernel oneStateMatrix) (Measure.dirac ()) :=
  oneState_isFiniteMarkovChain.toIsMarkovChain

/-- Zero-step law from the converted alternating witness. -/
theorem canonical_zero_step :
    (Measure.dirac ()).map (altProcess (0 + 0)) =
      ((Measure.dirac ()).map (altProcess 0)).bind (fun x =>
        ((finiteChainKernel flipMatrix) ^ 0) x) :=
  alternating_isCanonicalChain.map_eq_bind_pow 0 0

/-- One-step law from the same converted witness. -/
theorem canonical_one_step :
    (Measure.dirac ()).map (altProcess (0 + 1)) =
      ((Measure.dirac ()).map (altProcess 0)).bind (fun x =>
        ((finiteChainKernel flipMatrix) ^ 1) x) :=
  alternating_isCanonicalChain.map_eq_bind_pow 0 1

/-- Two-step law from the same converted witness, with literal 0→1→0 control in the original test. -/
theorem canonical_two_step :
    (Measure.dirac ()).map (altProcess (0 + 2)) =
      ((Measure.dirac ()).map (altProcess 0)).bind (fun x =>
        ((finiteChainKernel flipMatrix) ^ 2) x) :=
  alternating_isCanonicalChain.map_eq_bind_pow 0 2

/-- The existing n-step bounded state-function API accepts this converted finite witness. -/
theorem canonical_two_step_state_function :
    (Measure.dirac ())[(fun j : Fin 2 => (j : ℝ)) ∘ altProcess (0 + 2)
      | topFiltration 0] =ᵐ[Measure.dirac ()]
        fun ω => ∫ y, (y : ℝ) ∂((finiteChainKernel flipMatrix) ^ 2) (altProcess 0 ω) := by
  exact MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_comp_eq_integral_pow
    alternating_isCanonicalChain 0 2 measurable_from_top.stronglyMeasurable
    ⟨1, by intro j; fin_cases j <;> norm_num⟩

end MathlibExtTest.Probability.FiniteMarkovChainCanonicalTests
