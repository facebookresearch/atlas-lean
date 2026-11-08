/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainConstruction

/-!
# Tests for Markov chain construction

A restatement of `markov_chain_construction` with its exact public
signature, the lifted kernel being a Markov kernel, the canonical
measure being a probability measure, a restatement of the conditional
distribution theorem, and two concrete instances: the identity kernel
on `ℝ` started from `δ₀`, whose initial law is `δ₀`, and the lifted
identity kernel applied to a history, which is the Dirac mass at the
history's last coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel Set
open MathlibExt.Probability.MarkovChainConstruction

namespace MathlibExtTest.Probability.MarkovChainConstruction

/-- The Markov-chain construction theorem restates with its exact public signature. -/
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (P : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P),
      P.map (fun (ω : ℕ → ℝ) => ω 0) = μ ∧
      ∀ n : ℕ,
        condDistrib (fun (x : ℕ → ℝ) => x (n + 1)) (Preorder.frestrictLe n) P
          =ᵐ[Measure.map (Preorder.frestrictLe n) P] markovLiftKernel κ n :=
  markov_chain_construction κ μ

/-- The lifted kernel of a Markov kernel is a Markov kernel. -/
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovLiftKernel κ n) := by
  infer_instance

/-- The canonical Markov-chain measure is a probability measure. -/
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (markovChainMeasure κ μ) := by
  infer_instance

/-- The conditional distribution theorem restates with its exact public signature. -/
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    condDistrib (fun (x : ℕ → ℝ) => x (n + 1)) (Preorder.frestrictLe n)
      (markovChainMeasure κ μ)
      =ᵐ[Measure.map (Preorder.frestrictLe n) (markovChainMeasure κ μ)]
        markovLiftKernel κ n :=
  markovChainMeasure_condDistrib κ μ n

/-- Concrete instance: the identity kernel on `ℝ` started from `δ₀` has initial law `δ₀`. -/
example :
    Measure.map (fun (ω : ℕ → ℝ) => ω 0)
      (markovChainMeasure Kernel.id (Measure.dirac 0)) = Measure.dirac 0 :=
  markovChainMeasure_initial_distribution Kernel.id (Measure.dirac 0)

/-- Concrete instance: the lifted identity kernel applied to a finite history is the
Dirac mass at the history's last coordinate. -/
example (n : ℕ) (x : (i : ↥(Finset.Iic n)) → ℝ) :
    markovLiftKernel Kernel.id n x =
      Measure.dirac (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rfl

#print axioms markov_chain_construction
#print axioms markovChainMeasure_initial_distribution
#print axioms markovChainMeasure_condDistrib

end MathlibExtTest.Probability.MarkovChainConstruction
