/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAINING A 3-NODE NEURAL NETWORK is NP-complete

Source:
A. L. Blum and R. L. Rivest, "Training a 3-node neural network is NP-complete", Neural Networks
5(1) (1992), 117-127, doi:10.1016/S0893-6080(05)80010-3; conference version in *Advances in
Neural Information Processing Systems 1* (NIPS 1988), 494-501 (problem TRAINING A 3-NODE NEURAL
NETWORK and its Theorem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import CSLibExt.MachineLearning.Perceptron

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork

open Cslib.MachineLearning.Perceptron (sign)

/-!
# TRAINING A 3-NODE NEURAL NETWORK is NP-complete

The network has `n` binary inputs and three nodes `N₁, N₂, N₃`: all inputs feed the hidden
nodes `N₁` and `N₂`, whose outputs feed the output node `N₃`. Each node `Nᵢ` computes a linear
threshold function `fᵢ` of its inputs `x = (x₁, …, x_m)`: for some constants `a₀, …, a_m`,
`fᵢ(x) = +1` if `a₁x₁ + ⋯ + a_m x_m > a₀` and `fᵢ(x) = -1` otherwise. A training example is a
positive example (desired output `+1`) or a negative example (desired output `-1`).

INSTANCE: a set of training examples on `n` inputs. QUESTION: do there exist linear threshold
functions `f₁, f₂, f₃` for the nodes `N₁, N₂, N₃` such that the network produces outputs
consistent with the training set?

The constants are real numbers; inputs are `0` or `1`, and the hidden outputs `±1` are the
inputs of `N₃`. An example is a vector of `n` Booleans with its label (`true` for positive); the
desired output `±1` of a label is `Cslib.MachineLearning.Perceptron.sign`, and weighted sums are
Mathlib's `dotProduct`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of inputs and the training examples, each an input vector with
its label (`true` for a positive example). -/
abbrev TrainingThreeNodeNeuralNetworkInstance := ℕ × List (List Bool × Bool)

/-- A linear threshold function with weights `a` and threshold `a₀`: `+1` if
`a ⬝ᵥ z = ∑ⱼ aⱼ zⱼ > a₀`, and `-1` otherwise. -/
noncomputable def threshold {m : ℕ} (a : Fin m → ℝ) (a₀ : ℝ) (z : Fin m → ℝ) : ℝ :=
  if a₀ < a ⬝ᵥ z then 1 else -1

/-- An input vector as real inputs `0` or `1`. -/
noncomputable def inputs (n : ℕ) (x : List Bool) : Fin n → ℝ :=
  fun j => if x.getD j false then 1 else 0

/-- The output of the network: `N₃` (weights `c`, threshold `c₀`) applied to the outputs of
`N₁` (weights `a₁`, threshold `t₁`) and `N₂` (weights `a₂`, threshold `t₂`). -/
noncomputable def output {n : ℕ} (a₁ a₂ : Fin n → ℝ) (t₁ t₂ : ℝ) (c : Fin 2 → ℝ) (c₀ : ℝ)
    (z : Fin n → ℝ) : ℝ :=
  threshold c c₀ ![threshold a₁ t₁ z, threshold a₂ t₂ z]

/-- Well-formedness of an instance: every example has `n` inputs. -/
def WellFormed (i : TrainingThreeNodeNeuralNetworkInstance) : Prop :=
  ∀ e ∈ i.2, e.1.length = i.1

/-- Some linear threshold functions for the three nodes make the network output `+1` on every
positive example and `-1` on every negative example. -/
def TrainingThreeNodeNeuralNetworkFeasible (i : TrainingThreeNodeNeuralNetworkInstance) :
    Prop :=
  ∃ a₁ a₂ : Fin i.1 → ℝ, ∃ t₁ t₂ : ℝ, ∃ c : Fin 2 → ℝ, ∃ c₀ : ℝ,
    ∀ e ∈ i.2, output a₁ a₂ t₁ t₂ c c₀ (inputs i.1 e.1) = sign e.2

open Classical in
/-- TRAINING A 3-NODE NEURAL NETWORK as a decision problem over bitstrings. -/
noncomputable def trainingThreeNodeNeuralNetworkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TrainingThreeNodeNeuralNetworkInstance) x with
  | some i => decide (WellFormed i ∧ TrainingThreeNodeNeuralNetworkFeasible i)
  | none => false

/-- **TRAINING A 3-NODE NEURAL NETWORK is NP-complete.** Source: Blum and Rivest (1992). -/
public theorem_wanted trainingThreeNodeNeuralNetwork_npComplete :
    trainingThreeNodeNeuralNetworkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L trainingThreeNodeNeuralNetworkDec

end MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork
