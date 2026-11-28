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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetworkDefs

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

/-- **TRAINING A 3-NODE NEURAL NETWORK is NP-complete.** Source: Blum and Rivest (1992). -/
public theorem_wanted trainingThreeNodeNeuralNetwork_npComplete :
    trainingThreeNodeNeuralNetworkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L trainingThreeNodeNeuralNetworkDec

end MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork
