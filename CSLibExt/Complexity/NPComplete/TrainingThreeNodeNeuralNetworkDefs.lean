/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAINING A 3-NODE NEURAL NETWORK: definitions

Source:
A. L. Blum and R. L. Rivest, "Training a 3-node neural network is NP-complete", Neural Networks
5(1) (1992), 117-127, doi:10.1016/S0893-6080(05)80010-3; conference version in *Advances in
Neural Information Processing Systems 1* (NIPS 1988), 494-501 (problem TRAINING A 3-NODE NEURAL
NETWORK and its Theorem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import CSLibExt.MachineLearning.Perceptron

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork

open Cslib.MachineLearning.Perceptron (sign)

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

end MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork
