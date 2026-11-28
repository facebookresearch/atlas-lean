/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetworkDefs

namespace MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork

open MetaMathlibExt.BitstringEncoding
open Cslib.MachineLearning.Perceptron (sign)

private theorem sum_two {M : Type} [AddCommMonoid M] (g : Fin 2 → M) :
    ∑ i, g i = g 0 + (g 1 + 0) := rfl

/-- Exclusive or on two inputs, which no single threshold function computes. -/
private abbrev xor : TrainingThreeNodeNeuralNetworkInstance :=
  (2, [([false, false], false), ([false, true], true), ([true, false], true), ([true, true], false)])

private theorem xor_wellFormed : WellFormed xor := by unfold WellFormed; decide

/-- `N₁` computes OR (`x₁ + x₂ > 1/2`), `N₂` computes NAND (`-x₁ - x₂ > -3/2`), and `N₃`
outputs `+1` only when both do (`h₁ + h₂ > 1`): the network computes exclusive or. -/
private theorem xor_feasible : TrainingThreeNodeNeuralNetworkFeasible xor := by
  unfold TrainingThreeNodeNeuralNetworkFeasible
  dsimp only
  refine ⟨![1, 1], ![-1, -1], 1 / 2, -3 / 2, ![1, 1], 1, ?_⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    norm_num [output, threshold, inputs, dotProduct, sum_two, sign]

/-- One input, presented once as a positive and once as a negative example. -/
private abbrev contradictory : TrainingThreeNodeNeuralNetworkInstance :=
  (1, [([true], true), ([true], false)])

private theorem contradictory_wellFormed : WellFormed contradictory := by
  unfold WellFormed; decide

/-- The network computes a function of its input, so it cannot output both `+1` and `-1` on
the same input. -/
private theorem contradictory_infeasible :
    ¬ TrainingThreeNodeNeuralNetworkFeasible contradictory := by
  rintro ⟨a₁, a₂, t₁, t₂, c, c₀, h⟩
  have hp := h ([true], true) (by simp)
  have hn := h ([true], false) (by simp)
  rw [hp] at hn
  norm_num [sign] at hn

/-- An example with the wrong number of inputs is malformed. -/
example : ¬ WellFormed ((2, [([true], true)]) : TrainingThreeNodeNeuralNetworkInstance) := by
  unfold WellFormed; decide

/-- The decision problem accepts the encoding of `xor`. -/
example : trainingThreeNodeNeuralNetworkDec (bitEncode xor) = true := by
  simp [trainingThreeNodeNeuralNetworkDec, xor_wellFormed, xor_feasible]

/-- It rejects the encoding of the well-formed but infeasible `contradictory`. -/
example : trainingThreeNodeNeuralNetworkDec (bitEncode contradictory) = false := by
  simp [trainingThreeNodeNeuralNetworkDec, contradictory_infeasible]

/-- `contradictory` is well formed, so infeasibility is what rejects it. -/
example : WellFormed contradictory := contradictory_wellFormed

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : trainingThreeNodeNeuralNetworkDec [true] = false := by
  have h : bitDecode (α := TrainingThreeNodeNeuralNetworkInstance) [true] = none := rfl
  simp [trainingThreeNodeNeuralNetworkDec, h]

end MetaMathlibExt.Complexity.NPComplete.TrainingThreeNodeNeuralNetwork
