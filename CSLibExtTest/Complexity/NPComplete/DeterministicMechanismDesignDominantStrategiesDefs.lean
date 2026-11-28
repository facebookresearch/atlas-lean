/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategiesDefs

namespace MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open QuadraticProgramming (RatCode)

private theorem accepts_encoding (i : DeterministicMechanismDesignDominantStrategiesInstance) :
    deterministicMechanismDesignDominantStrategiesDec (bitEncode i) = true ↔
      WellFormed i ∧ DeterministicMechanismDesignDominantStrategiesFeasible i := by
  simp [deterministicMechanismDesignDominantStrategiesDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : deterministicMechanismDesignDominantStrategiesDec [true] = false := by
  have h : bitDecode (α := DeterministicMechanismDesignDominantStrategiesInstance) [true] =
    none := rfl
  simp [deterministicMechanismDesignDominantStrategiesDec, h]

/-- Agent 1 has two equally likely types; type `θ` values outcome `θ` at `1` and the other
outcome at `0`. -/
private abbrev agent₁ : AgentData :=
  ([(1, 2), (1, 2)], [[((1, 0), 1), ((0, 0), 1)], [((0, 0), 1), ((1, 0), 1)]])

/-- Agent 2 has a single type, indifferent between the two outcomes. -/
private abbrev agent₂ : AgentData := ([(1, 1)], [[((0, 0), 1), ((0, 0), 1)]])

/-- Two outcomes, the two agents, the objective table `g`, and the goal `G = 1`. -/
private abbrev withObjective (g : List (List (List RatCode))) :
    DeterministicMechanismDesignDominantStrategiesInstance := (2, agent₁, agent₂, g, ((1, 0), 1))

/-- The objective rewards choosing agent 1's favorite outcome. -/
private abbrev yesInst := withObjective
  [[[((1, 0), 1), ((0, 0), 1)]], [[((0, 0), 1), ((1, 0), 1)]]]

/-- The objective rewards choosing the outcome agent 1 likes less. -/
private abbrev noInst := withObjective
  [[[((0, 0), 1), ((1, 0), 1)]], [[((1, 0), 1), ((0, 0), 1)]]]

/-- Choosing agent 1's reported favorite is truthful and attains `E[g] = 1`. -/
example : deterministicMechanismDesignDominantStrategiesDec (bitEncode yesInst) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed AgentWellFormed; decide +kernel,
    fun θ₁ _ => θ₁, ?_, ?_⟩
  · unfold IsDominantStrategyImplementation
    decide +kernel
  · decide +kernel

/-- The instance is well formed, but `E[g] = 1` needs the less liked outcome for both types of
agent 1, and type `0` would then gain by reporting type `1`; every one of the four mechanisms
fails. -/
example : deterministicMechanismDesignDominantStrategiesDec (bitEncode noInst) = false := by
  have hw : WellFormed noInst := by unfold WellFormed AgentWellFormed; decide +kernel
  have h : ¬ DeterministicMechanismDesignDominantStrategiesFeasible noInst := by
    unfold DeterministicMechanismDesignDominantStrategiesFeasible
      IsDominantStrategyImplementation
    decide +kernel
  simp [deterministicMechanismDesignDominantStrategiesDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies
