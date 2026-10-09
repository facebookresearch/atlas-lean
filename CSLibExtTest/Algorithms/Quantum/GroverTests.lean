/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover

@[expose] public section

/-!
# Public API tests for Grover search

These tests use only the topic entry point. They also exercise the degenerate
empty and fully marked definitions, which are deliberately outside the
hypotheses of the exact nondegenerate analysis.
-/

namespace Cslib.Grover.Tests

def oneMarked : Finset (Fin 4) := {0}

theorem oneMarked_nonempty : oneMarked.Nonempty := by
  simp [oneMarked]

theorem oneMarked_compl_nonempty : oneMarkedᶜ.Nonempty := by
  refine ⟨1, ?_⟩
  simp [oneMarked]

example {α : Type*} [DecidableEq α] (ψ : Amplitude α) :
    phaseOracle ∅ ψ = ψ := by
  funext x
  simp [phaseOracle]

example {α : Type*} [Fintype α] [DecidableEq α] (ψ : Amplitude α) :
    phaseOracle Finset.univ ψ = -ψ := by
  funext x
  simp [phaseOracle]

example {α : Type*} [DecidableEq α] (ψ : Amplitude α) :
    markedProbability ∅ ψ = 0 := by
  simp [markedProbability]

example {α : Type*} [Fintype α] [DecidableEq α] (ψ : Amplitude α) :
    markedProbability Finset.univ ψ = amplitudeNormSq ψ := by
  simp [markedProbability, amplitudeNormSq]

example (k : ℕ) :
    markedProbability oneMarked
        (groverIterate oneMarked k (uniformAmplitude (Fin 4))) =
      (Real.sin (groverPhase oneMarked k)) ^ 2 :=
  markedProbability_groverIterate_uniform oneMarked oneMarked_nonempty
    oneMarked_compl_nonempty k

example : amplitudeNormSq (uniformAmplitude (Fin 4)) = 1 :=
  amplitudeNormSq_uniformAmplitude (Fin 4)

example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (marked : Finset α) (k : ℕ) :
    amplitudeNormSq (groverIterate marked k (uniformAmplitude α)) = 1 :=
  amplitudeNormSq_groverIterate_uniform marked k

example (k : ℕ) :
    amplitudeNormSq
        (groverIterate oneMarked k (uniformAmplitude (Fin 4))) = 1 :=
  amplitudeNormSq_groverIterate_uniform oneMarked k

#print axioms Cslib.Grover.amplitudeNormSq_uniformAmplitude
#print axioms Cslib.Grover.amplitudeNormSq_groverIterate
#print axioms Cslib.Grover.amplitudeNormSq_groverIterate_uniform
#print axioms Cslib.Grover.amplitudeNormSq_groverStep
#print axioms Cslib.Grover.groverIterate_uniform_eq_angleAmplitude
#print axioms Cslib.Grover.markedProbability_groverIterate_uniform
#print axioms Cslib.Grover.floorIterations_failure_probability_le
#print axioms Cslib.Grover.one_step_success_of_four_mul_card_eq

end Cslib.Grover.Tests
