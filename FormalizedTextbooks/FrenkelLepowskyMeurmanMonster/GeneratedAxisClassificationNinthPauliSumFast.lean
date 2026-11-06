/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData

/-! A proved zero-coefficient branch preserves the complete 128-term reconstruction sum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The full stated integer sum, with a zero source coefficient evaluated before its state. -/
def generatedNinthPauliReconstructionFast (b : Fin 8) (n : Fin 4096) : ℤ :=
  ∑ q : Fin 128,
    if generatedNinthPauliInputCoefficients b q = 0 then 0 else
      generatedNinthPauliInputCoefficients b q *
        generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n

/-- Skipping a state with zero source coefficient preserves the entire original finite sum. -/
theorem generatedNinth_pauli_reconstruction_fast (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliReconstructionFast b n =
      ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
        generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n := by
  unfold generatedNinthPauliReconstructionFast
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : generatedNinthPauliInputCoefficients b q = 0
  · simp only [h, ite_true, zero_mul]
  · rw [ite_eq_right h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
