/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedSoundness

/-! All eight original input columns reconstruct from actual Q translates of column one. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The literal positive Q witnesses in the exact original source-coordinate masks. -/
def generatedNinthPauliWitness (q : Fin 128) : Q :=
  generatedNinthPauliQ (generatedNinthPauliWitnessLabels q 0)
    (generatedNinthPauliWitnessLabels q 1)

/-- Every cached witness state is the actual full signed Q translate of the original input. -/
theorem generatedNinth_pauli_operator_actual (q : Fin 128) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n =
      nortonUIntegerQ (generatedNinthPauliWitness q) (generatedNinthColumnInputInteger 1) n := by
  rw [generatedNinth_pauli_operator_certificate, ← generatedNinth_pauli_sparse_actual]
  change nortonUIntegerQ (generatedNinthPauliWitness q) (generatedNinthColumnSpinPacked 0) n = _
  have h : generatedNinthColumnSpinPacked 0 = generatedNinthColumnInputInteger 1 := by
    funext m
    rw [generatedNinth_column_spin_packed, generatedNinth_column_initial_actual]
  rw [h]

/-- Every cached basis input is its actual original physical input column. -/
theorem generatedNinth_pauli_input_actual (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b) n := by
  rw [generatedNinth_pauli_input_certificate, ← generatedNinth_column_input_sparse]

/-- All eight literal original inputs are exact integer combinations of actual Q translates. -/
theorem generatedNinth_pauli_input_reconstruction (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliInputDenominator b *
      generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b) n =
        ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
          nortonUIntegerQ (generatedNinthPauliWitness q)
            (generatedNinthColumnInputInteger 1) n := by
  have h := generatedNinth_pauli_reconstruction b n
  simpa only [generatedNinth_pauli_input_actual, generatedNinth_pauli_operator_actual] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
