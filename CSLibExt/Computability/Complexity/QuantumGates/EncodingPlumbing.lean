/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# QGate/RatEnc encoding plumbing for approximants

General bridges between Gaussian-rational matrices and well-formed Atlas
gates: every Gaussian-rational unitary `4 × 4` matrix encodes as a
well-formed gate on any qubit pair, and every complex matrix with
Gaussian-rational entries has a Gaussian-rational encoding representing it.
Approximant generators (for example from rational unitary snapping) produce
Gaussian-rational unitaries; these lemmas turn them into `QGate` encodings
with the expected decoded matrix.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

/-- Any Gaussian-rational unitary encodes as a well-formed gate on qubits
`i < j`. -/
theorem qGateWellFormed_entriesOf
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat)
    (hU : star (complexOfGRatMatrix M) * complexOfGRatMatrix M = 1)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, entriesOf M) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries (entriesOf M)) * matrixOfEntries (entriesOf M) = 1
  rw [matrixOfEntries_entriesOf]
  exact hU

/-- Every complex matrix with Gaussian-rational entries is represented by a
Gaussian-rational matrix of encodings. -/
theorem exists_gratMatrix_eq
    (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : ∀ p q, ∃ a b : ℚ, U p q = ⟨(a : ℝ), (b : ℝ)⟩) :
    ∃ M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat,
      complexOfGRatMatrix M = U ∧
        ∀ p q, ∃ a b : ℚ, M p q = gaussRatEnc a b := by
  choose a b hab using hU
  refine ⟨fun p q => gaussRatEnc (a p q) (b p q), ?_,
    fun p q => ⟨a p q, b p q, rfl⟩⟩
  ext p q
  show toComplex (gaussRatEnc (a p q) (b p q)) = U p q
  rw [toComplex_gaussRatEnc]
  exact (hab p q).symm

/-- Every Gaussian-rational unitary is the decoded matrix of a well-formed
gate on any qubit pair, with a 16-entry encoding. -/
theorem exists_wellFormed_gate_matrixOfEntries_eq
    (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : star U * U = 1)
    (hG : ∀ p q, ∃ a b : ℚ, U p q = ⟨(a : ℝ), (b : ℝ)⟩)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    ∃ e : List (RatEnc × RatEnc),
      QGateWellFormed N (i, j, e) ∧ matrixOfEntries e = U ∧ e.length = 16 := by
  obtain ⟨M, rfl, -⟩ := exists_gratMatrix_eq U hG
  exact ⟨entriesOf M, qGateWellFormed_entriesOf M hU hij hjN,
    matrixOfEntries_entriesOf M, entriesOf_length M⟩

end Cslib.Complexity.Classes.QuantumGates
