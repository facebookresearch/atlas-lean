/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Logic.Equiv.Prod


/-!
# Gate relabeling at the encoding level

SWAP-conjugated gate entry lists and well-formedness of relabeled gates, in both orientations, over the merged exact gate exports.
-/

@[expose] public section

open Cslib.Complexity.Classes
namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

/-- entry list of SWAP·M·SWAP for an arbitrary entry list (same default as matrixOfEntries) -/
def swapConjEntries (l : List (RatEnc × RatEnc)) : List (RatEnc × RatEnc) := entriesOf (Matrix.of fun p q => l.getD (qIdx2 p.swap * 4 + qIdx2 q.swap) ((false, 0, 1), (false, 0, 1)))

theorem swapConjEntries_length (l : List (RatEnc × RatEnc)) : (swapConjEntries l).length = 16 := rfl

/-- decoding of the conjugated list -/
theorem matrixOfEntries_swapConjEntries (l : List (RatEnc × RatEnc)) : matrixOfEntries (swapConjEntries l) = (matrixOfEntries l).submatrix Prod.swap Prod.swap := by
  unfold swapConjEntries
  rw [matrixOfEntries_entriesOf]
  apply Matrix.ext
  intro p q
  rfl

/-- identifies the reindex with the exporter's SWAP (contract wording "SWAP M SWAP") -/
theorem swapMatrix_mul_mul_swapMatrix (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : complexOfGRatMatrix swapMatrix * M * complexOfGRatMatrix swapMatrix = M.submatrix Prod.swap Prod.swap := by
  apply Matrix.ext
  intro p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, complexOfGRatMatrix, swapMatrix,
      toComplex_gaussRatEnc, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.submatrix_apply, Complex.ext_iff]

/-- "star(SWAP M SWAP)(SWAP M SWAP) = 1 from star M * M = 1" -/
theorem star_mul_self_matrixOfEntries_swapConjEntries {l : List (RatEnc × RatEnc)} (h : star (matrixOfEntries l) * matrixOfEntries l = 1) : star (matrixOfEntries (swapConjEntries l)) * matrixOfEntries (swapConjEntries l) = 1 := by
  have h' : Matrix.conjTranspose (matrixOfEntries l) * matrixOfEntries l = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using h
  rw [matrixOfEntries_swapConjEntries, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, ← Equiv.coe_prodComm,
    Matrix.submatrix_mul_equiv, h']
  exact Matrix.submatrix_one_equiv (Equiv.prodComm (Fin 2) (Fin 2))

/-- exact list equality on exporter outputs -/
theorem swapConjEntries_entriesOf (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat) : swapConjEntries (entriesOf M) = entriesOf (M.submatrix Prod.swap Prod.swap) := by
  rfl

/-- exporter orientation rule recovered -/
theorem ctrlLow_submatrix_swap (U : Matrix (Fin 2) (Fin 2) GRat) : (ctrlLow U).submatrix Prod.swap Prod.swap = ctrlHigh U := by
  apply Matrix.ext
  intro p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

/-- contract: (i, j, M) ↦ (π i, π j, M) if π i < π j, else (π j, π i, SWAP M SWAP) -/
def relabelGate (π : ℕ → ℕ) (g : QGate) : QGate := if π g.1 < π g.2.1 then (π g.1, π g.2.1, g.2.2) else (π g.2.1, π g.1, swapConjEntries g.2.2)

/-- acceptance bullet 1, both orientations -/
theorem qGateWellFormed_relabelGate {N N' : ℕ} {π : ℕ → ℕ} {g : QGate} (hg : QGateWellFormed N g) (hne : π g.1 ≠ π g.2.1) (h₁ : π g.1 < N') (h₂ : π g.2.1 < N') : QGateWellFormed N' (relabelGate π g) := by
  have hU : star (matrixOfEntries g.2.2) * matrixOfEntries g.2.2 = 1 := hg.2.2
  unfold relabelGate
  by_cases h : π g.1 < π g.2.1
  · simp [h]
    exact ⟨h, h₂, hU⟩
  · simp [h]
    have hswap : π g.2.1 < π g.1 := by omega
    exact ⟨hswap, h₁, star_mul_self_matrixOfEntries_swapConjEntries hU⟩

/-- list form for relocated verifier copies -/
theorem qGateWellFormed_map_relabelGate {N N' : ℕ} {π : ℕ → ℕ} {gs : List QGate} (hgs : ∀ g ∈ gs, QGateWellFormed N g) (hinj : ∀ a b, a < N → b < N → a ≠ b → π a ≠ π b) (hπ : ∀ a, a < N → π a < N') : ∀ g ∈ gs.map (relabelGate π), QGateWellFormed N' g := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0mem, rfl⟩ := hg
  have h12 : g0.1 < g0.2.1 := (hgs g0 hg0mem).1
  have h2N : g0.2.1 < N := (hgs g0 hg0mem).2.1
  have hg1N : g0.1 < N := lt_trans h12 h2N
  exact qGateWellFormed_relabelGate (hgs g0 hg0mem) (hinj _ _ hg1N h2N (ne_of_lt h12))
    (hπ _ hg1N) (hπ _ h2N)

/-- consistency with the merged exporter (controlledGate) -/
theorem relabelGate_ctrlLow (U : Matrix (Fin 2) (Fin 2) GRat) (π : ℕ → ℕ) : relabelGate π (0, 1, entriesOf (ctrlLow U)) = controlledGate U (π 0) (π 1) := by
  simp only [relabelGate, controlledGate]
  by_cases h : π 0 < π 1
  · simp [h]
  · simp [h, swapConjEntries_entriesOf, ctrlLow_submatrix_swap]

end Cslib.Complexity.Classes.QuantumGates
