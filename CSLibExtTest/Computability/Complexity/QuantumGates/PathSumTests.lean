/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PathSum
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# Tests: path-sum expansion and scaled integrality
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes

open scoped Matrix

#print axioms applyCircuit_eq_ampSum
#print axioms acceptProb_scaled_nat

/-- The identity gate on qubits `0, 1`: entry list is the `4 × 4` identity
in row-major order, real parts on the diagonal. -/
def idGate01 : QGate :=
  (0, 1, [((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1))])

private theorem matrixOfEntries_idGate01 : matrixOfEntries idGate01.2.2 = 1 := by
  unfold idGate01
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp only [matrixOfEntries, qIdx2, Matrix.one_apply] <;>
    norm_num [toComplex, toRat, Complex.ext_iff]

private theorem gateDenom_idGate01 : gateDenom idGate01 = 1 := by
  rfl

private theorem qGateWellFormed_idGate01 : QGateWellFormed 2 idGate01 := by
  refine ⟨by norm_num [idGate01], by norm_num [idGate01], ?_⟩
  simp only [matrixOfEntries_idGate01, star_one, one_mul]

private theorem gateMatrix_idGate01 : gateMatrix 2 idGate01 = 1 := by
  ext s t
  have hagree : (∀ k : Fin 2, k.val ≠ idGate01.1 → k.val ≠ idGate01.2.1 →
      qBit k.val s.val = qBit k.val t.val) := by
    intro k hk0 hk1
    simp only [idGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, matrixOfEntries_idGate01, Matrix.one_apply]
  fin_cases s <;> fin_cases t <;> simp [qBit, idGate01]

/-- Nonvacuity, two-gate check: the empty path sum is the Kronecker delta,
a single identity gate has diagonal amplitude `1`, and the two-gate
identity circuit on input `[true]` has scaled acceptance `1` at scale `1`. -/
theorem pathSum_two_gate_check :
    (∀ s t : Fin (2 ^ 2), ampSum 2 [] s t = if s = t then 1 else 0) ∧
      (∀ s : Fin (2 ^ 2), ampSum 2 [idGate01] s s = 1) ∧
      (([idGate01, idGate01].map gateDenom).prod : ℝ) ^ 2 *
        acceptProb (applyCircuit (1 + 1) [idGate01, idGate01]
          (bqpInitState [true] 1)) = 1 := by
  refine ⟨?h1, ?h2, ?h3⟩
  · intro s t
    rfl
  · intro s
    show (∑ u, ampSum 2 [] s u * gateMatrix 2 idGate01 u s) = 1
    simp only [show ∀ a b : Fin (2 ^ 2), ampSum 2 [] a b = if a = b then 1 else 0
      from fun a b => rfl]
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
    rw [gateMatrix_idGate01]
    simp
  · have hprod : (([idGate01, idGate01].map gateDenom).prod : ℝ) = 1 := by
      simp [gateDenom_idGate01]
    rw [hprod]
    norm_num
    have hwf11 : QGateWellFormed (1 + 1) idGate01 := qGateWellFormed_idGate01
    have hGM11 : gateMatrix (1 + 1) idGate01 = 1 := gateMatrix_idGate01
    have hgate : ∀ ψ : Fin (2 ^ (1 + 1)) → ℂ,
        applyGate (1 + 1) idGate01 ψ = ψ := by
      intro ψ
      rw [applyGate_eq_gateMatrix_mulVec hwf11 ψ, hGM11, Matrix.one_mulVec]
    have hcirc : applyCircuit (1 + 1) [idGate01, idGate01] (bqpInitState [true] 1)
        = bqpInitState [true] 1 := by
      show applyGate (1 + 1) idGate01 (applyGate (1 + 1) idGate01 _) = _
      rw [hgate, hgate]
    rw [hcirc]
    simp only [acceptProb, bqpInitState, tensorProd, basisState, zeroState, qNumOf, qBit]
    rw [Fintype.sum_eq_single 1 ?h0]
    · norm_num [Fin.ext_iff]
    · intro x hx
      fin_cases x <;> simp_all [Fin.ext_iff]

/-- The `e^{iπ/4} H` gate on qubit `0` (spectator qubit `1`), encoded with
denominators `2`. -/
def omegaGate01 : QGate :=
  (0, 1, Cslib.Complexity.Classes.QuantumGates.entriesOf
    (Cslib.Complexity.Classes.QuantumGates.onLow
      Cslib.Complexity.Classes.QuantumGates.omegaH))

/-- The `X` gate on qubit `0` (spectator qubit `1`). -/
def xGate01 : QGate :=
  (0, 1, Cslib.Complexity.Classes.QuantumGates.entriesOf
    (Cslib.Complexity.Classes.QuantumGates.onLow
      Cslib.Complexity.Classes.QuantumGates.xGate))

private theorem ampSum_singleton_xGate01 (s u : Fin (2 ^ 2)) :
    ampSum 2 [xGate01] s u = gateMatrix 2 xGate01 s u := by
  show (∑ v, ampSum 2 [] s v * gateMatrix 2 xGate01 v u) = _
  simp only [show ∀ a b : Fin (2 ^ 2), ampSum 2 [] a b = if a = b then 1 else 0
    from fun a b => rfl]
  simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]

private theorem ampSum_singleton_omegaGate01 (s u : Fin (2 ^ 2)) :
    ampSum 2 [omegaGate01] s u = gateMatrix 2 omegaGate01 s u := by
  show (∑ v, ampSum 2 [] s v * gateMatrix 2 omegaGate01 v u) = _
  simp only [show ∀ a b : Fin (2 ^ 2), ampSum 2 [] a b = if a = b then 1 else 0
    from fun a b => rfl]
  simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]

private theorem gateMatrix_xGate01_1_0 : gateMatrix 2 xGate01 1 0 = 1 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_1_1 : gateMatrix 2 xGate01 1 1 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (1 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_1_2 : gateMatrix 2 xGate01 1 2 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (2 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_1_3 : gateMatrix 2 xGate01 1 3 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (3 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_0_0 : gateMatrix 2 xGate01 0 0 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (0 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_2_0 : gateMatrix 2 xGate01 2 0 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (2 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_xGate01_3_0 : gateMatrix 2 xGate01 3 0 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ xGate01.1 → k.val ≠ xGate01.2.1 →
      qBit k.val (3 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [xGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, xGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.xGate,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_0_0 :
    gateMatrix 2 omegaGate01 0 0 = (⟨1/2, 1/2⟩ : ℂ) := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (0 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_1_0 :
    gateMatrix 2 omegaGate01 1 0 = (⟨1/2, 1/2⟩ : ℂ) := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_2_0 : gateMatrix 2 omegaGate01 2 0 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (2 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_3_0 : gateMatrix 2 omegaGate01 3 0 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (3 : Fin (2 ^ 2)).val = qBit k.val (0 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_1_1 :
    gateMatrix 2 omegaGate01 1 1 = (⟨-1/2, -1/2⟩ : ℂ) := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (1 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_1_2 : gateMatrix 2 omegaGate01 1 2 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (2 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem gateMatrix_omegaGate01_1_3 : gateMatrix 2 omegaGate01 1 3 = 0 := by
  have hagree : (∀ k : Fin 2, k.val ≠ omegaGate01.1 → k.val ≠ omegaGate01.2.1 →
      qBit k.val (1 : Fin (2 ^ 2)).val = qBit k.val (3 : Fin (2 ^ 2)).val) := by
    intro k hk0 hk1
    simp only [omegaGate01] at hk0 hk1
    fin_cases k <;> simp_all
  simp only [gateMatrix, ite_eq_left hagree, omegaGate01]
  simp only [Cslib.Complexity.Classes.QuantumGates.matrixOfEntries_entriesOf]
  norm_num [qBit, Cslib.Complexity.Classes.QuantumGates.complexOfGRatMatrix,
    Cslib.Complexity.Classes.QuantumGates.onLow,
    Cslib.Complexity.Classes.QuantumGates.omegaH,
    Cslib.Complexity.Classes.QuantumGates.toComplex_gaussRatEnc, Complex.ext_iff]

private theorem qGateWellFormed_omegaGate01 : QGateWellFormed 2 omegaGate01 := by
  unfold omegaGate01
  exact Cslib.Complexity.Classes.QuantumGates.qGateWellFormed_onLow
    Cslib.Complexity.Classes.QuantumGates.omegaH
    Cslib.Complexity.Classes.QuantumGates.omegaH_unitary
    (by decide) (by decide)

private theorem bqpInitState_false_one (s : Fin (2 ^ (1 + 1))) :
    bqpInitState [false] 1 s = if s = 0 then 1 else 0 := by
  fin_cases s <;> norm_num [bqpInitState, tensorProd, basisState, zeroState, qNumOf, qBit]

private theorem apply_omega_basis0_0 :
    (gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1) 0 =
      (⟨1/2, 1/2⟩ : ℂ) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single 0]
  · rw [bqpInitState_false_one]
    simp only [ite_true, mul_one]
    exact gateMatrix_omegaGate01_0_0
  · intro t ht
    rw [bqpInitState_false_one]
    simp [ht]

private theorem apply_omega_basis0_1 :
    (gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1) 1 =
      (⟨1/2, 1/2⟩ : ℂ) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single 0]
  · rw [bqpInitState_false_one]
    simp only [ite_true, mul_one]
    exact gateMatrix_omegaGate01_1_0
  · intro t ht
    rw [bqpInitState_false_one]
    simp [ht]

private theorem apply_omega_basis0_2 :
    (gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1) 2 = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single 0]
  · rw [bqpInitState_false_one]
    simp only [ite_true, mul_one]
    exact gateMatrix_omegaGate01_2_0
  · intro t ht
    rw [bqpInitState_false_one]
    simp [ht]

private theorem apply_omega_basis0_3 :
    (gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1) 3 = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single 0]
  · rw [bqpInitState_false_one]
    simp only [ite_true, mul_one]
    exact gateMatrix_omegaGate01_3_0
  · intro t ht
    rw [bqpInitState_false_one]
    simp [ht]

/-- Nonvacuity, order and denominators: the two orders of the noncommuting
pair `e^{iπ/4} H` then `X` versus `X` then `e^{iπ/4} H` give different
off-diagonal amplitudes `(1+i)/2` and `-(1+i)/2`, the `e^{iπ/4} H` gate has
a non-unit encoded denominator, and its acceptance on input `[false]` is
`1/2`, so the denominator-scaled acceptance is `D²/2 ≠ 1/2`. -/
theorem pathSum_order_denominator_check :
    ampSum 2 [omegaGate01, xGate01] 1 0 = (⟨1/2, 1/2⟩ : ℂ) ∧
      ampSum 2 [xGate01, omegaGate01] 1 0 = (⟨-1/2, -1/2⟩ : ℂ) ∧
      1 < gateDenom omegaGate01 ∧
      (([omegaGate01].map gateDenom).prod : ℝ) ^ 2 *
        acceptProb (applyCircuit (1 + 1) [omegaGate01]
          (bqpInitState [false] 1)) = (gateDenom omegaGate01 : ℝ) ^ 2 / 2 := by
  refine ⟨?h1, ?h2, ?h3, ?h4⟩
  · show (∑ u, ampSum 2 [xGate01] 1 u * gateMatrix 2 omegaGate01 u 0) = _
    simp only [ampSum_singleton_xGate01]
    have hsum : (∑ u : Fin (2 ^ 2),
        gateMatrix 2 xGate01 1 u * gateMatrix 2 omegaGate01 u 0)
        = gateMatrix 2 xGate01 1 0 * gateMatrix 2 omegaGate01 0 0
        + gateMatrix 2 xGate01 1 1 * gateMatrix 2 omegaGate01 1 0
        + gateMatrix 2 xGate01 1 2 * gateMatrix 2 omegaGate01 2 0
        + gateMatrix 2 xGate01 1 3 * gateMatrix 2 omegaGate01 3 0 :=
      Fin.sum_univ_four _
    rw [hsum, gateMatrix_xGate01_1_0, gateMatrix_xGate01_1_1,
      gateMatrix_xGate01_1_2, gateMatrix_xGate01_1_3,
      gateMatrix_omegaGate01_0_0, gateMatrix_omegaGate01_1_0,
      gateMatrix_omegaGate01_2_0, gateMatrix_omegaGate01_3_0]
    norm_num [Complex.ext_iff]
  · show (∑ u, ampSum 2 [omegaGate01] 1 u * gateMatrix 2 xGate01 u 0) = _
    simp only [ampSum_singleton_omegaGate01]
    have hsum : (∑ u : Fin (2 ^ 2),
        gateMatrix 2 omegaGate01 1 u * gateMatrix 2 xGate01 u 0)
        = gateMatrix 2 omegaGate01 1 0 * gateMatrix 2 xGate01 0 0
        + gateMatrix 2 omegaGate01 1 1 * gateMatrix 2 xGate01 1 0
        + gateMatrix 2 omegaGate01 1 2 * gateMatrix 2 xGate01 2 0
        + gateMatrix 2 omegaGate01 1 3 * gateMatrix 2 xGate01 3 0 :=
      Fin.sum_univ_four _
    rw [hsum, gateMatrix_omegaGate01_1_0, gateMatrix_omegaGate01_1_1,
      gateMatrix_omegaGate01_1_2, gateMatrix_omegaGate01_1_3,
      gateMatrix_xGate01_0_0, gateMatrix_xGate01_1_0,
      gateMatrix_xGate01_2_0, gateMatrix_xGate01_3_0]
    norm_num [Complex.ext_iff]
  · have hmem_entry :
        Cslib.Complexity.Classes.QuantumGates.gaussRatEnc (1/2) (1/2)
          ∈ omegaGate01.2.2 := by
      simp [omegaGate01,
        Cslib.Complexity.Classes.QuantumGates.entriesOf,
        Cslib.Complexity.Classes.QuantumGates.onLow,
        Cslib.Complexity.Classes.QuantumGates.omegaH]
    have hfactor :
        ratDenom
            (Cslib.Complexity.Classes.QuantumGates.gaussRatEnc (1/2) (1/2)).1 *
            ratDenom
              (Cslib.Complexity.Classes.QuantumGates.gaussRatEnc (1/2) (1/2)).2 =
          4 := by
      norm_num [ratDenom, Cslib.Complexity.Classes.QuantumGates.gaussRatEnc,
        Cslib.Complexity.Classes.QuantumGates.ratEncOfRat]
    have hmem4 : (4 : ℕ)
        ∈ omegaGate01.2.2.map (fun p => ratDenom p.1 * ratDenom p.2) := by
      rw [List.mem_map]
      exact ⟨Cslib.Complexity.Classes.QuantumGates.gaussRatEnc (1/2) (1/2),
        hmem_entry, hfactor⟩
    have hall :
        ∀ x ∈ omegaGate01.2.2.map (fun p => ratDenom p.1 * ratDenom p.2),
          1 ≤ x := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      simp only [ratDenom]
      have h1 : (1 : ℕ) ≤ max p.1.2.2 1 := Nat.le_max_right _ _
      have h2 : (1 : ℕ) ≤ max p.2.2.2 1 := Nat.le_max_right _ _
      calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
        _ ≤ max p.1.2.2 1 * max p.2.2.2 1 := Nat.mul_le_mul h1 h2
    have hle :
        4 ≤ (omegaGate01.2.2.map (fun p => ratDenom p.1 * ratDenom p.2)).prod :=
      List.single_le_prod hall 4 hmem4
    have hden : gateDenom omegaGate01
        = (omegaGate01.2.2.map (fun p => ratDenom p.1 * ratDenom p.2)).prod := by
      simp only [gateDenom]
    omega
  · have hprod : (([omegaGate01].map gateDenom).prod : ℝ)
        = (gateDenom omegaGate01 : ℝ) := by
      simp only [List.map_singleton, List.prod_singleton]
    rw [hprod]
    have hwf : QGateWellFormed (1 + 1) omegaGate01 := qGateWellFormed_omegaGate01
    have hcirc : applyCircuit (1 + 1) [omegaGate01] (bqpInitState [false] 1)
        = gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1 := by
      show applyGate (1 + 1) omegaGate01 (bqpInitState [false] 1) = _
      rw [applyGate_eq_gateMatrix_mulVec hwf]
    rw [hcirc]
    have hacc : acceptProb
        (gateMatrix (1 + 1) omegaGate01 *ᵥ bqpInitState [false] 1) = 1 / 2 := by
      simp only [acceptProb]
      have hsum : (∑ s : Fin (2 ^ (1 + 1)),
          (if qBit 0 s.val = 1 then
            (starRingEnd ℂ ((gateMatrix (1 + 1) omegaGate01 *ᵥ
              bqpInitState [false] 1) s) *
              ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                bqpInitState [false] 1) s)).re
          else (0 : ℝ)))
          = (if qBit 0 (0 : Fin (2 ^ (1 + 1))).val = 1 then
              (starRingEnd ℂ ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                bqpInitState [false] 1) 0) *
                ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                  bqpInitState [false] 1) 0)).re
            else (0 : ℝ))
          + (if qBit 0 (1 : Fin (2 ^ (1 + 1))).val = 1 then
              (starRingEnd ℂ ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                bqpInitState [false] 1) 1) *
                ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                  bqpInitState [false] 1) 1)).re
            else (0 : ℝ))
          + (if qBit 0 (2 : Fin (2 ^ (1 + 1))).val = 1 then
              (starRingEnd ℂ ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                bqpInitState [false] 1) 2) *
                ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                  bqpInitState [false] 1) 2)).re
            else (0 : ℝ))
          + (if qBit 0 (3 : Fin (2 ^ (1 + 1))).val = 1 then
              (starRingEnd ℂ ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                bqpInitState [false] 1) 3) *
                ((gateMatrix (1 + 1) omegaGate01 *ᵥ
                  bqpInitState [false] 1) 3)).re
            else (0 : ℝ)) :=
        Fin.sum_univ_four _
      rw [hsum, apply_omega_basis0_0, apply_omega_basis0_1,
        apply_omega_basis0_2, apply_omega_basis0_3]
      have hq0 : qBit 0 (0 : Fin (2 ^ (1 + 1))).val = 0 := by decide
      have hq1 : qBit 0 (1 : Fin (2 ^ (1 + 1))).val = 1 := by decide
      have hq2 : qBit 0 (2 : Fin (2 ^ (1 + 1))).val = 0 := by decide
      have hq3 : qBit 0 (3 : Fin (2 ^ (1 + 1))).val = 1 := by decide
      rw [hq0, hq1, hq2, hq3]
      norm_num [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [hacc]
    ring

end Cslib.Complexity.Classes.Tests
