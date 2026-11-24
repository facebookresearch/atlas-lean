/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PathSum

/-!
# Tests: path-sum expansion and integer gap
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes

#print axioms applyCircuit_eq_ampSum
#print axioms acceptProb_gap

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
identity circuit on input `[true]` has gap numerator `1` at scale `1`. -/
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

end Cslib.Complexity.Classes.Tests
