/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.CircuitBridge
public import CSLibExt.Computability.Complexity.QuantumGates.BQPAudit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Tests: circuit vectors as density operators
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.CircuitBridge

set_option autoImplicit false

open PhyslibExt.QuantumInfo.CircuitBridge Cslib.Complexity.Classes

#print axioms ketOfVec_apply
#print axioms vecState_of_sqNorm_eq_one
#print axioms circuitChannel_vecState
#print axioms outputPOVM_measure_vecState

/-- On input `[true]` with one ancilla, the acceptance probability is `1`. -/
private theorem acceptProb_init_single_true :
    acceptProb (bqpInitState [true] 1) = 1 := by
  simp only [acceptProb]
  show (Finset.sum Finset.univ (fun s : Fin 4 => if qBit 0 s.val = 1 then
      (starRingEnd Complex (bqpInitState [true] 1 s) *
        bqpInitState [true] 1 s).re else 0)) = 1
  rw [Fin.sum_univ_four]
  simp [bqpInitState, tensorProd, basisState, zeroState, qNumOf, qBit]

/-- On input `[false]` with one ancilla, the acceptance probability is `0`. -/
private theorem acceptProb_init_single_false :
    acceptProb (bqpInitState [false] 1) = 0 := by
  simp only [acceptProb]
  show (Finset.sum Finset.univ (fun s : Fin 4 => if qBit 0 s.val = 1 then
      (starRingEnd Complex (bqpInitState [false] 1 s) *
        bqpInitState [false] 1 s).re else 0)) = 0
  rw [Fin.sum_univ_four]
  simp [bqpInitState, tensorProd, basisState, zeroState, qNumOf, qBit]

/-- A gate with swapped qubits falls back to the identity unitary. -/
theorem circuitUnitary_swapped_is_one :
    circuitUnitary 2 [(1, 0, QuantumGates.xLowEntries)] = 1 := by
  have hnot : ¬ ∀ g ∈ [(1, 0, QuantumGates.xLowEntries)],
      QGateWellFormed 2 g := by
    intro hall
    have h1 := hall (1, 0, QuantumGates.xLowEntries) (by simp)
    unfold QGateWellFormed at h1
    simp at h1
  unfold circuitUnitary
  exact dite_eq_right hnot

#print axioms circuitUnitary_swapped_is_one

/-- Measuring the output qubit of the `[true]` initial state accepts. -/
theorem outputPOVM_measure_init_true :
    (((outputPOVM 2 0).measure (vecState 2 0 (bqpInitState [true] 1)) true :
      Prob) : ℝ) = 1 := by
  have hψ : sqNorm (bqpInitState [true] 1) = 1 := sqNorm_bqpInitState [true] 1
  have hbridge := outputPOVM_measure_vecState (v := 2) (m := 0)
    (ψ := bqpInitState [true] 1) hψ
  rw [hbridge]
  exact acceptProb_init_single_true

#print axioms outputPOVM_measure_init_true

/-- Measuring the output qubit of the `[false]` initial state rejects. -/
theorem outputPOVM_measure_init_false :
    (((outputPOVM 2 0).measure (vecState 2 0 (bqpInitState [false] 1)) true :
      Prob) : ℝ) = 0 := by
  have hψ : sqNorm (bqpInitState [false] 1) = 1 := sqNorm_bqpInitState [false] 1
  have hbridge := outputPOVM_measure_vecState (v := 2) (m := 0)
    (ψ := bqpInitState [false] 1) hψ
  rw [hbridge]
  exact acceptProb_init_single_false

#print axioms outputPOVM_measure_init_false

/-- With one ancilla qubit (`m = 1`), the state of the input `[true]` is the product of
`|1⟩` on the first register and `|0⟩` on the second: the input sits on the low-order
qubit, as `qubitSplit` and `tensorProd` read it. -/
theorem vecState_init_true_one_ancilla :
    vecState 1 1 (bqpInitState [true] 1) =
      MState.pure (Ket.basis 1) ⊗ᴹ MState.pure (Ket.basis 0) := by
  have hψ : sqNorm (m := 1 + 1) (bqpInitState [true] 1) = 1 := sqNorm_bqpInitState [true] 1
  rw [vecState_of_sqNorm_eq_one (v := 1) (m := 1) hψ, MState.relabel_pure,
    ← MState.pure_prod_pure]
  congr 1
  refine Ket.ext fun x => ?_
  obtain ⟨p, q⟩ := x
  rw [Ket.relabel_apply, ketOfVec_apply]
  refine (tensorProd_qubitSplit (v := 1) (m := 1) (basisState [true]) (zeroState 1) p q).trans ?_
  fin_cases p <;> fin_cases q <;>
    simp [basisState, zeroState, qNumOf, Ket.prod, Ket.basis, Ket.apply]

#print axioms vecState_init_true_one_ancilla

/-- After an `X` gate on the output qubit, the `[true]` state rejects. -/
theorem outputPOVM_measure_after_xLow :
    (((outputPOVM 2 0).measure (circuitChannel 2 0
      [(0, 1, QuantumGates.xLowEntries)]
      (vecState 2 0 (bqpInitState [true] 1))) true : Prob) : ℝ) = 0 := by
  have hψ : sqNorm (m := 2 + 0) (bqpInitState [true] 1) = 1 :=
    sqNorm_bqpInitState [true] 1
  have hwf : ∀ g ∈ [(0, 1, QuantumGates.xLowEntries)],
      QGateWellFormed (2 + 0) g := by
    intro g hg
    simp at hg
    subst hg
    unfold QuantumGates.xLowEntries
    exact QuantumGates.qGateWellFormed_onLow QuantumGates.xGate
      QuantumGates.xGate_unitary (by norm_num) (by omega)
  have hchan := circuitChannel_vecState (v := 2) (m := 0)
    (gs := [(0, 1, QuantumGates.xLowEntries)]) hwf (ψ := bqpInitState [true] 1)
    hψ
  rw [hchan]
  have hφ : sqNorm (applyCircuit (2 + 0) [(0, 1, QuantumGates.xLowEntries)]
      (bqpInitState [true] 1)) = 1 :=
    (sqNorm_applyCircuit hwf _).trans (sqNorm_bqpInitState [true] 1)
  have hmeas := outputPOVM_measure_vecState (v := 2) (m := 0)
    (ψ := applyCircuit (2 + 0) [(0, 1, QuantumGates.xLowEntries)]
      (bqpInitState [true] 1)) hφ
  rw [hmeas]
  have hsing : applyCircuit (2 + 0) [(0, 1, QuantumGates.xLowEntries)]
      (bqpInitState [true] 1) = applyGate (2 + 0)
      (0, 1, QuantumGates.xLowEntries) (bqpInitState [true] 1) := rfl
  have hacc : acceptProb (N := 2 + 0) (bqpInitState [true] 1) = 1 :=
    acceptProb_init_single_true
  rw [hsing, acceptProb_applyGate_xLow (by omega : 2 ≤ 2 + 0), hψ, hacc]
  norm_num

#print axioms outputPOVM_measure_after_xLow

end PhyslibExtTest.QuantumInfo.CircuitBridge
