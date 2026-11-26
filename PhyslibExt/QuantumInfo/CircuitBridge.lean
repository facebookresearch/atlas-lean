/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Channels
public import CSLibExt.Computability.Complexity.QuantumGates.CircuitMatrix

/-!
# From circuit vectors to density operators

## i. Overview

A unit circuit vector on `v + m` qubits, read as a density operator on
the register pair of `qubitSplit v m`; a gate list as a unitary channel
on that pair, which acts on such states exactly as `applyCircuit` acts on
the vector when every gate is well formed; and the computational-basis
measurement of global qubit `0`, whose probability on these states is the
circuit acceptance probability.

## ii. Key results

* `circuitChannel_vecState`: the channel of a well-formed gate list
  sends the state of a vector to the state of its circuit image.
* `outputPOVM_measure_vecState`: measuring qubit `0` of the state of a
  unit vector gives the circuit acceptance probability.

## iii. Table of contents

* `ketOfVec`, `vecState`: vectors as kets and states.
* `circuitUnitary`, `circuitChannel`: gate lists as channels.
* `outputProj`, `outputPOVM`: the acceptance measurement.

## iv. References

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (density
operators of pure states) and Chapter 4 (quantum circuits).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.CircuitBridge

open Cslib.Complexity.Classes

/-- **Ket of a unit circuit vector.** The ket whose coefficients are those of a circuit vector
of squared norm `1`. -/
def ketOfVec {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) (hψ : sqNorm ψ = 1) : Ket (Fin (2 ^ N)) where
  vec := ψ
  normalized' := by
    have hnorm : ∀ z : ℂ, (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
      intro z
      have h2 : starRingEnd ℂ z * z = ((Complex.normSq z : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
      rw [h2, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp only [sqNorm] at hψ
    trans ∑ s : Fin (2 ^ N), (starRingEnd ℂ (ψ s) * ψ s).re
    · exact Finset.sum_congr rfl (fun s _ => (hnorm (ψ s)).symm)
    · exact hψ

lemma ketOfVec_apply {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) (hψ : sqNorm ψ = 1) (s : Fin (2 ^ N)) :
    ketOfVec ψ hψ s = ψ s :=
  rfl

/-- **State of a circuit vector.** For a unit vector on `v + m` qubits, its pure state, read on
the register pair of `qubitSplit v m`; for any other vector, the maximally mixed state. -/
noncomputable def vecState (v m : ℕ) (ψ : Fin (2 ^ (v + m)) → ℂ) :
    MState (Fin (2 ^ v) × Fin (2 ^ m)) :=
  if h : sqNorm ψ = 1 then (MState.pure (ketOfVec ψ h)).relabel (qubitSplit v m) else default

lemma vecState_of_sqNorm_eq_one {v m : ℕ} {ψ : Fin (2 ^ (v + m)) → ℂ} (hψ : sqNorm ψ = 1) :
    vecState v m ψ = (MState.pure (ketOfVec ψ hψ)).relabel (qubitSplit v m) := by
  rw [vecState, dite_eq_left hψ]

open scoped Classical in
/-- **Unitary of a gate list.** The circuit matrix of a gate list, as an element of the unitary
group, when every gate is well formed; the identity otherwise. -/
noncomputable def circuitUnitary (N : ℕ) (gs : List QGate) :
    Matrix.unitaryGroup (Fin (2 ^ N)) ℂ :=
  if h : ∀ g ∈ gs, QGateWellFormed N g then ⟨circuitMatrix N gs, circuitMatrix_mem_unitaryGroup h⟩
  else 1

/-- **Channel of a gate list.** The unitary channel of a gate list on the register pair of
`qubitSplit v m`; the identity channel when some gate is not well formed. -/
noncomputable def circuitChannel (v m : ℕ) (gs : List QGate) :
    CPTPMap (Fin (2 ^ v) × Fin (2 ^ m)) (Fin (2 ^ v) × Fin (2 ^ m)) :=
  CPTPMap.ofEquiv (qubitSplit v m).symm ∘ₘ CPTPMap.ofUnitary (circuitUnitary (v + m) gs) ∘ₘ
    CPTPMap.ofEquiv (qubitSplit v m)

private lemma uConj_pure_eq {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : Ket d) (U : Matrix.unitaryGroup d ℂ) (φ : Ket d)
    (hφ : ∀ i, φ i = (U.val.mulVec ψ) i) :
    (MState.pure ψ).uConj U = MState.pure φ := by
  apply MState.ext_m
  ext i j
  have hU : ((MState.pure ψ).uConj U).m
      = U.val * (MState.pure ψ).m * U.val.conjTranspose := by
    change ((MState.pure ψ).M.conj U.val).mat = _
    rw [HermitianMat.conj_apply_mat, MState.mat_M]
  rw [hU]
  have hentry : ∀ i j, (U.val * (MState.pure ψ).m * U.val.conjTranspose) i j
      = (U.val.mulVec ψ) i * (starRingEnd ℂ) ((U.val.mulVec ψ) j) := by
    intro i j
    simp only [Matrix.mul_apply, MState.pure_apply, Matrix.conjTranspose_apply,
      Matrix.mulVec_apply_eq_sum]
    have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
    simp only [hstar]
    have hinner : ∀ k, (∑ l, U.val i l * (ψ l * (starRingEnd ℂ) (ψ k)))
        = (∑ l, U.val i l * ψ l) * (starRingEnd ℂ) (ψ k) := by
      intro k
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hfac : (∑ k, (∑ l, U.val i l * (ψ l * (starRingEnd ℂ) (ψ k)))
          * (starRingEnd ℂ) (U.val j k))
        = (∑ l, U.val i l * ψ l)
          * (∑ k, (starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k)) := by
      have h1 : ∀ k, (∑ l, U.val i l * (ψ l * (starRingEnd ℂ) (ψ k)))
            * (starRingEnd ℂ) (U.val j k)
          = (∑ l, U.val i l * ψ l)
            * ((starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k)) := by
        intro k
        rw [hinner k, mul_assoc]
      calc (∑ k, (∑ l, U.val i l * (ψ l * (starRingEnd ℂ) (ψ k)))
              * (starRingEnd ℂ) (U.val j k))
          = ∑ k, (∑ l, U.val i l * ψ l)
              * ((starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k)) :=
            Finset.sum_congr rfl (fun k _ => h1 k)
        _ = (∑ l, U.val i l * ψ l)
            * (∑ k, (starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k)) := by
            rw [Finset.mul_sum]
    have hconj : (∑ k, (starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k))
        = (starRingEnd ℂ) (∑ k, U.val j k * ψ k) := by
      have hterm : ∀ k, (starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k)
          = (starRingEnd ℂ) (U.val j k * ψ k) := by
        intro k
        rw [map_mul, mul_comm ((starRingEnd ℂ) (ψ k)) _]
      calc (∑ k, (starRingEnd ℂ) (ψ k) * (starRingEnd ℂ) (U.val j k))
          = ∑ k, (starRingEnd ℂ) (U.val j k * ψ k) :=
            Finset.sum_congr rfl (fun k _ => hterm k)
        _ = (starRingEnd ℂ) (∑ k, U.val j k * ψ k) := by rw [map_sum]
    rw [hfac, hconj]
  rw [hentry i j, MState.pure_apply, hφ i, hφ j]

/-- **A gate-list channel acts as the circuit.** For a well-formed gate list and a unit vector
`ψ`, the channel of the list sends the state of `ψ` to the state of the circuit's image of
`ψ`. -/
lemma circuitChannel_vecState {v m : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (v + m) g) {ψ : Fin (2 ^ (v + m)) → ℂ}
    (hψ : sqNorm ψ = 1) :
    circuitChannel v m gs (vecState v m ψ) = vecState v m (applyCircuit (v + m) gs ψ) := by
  have hχ : sqNorm (applyCircuit (v + m) gs ψ) = 1 := by
    rw [sqNorm_applyCircuit, hψ]
    exact hgs
  have hUval : (circuitUnitary (v + m) gs).val = circuitMatrix (v + m) gs := by
    unfold circuitUnitary
    rw [dite_eq_left hgs]
  have hkeq : ⇑(ketOfVec ψ hψ) = ψ := funext (fun i => ketOfVec_apply ψ hψ i)
  have hχfun : ∀ i, ketOfVec (applyCircuit (v + m) gs ψ) hχ i
      = ((circuitUnitary (v + m) gs).val.mulVec (ketOfVec ψ hψ)) i := by
    intro i
    rw [ketOfVec_apply, hUval, hkeq, applyCircuit_eq_circuitMatrix_mulVec]
    exact hgs
  have hUconj := uConj_pure_eq (ketOfVec ψ hψ) (circuitUnitary (v + m) gs)
    (ketOfVec (applyCircuit (v + m) gs ψ) hχ) hχfun
  rw [vecState_of_sqNorm_eq_one hψ, vecState_of_sqNorm_eq_one hχ]
  simp only [circuitChannel, CPTPMap.compose_eq, CPTPMap.ofEquiv_apply,
    CPTPMap.ofUnitary_eq_conj]
  rw [MState.relabel_relabel, Equiv.symm_trans_self, MState.relabel_refl,
    hUconj, Equiv.symm_symm]

/-- **Projector onto the accepting basis states.** The diagonal projector onto the basis states
whose global qubit `0` is `1`. -/
noncomputable def outputProj (v m : ℕ) : HermitianMat (Fin (2 ^ v) × Fin (2 ^ m)) ℂ :=
  HermitianMat.diagonal ℂ fun p => if qBit 0 (qubitSplit v m p).val = 1 then (1 : ℝ) else 0

/-- **Measurement of the output qubit.** The computational-basis measurement of global qubit
`0`; the outcome `true` accepts. -/
noncomputable def outputPOVM (v m : ℕ) : POVM Bool (Fin (2 ^ v) × Fin (2 ^ m)) where
  mats b := if b then outputProj v m else 1 - outputProj v m
  nonneg := by
    intro b
    cases b
    · change 0 ≤ 1 - outputProj v m
      have hsub : (1 : HermitianMat (Fin (2 ^ v) × Fin (2 ^ m)) ℂ) - outputProj v m
          = HermitianMat.diagonal ℂ (1 - fun p =>
            if qBit 0 (qubitSplit v m p).val = 1 then (1 : ℝ) else 0) := by
        unfold outputProj
        rw [← HermitianMat.diagonal_one, ← HermitianMat.diagonal_sub]
      rw [hsub, HermitianMat.diagonal_nonneg]
      intro p
      change (0 : ℝ) ≤ 1 - (if qBit 0 (qubitSplit v m p).val = 1 then (1 : ℝ) else 0)
      by_cases h : qBit 0 (qubitSplit v m p).val = 1
      · simp only [ite_eq_left h, sub_self, le_refl]
      · simp only [ite_eq_right h, sub_zero, zero_le_one]
    · change 0 ≤ outputProj v m
      unfold outputProj
      rw [HermitianMat.diagonal_nonneg]
      intro p
      change (0 : ℝ) ≤ (if qBit 0 (qubitSplit v m p).val = 1 then (1 : ℝ) else 0)
      by_cases h : qBit 0 (qubitSplit v m p).val = 1
      · simp only [ite_eq_left h, zero_le_one]
      · simp only [ite_eq_right h, le_refl]
  normalized := by
    rw [Fintype.sum_bool]
    change outputProj v m + (1 - outputProj v m) = 1
    exact add_sub_cancel _ _

/-- **Born rule for the output qubit.** For a unit vector `ψ`, the probability that measuring
global qubit `0` of the state of `ψ` gives `true` is the acceptance probability of `ψ`. -/
lemma outputPOVM_measure_vecState {v m : ℕ} {ψ : Fin (2 ^ (v + m)) → ℂ} (hψ : sqNorm ψ = 1) :
    (((outputPOVM v m).measure (vecState v m ψ) true : Prob) : ℝ) =
      Cslib.Complexity.Classes.acceptProb ψ := by
  have hdiag : ∀ (f : Fin (2 ^ v) × Fin (2 ^ m) → ℝ) (i j : Fin (2 ^ v) × Fin (2 ^ m)),
      (HermitianMat.diagonal ℂ f).mat i j
        = if i = j then ((f i : ℝ) : ℂ) else 0 := by
    intro f i j
    rw [HermitianMat.diagonal_mat, Matrix.diagonal_apply]
    split_ifs <;> rfl
  have hre : ∀ z : ℂ, RCLike.re z = Complex.re z := fun z => rfl
  have hterm : ∀ (r : ℝ) (z : ℂ), (↑r * z).re = r * z.re := fun r z => by simp
  have hif : ∀ (c : Prop) [Decidable c] (X : ℝ),
      (if c then (1 : ℝ) else 0) * X = if c then X else 0 := by
    intro c _ X
    split_ifs <;> simp
  have hnorm : ∀ z : ℂ, (z * (starRingEnd ℂ) z).re = ((starRingEnd ℂ) z * z).re := by
    intro z
    rw [mul_comm]
  have hAcc : acceptProb ψ = ∑ s, (if qBit 0 s.val = 1 then
      ((ψ s) * (starRingEnd ℂ) (ψ s)).re else 0) := by
    unfold acceptProb
    refine Finset.sum_congr rfl fun s _ => ?_
    change (if qBit 0 s.val = 1 then ((starRingEnd ℂ) (ψ s) * ψ s).re else 0) =
      (if qBit 0 s.val = 1 then ((ψ s) * (starRingEnd ℂ) (ψ s)).re else 0)
    split_ifs with h
    · exact (hnorm (ψ s)).symm
    · rfl
  rw [vecState_of_sqNorm_eq_one hψ]
  change inner ℝ ((outputPOVM v m).mats true)
      (((MState.pure (ketOfVec ψ hψ)).relabel (qubitSplit v m)).M) = acceptProb ψ
  change inner ℝ (outputProj v m)
      (((MState.pure (ketOfVec ψ hψ)).relabel (qubitSplit v m)).M) = acceptProb ψ
  rw [HermitianMat.inner_eq_re_trace, MState.mat_M, MState.relabel_m]
  simp only [outputProj, Matrix.trace, Matrix.diag, Matrix.mul_apply, hdiag, ite_mul,
    zero_mul, Fintype.sum_ite_eq]
  rw [hre, Complex.re_sum]
  simp only [hterm, Matrix.submatrix_apply, MState.pure_apply, ketOfVec_apply, hif]
  rw [hAcc]
  exact Equiv.sum_comp (qubitSplit v m)
    (fun s => if qBit 0 s.val = 1 then ((ψ s) * (starRingEnd ℂ) (ψ s)).re else 0)

end PhyslibExt.QuantumInfo.CircuitBridge
