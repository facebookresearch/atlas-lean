/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.QIP
public import PhyslibExtTest.QuantumInfo.Interaction

/-!
# Tests: QIP acceptance predicates
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.QIP

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Interaction PhyslibExt.QuantumInfo.QIP

#print axioms acceptProb_zero
#print axioms complete_iff_exists_value
#print axioms sound_iff_forall_value

/-- The always-reject two-outcome measurement. -/
def rejectAllPOVM (d : Type*) [Fintype d] [DecidableEq d] : POVM Bool d where
  mats := fun b => if b then 0 else 1
  nonneg := by
    intro b
    cases b with
    | false =>
      simp [HermitianMat.zero_le_iff]
    | true =>
      simpa using le_refl (0 : HermitianMat _ _)
  normalized := by
    simp [Fintype.sum_bool]

noncomputable section

/-- A verifier that accepts every outcome, with identity steps. -/
def acceptAllV (k : ℕ) : Verifier k (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis (0, 0))
  step := fun _ => CPTPMap.id
  accept := PhyslibExtTest.QuantumInfo.Interaction.acceptAllPOVM (Fin 2 × Fin 2)

/-- A verifier that rejects every outcome, with identity steps. -/
def rejectAllV (k : ℕ) : Verifier k (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis (0, 0))
  step := fun _ => CPTPMap.id
  accept := rejectAllPOVM (Fin 2 × Fin 2)

/-- The accept-all verifier accepts with probability `1` against every prover. -/
theorem acceptAll_acceptProb (k : ℕ) (dP : Type*) [Fintype dP] [DecidableEq dP]
    (P : Prover k (Fin 2) dP) :
    acceptProb (acceptAllV k) P = 1 := by
  unfold acceptProb
  apply Prob.ext
  show inner ℝ (1 : HermitianMat (Fin 2 × Fin 2) ℂ)
      (finalState (acceptAllV k) P).M = 1
  have htr : (finalState (acceptAllV k) P).M.trace = 1 := MState.tr _
  rw [HermitianMat.one_inner, htr]

#print axioms acceptAll_acceptProb

/-- The reject-all verifier accepts with probability `0` against every prover. -/
theorem rejectAll_acceptProb (k : ℕ) (dP : Type*) [Fintype dP] [DecidableEq dP]
    (P : Prover k (Fin 2) dP) :
    acceptProb (rejectAllV k) P = 0 := by
  unfold acceptProb
  apply Prob.ext
  show inner ℝ (0 : HermitianMat (Fin 2 × Fin 2) ℂ)
      (finalState (rejectAllV k) P).M = 0
  exact HermitianMat.inner_zero_left _

#print axioms rejectAll_acceptProb

/-- The accept-all verifier is complete but not sound. -/
theorem complete_acceptAll_not_sound (k : ℕ) :
    Complete (acceptAllV k) ∧ ¬ Sound (acceptAllV k) := by
  have h1 : ((1 : Prob) : ℝ) = 1 := Prob.coe_one
  haveI : Nonempty (MState Unit) := inferInstance
  constructor
  · refine ⟨Unit, inferInstance, inferInstance,
      ⟨Classical.choice inferInstance, fun _ => CPTPMap.id⟩, ?_⟩
    rw [acceptAll_acceptProb, h1]
    norm_num
  · intro hS
    have h := hS Unit ⟨Classical.choice inferInstance, fun _ => CPTPMap.id⟩
    rw [acceptAll_acceptProb, h1] at h
    norm_num at h

#print axioms complete_acceptAll_not_sound

/-- The reject-all verifier is sound but not complete. -/
theorem sound_rejectAll_not_complete (k : ℕ) :
    Sound (rejectAllV k) ∧ ¬ Complete (rejectAllV k) := by
  have h0 : ((0 : Prob) : ℝ) = 0 := Prob.coe_zero
  constructor
  · intro dP _ _ P
    rw [rejectAll_acceptProb, h0]
    norm_num
  · rintro ⟨dP, _, _, P, h⟩
    rw [rejectAll_acceptProb, h0] at h
    norm_num at h

#print axioms sound_rejectAll_not_complete

/-- No prover strategies exist at the empty workspace, while the memoryless
workspace `Unit` has strategies. -/
theorem prover_empty_unit (k : ℕ) :
    IsEmpty (Prover k (Fin 2) Empty) ∧ Nonempty (Prover k (Fin 2) Unit) := by
  constructor
  · haveI : IsEmpty (MState Empty) :=
      ⟨fun ρ => (inferInstance : IsEmpty Empty).elim
        (Classical.choice ρ.nonempty)⟩
    exact Function.isEmpty (fun P => P.init)
  · haveI : Nonempty (MState Unit) := inferInstance
    exact ⟨⟨Classical.choice inferInstance, fun _ => CPTPMap.id⟩⟩

#print axioms prover_empty_unit

/-- The accept-all verifier has value `0` at the empty workspace and `1` at `Unit`. -/
theorem value_acceptAll_empty_unit (k : ℕ) :
    value (acceptAllV k) Empty = 0 ∧ value (acceptAllV k) Unit = 1 := by
  constructor
  · apply value_of_isEmpty
  · haveI := (prover_empty_unit k).2
    unfold value
    simp only [acceptAll_acceptProb, ciSup_const]

#print axioms value_acceptAll_empty_unit

/-- A zero-round verifier measuring the message qubit of a basis-state input. -/
def msgVerifier (q : Fin 2 × Fin 2) : Verifier 0 (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis q)
  step := fun i => i.elim0
  accept := PhyslibExtTest.QuantumInfo.Interaction.msgOnePOVM

/-- At zero rounds, the message-qubit verifier accepts input `|01⟩` with probability
`1` and `|00⟩` with probability `0`, against every prover and workspace. -/
theorem msgVerifier_zero_accept (dP : Type*) [Fintype dP] [DecidableEq dP]
    (P : Prover 0 (Fin 2) dP) :
    acceptProb (msgVerifier (0, 1)) P = 1 ∧
      acceptProb (msgVerifier (0, 0)) P = 0 := by
  constructor
  · rw [acceptProb_zero]
    apply Prob.ext
    show inner ℝ PhyslibExtTest.QuantumInfo.Interaction.msgOneDiag
        (MState.pure (Ket.basis ((0, 1) : Fin 2 × Fin 2))).M = 1
    rw [PhyslibExtTest.QuantumInfo.Interaction.inner_msgOneDiag_pure]
    rfl
  · rw [acceptProb_zero]
    apply Prob.ext
    show inner ℝ PhyslibExtTest.QuantumInfo.Interaction.msgOneDiag
        (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M = 0
    rw [PhyslibExtTest.QuantumInfo.Interaction.inner_msgOneDiag_pure]
    rfl

#print axioms msgVerifier_zero_accept

end

end PhyslibExtTest.QuantumInfo.QIP
