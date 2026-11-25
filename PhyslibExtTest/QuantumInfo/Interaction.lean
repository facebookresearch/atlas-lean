/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Interaction

/-!
# Tests: quantum interaction semantics
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.Interaction

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Interaction

#print axioms value_zero
#print axioms value_le_iff

/-- The always-accept two-outcome measurement. -/
def acceptAllPOVM (d : Type*) [Fintype d] [DecidableEq d] : POVM Bool d where
  mats := fun b => if b then 1 else 0
  nonneg := by
    intro b
    cases b with
    | false => simpa using le_refl (0 : HermitianMat _ _)
    | true =>
      simp [HermitianMat.zero_le_iff]
  normalized := by
    simp [Fintype.sum_bool]

/-- A constant verifier that accepts everything in zero messages has
value `1` at every prover workspace, including the memoryless workspace
`Unit`. The value `0` at the empty workspace `Empty` is the
zero-dimensional artifact: no density operator exists there. -/
theorem value_zero_acceptAll :
    value (dV := Fin 2) (dM := Fin 2)
        { init := MState.pure (Ket.basis (0, 0)), step := fun i => i.elim0,
          accept := acceptAllPOVM (Fin 2 × Fin 2) } (Fin 2) = 1 ∧
      value (dV := Fin 2) (dM := Fin 2)
        { init := MState.pure (Ket.basis (0, 0)), step := fun i => i.elim0,
          accept := acceptAllPOVM (Fin 2 × Fin 2) } Unit = 1 ∧
      value (dV := Fin 2) (dM := Fin 2)
        { init := MState.pure (Ket.basis (0, 0)), step := fun i => i.elim0,
          accept := acceptAllPOVM (Fin 2 × Fin 2) } Empty = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [value_zero]
    have htr : (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M.trace = 1 :=
      MState.tr _
    apply Prob.ext
    show inner ℝ (1 : HermitianMat (Fin 2 × Fin 2) ℂ)
        (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M = 1
    rw [HermitianMat.one_inner, htr]
  · rw [value_zero]
    have htr : (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M.trace = 1 :=
      MState.tr _
    apply Prob.ext
    show inner ℝ (1 : HermitianMat (Fin 2 × Fin 2) ℂ)
        (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M = 1
    rw [HermitianMat.one_inner, htr]
  · apply value_of_isEmpty

#print axioms value_zero_acceptAll

noncomputable section

lemma ket_basis_prod (a b : Fin 2) :
    Ket.basis (a, b) = (Ket.basis a) ⊗ᵠ (Ket.basis b) := by
  ext ⟨i, j⟩
  simp only [Ket.prod, Ket.basis, Ket.apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

lemma pure_basis_prod (a b : Fin 2) :
    MState.pure (Ket.basis (a, b))
      = (MState.pure (Ket.basis a)) ⊗ᴹ (MState.pure (Ket.basis b)) := by
  rw [ket_basis_prod, MState.pure_prod_pure]

lemma prod_assoc_eq {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
    [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
    (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    ((ρ ⊗ᴹ σ) ⊗ᴹ τ).assoc = ρ ⊗ᴹ (σ ⊗ᴹ τ) :=
  (MState.prod_assoc ρ σ τ).symm

lemma prod_assoc'_eq {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
    [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
    (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ᴹ (σ ⊗ᴹ τ)).assoc' = (ρ ⊗ᴹ σ) ⊗ᴹ τ := by
  have h : ((ρ ⊗ᴹ σ) ⊗ᴹ τ).assoc = ρ ⊗ᴹ (σ ⊗ᴹ τ) :=
    (MState.prod_assoc ρ σ τ).symm
  rw [← h, MState.assoc'_assoc]

/-- Diagonal acceptance matrix for the message-is-`1` measurement. -/
def msgOneDiag : HermitianMat (Fin 2 × Fin 2) ℂ :=
  HermitianMat.diagonal ℂ fun p => if p.2 = 1 then (1 : ℝ) else 0

open scoped ComplexOrder in
lemma msgOneDiag_nonneg : 0 ≤ msgOneDiag := by
  rw [msgOneDiag, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat,
    Matrix.posSemidef_diagonal_iff]
  intro p
  by_cases h : p.2 = 1 <;> simp [h]

open scoped ComplexOrder in
lemma msgOneDiag_sub_nonneg : 0 ≤ 1 - msgOneDiag := by
  have h : (1 : HermitianMat (Fin 2 × Fin 2) ℂ) - msgOneDiag
      = HermitianMat.diagonal ℂ
        (1 - fun p : Fin 2 × Fin 2 => if p.2 = 1 then (1 : ℝ) else 0) := by
    rw [msgOneDiag, ← HermitianMat.diagonal_one, ← HermitianMat.diagonal_sub]
  rw [h, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat,
    Matrix.posSemidef_diagonal_iff]
  intro p
  simp only [Pi.sub_apply]
  by_cases hp : p.2 = 1 <;> simp [hp]

lemma inner_msgOneDiag_pure (q : Fin 2 × Fin 2) :
    inner ℝ msgOneDiag (MState.pure (Ket.basis q)).M
      = if q.2 = 1 then 1 else 0 := by
  rw [HermitianMat.inner_eq_re_trace]
  have hρ : ∀ i : Fin 2 × Fin 2, (MState.pure (Ket.basis q)).m i i
      = if q = i then 1 else 0 := by
    intro i
    rw [MState.pure_apply]
    simp only [Ket.basis, Ket.coe_fun_eq]
    by_cases h : q = i <;> simp [h]
  simp only [msgOneDiag, HermitianMat.diagonal_mat, Matrix.trace,
    Matrix.diag_apply, Matrix.diagonal_mul, MState.mat_M, hρ, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases h : q.2 = 1 <;> simp [h]

/-- The two-outcome measurement accepting exactly when the message qubit
(the second component) is `1`. -/
def msgOnePOVM : POVM Bool (Fin 2 × Fin 2) :=
  { mats := fun b => if b then msgOneDiag else 1 - msgOneDiag
    nonneg := by
      intro b
      cases b with
      | false => simpa using msgOneDiag_sub_nonneg
      | true => simpa using msgOneDiag_nonneg
    normalized := by
      simp }

/-- A one-round verifier that does nothing in its round. -/
def idVerifier1 : Verifier 1 (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis (0, 0))
  step := fun _ => CPTPMap.id
  accept := msgOnePOVM

/-- A one-round verifier that resets both registers to `|00⟩` in its round. -/
def resetVerifier1 : Verifier 1 (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis (0, 0))
  step := fun _ => CPTPMap.replacement (MState.pure (Ket.basis (0, 0)))
  accept := msgOnePOVM

/-- A prover whose single channel writes `|1⟩` to the message register. -/
def writeOneProver : Prover 1 (Fin 2) (Fin 2) where
  init := MState.pure (Ket.basis 0)
  step := fun _ => CPTPMap.replacement (MState.pure (Ket.basis (1, 0)))

/-- One-round order check: the prover's write survives an idle verifier
round (acceptance `1`) but is erased by a resetting verifier round applied
after it (acceptance `0`, final state `|00⟩`). With the opposite round
order the second value would be `1`. -/
theorem one_round_order_check :
    acceptProb idVerifier1 writeOneProver = 1 ∧
      acceptProb resetVerifier1 writeOneProver = 0 ∧
      finalState resetVerifier1 writeOneProver =
        MState.pure (Ket.basis (0, 0)) := by
  have hfin_id : finalState idVerifier1 writeOneProver
      = MState.pure (Ket.basis (0, 1)) := by
    have hVinit : idVerifier1.init = MState.pure (Ket.basis (0, 0)) := rfl
    have hPinit : writeOneProver.init = MState.pure (Ket.basis 0) := rfl
    have hVi : idVerifier1.step (Fin.last 0) = CPTPMap.id := rfl
    have hPi : writeOneProver.step (Fin.last 0)
        = CPTPMap.replacement (MState.pure (Ket.basis (1, 0))) := rfl
    have hrun : run 1 idVerifier1.step writeOneProver.step
        = PhyslibExt.QuantumInfo.Interaction.round (idVerifier1.step (Fin.last 0))
            (writeOneProver.step (Fin.last 0)) ∘ₘ CPTPMap.id := rfl
    have hsplit00 : MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))
        = (MState.pure (Ket.basis 0)) ⊗ᴹ (MState.pure (Ket.basis 0)) :=
      pure_basis_prod 0 0
    have hsplit10 : MState.pure (Ket.basis ((1, 0) : Fin 2 × Fin 2))
        = (MState.pure (Ket.basis 1)) ⊗ᴹ (MState.pure (Ket.basis 0)) :=
      pure_basis_prod 1 0
    unfold finalState
    rw [hrun, hVinit, hPinit, hVi, hPi, hsplit00, hsplit10]
    unfold PhyslibExt.QuantumInfo.Interaction.round
    simp only [CPTPMap.compose_eq, CPTPMap.id_MState,
      CPTPMap.assoc_eq_MState_assoc, CPTPMap.assoc'_eq_MState_assoc',
      CPTPMap.traceRight_eq_MState_traceRight, prod_assoc_eq,
      CPTPMap.prod_apply_prod, CPTPMap.replacement_apply, prod_assoc'_eq,
      MState.traceRight_prod_eq]
    rw [← pure_basis_prod]
  have hfin_reset : finalState resetVerifier1 writeOneProver
      = MState.pure (Ket.basis (0, 0)) := by
    have hVinit : resetVerifier1.init = MState.pure (Ket.basis (0, 0)) := rfl
    have hPinit : writeOneProver.init = MState.pure (Ket.basis 0) := rfl
    have hVi : resetVerifier1.step (Fin.last 0)
        = CPTPMap.replacement (MState.pure (Ket.basis (0, 0))) := rfl
    have hPi : writeOneProver.step (Fin.last 0)
        = CPTPMap.replacement (MState.pure (Ket.basis (1, 0))) := rfl
    have hrun : run 1 resetVerifier1.step writeOneProver.step
        = PhyslibExt.QuantumInfo.Interaction.round
            (resetVerifier1.step (Fin.last 0))
            (writeOneProver.step (Fin.last 0)) ∘ₘ CPTPMap.id := rfl
    have hsplit00 : MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))
        = (MState.pure (Ket.basis 0)) ⊗ᴹ (MState.pure (Ket.basis 0)) :=
      pure_basis_prod 0 0
    have hsplit10 : MState.pure (Ket.basis ((1, 0) : Fin 2 × Fin 2))
        = (MState.pure (Ket.basis 1)) ⊗ᴹ (MState.pure (Ket.basis 0)) :=
      pure_basis_prod 1 0
    unfold finalState
    rw [hrun, hVinit, hPinit, hVi, hPi, hsplit00, hsplit10]
    unfold PhyslibExt.QuantumInfo.Interaction.round
    simp only [CPTPMap.compose_eq, CPTPMap.id_MState,
      CPTPMap.assoc_eq_MState_assoc, CPTPMap.assoc'_eq_MState_assoc',
      CPTPMap.traceRight_eq_MState_traceRight, prod_assoc_eq,
      CPTPMap.prod_apply_prod, CPTPMap.replacement_apply, prod_assoc'_eq,
      MState.traceRight_prod_eq]
  have haccept_id : idVerifier1.accept = msgOnePOVM := rfl
  have haccept_reset : resetVerifier1.accept = msgOnePOVM := rfl
  refine ⟨?_, ?_, hfin_reset⟩
  · unfold acceptProb
    rw [haccept_id, hfin_id]
    apply Prob.ext
    show inner ℝ msgOneDiag
        (MState.pure (Ket.basis ((0, 1) : Fin 2 × Fin 2))).M = 1
    rw [inner_msgOneDiag_pure]
    rfl
  · unfold acceptProb
    rw [haccept_reset, hfin_reset]
    apply Prob.ext
    show inner ℝ msgOneDiag
        (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M = 0
    rw [inner_msgOneDiag_pure]
    rfl

#print axioms one_round_order_check

end

end PhyslibExtTest.QuantumInfo.Interaction
