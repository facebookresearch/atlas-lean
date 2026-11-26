/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
public import MathlibExt.Quantum.BlockEncoding

/-!
# Circuit matrices and register-pair layouts

The matrix of a whole gate list (the product of the gate matrices, first
gate rightmost), its unitarity on well-formed circuits, and the layout
equivalence that reads a register pair as low-order and high-order parts
of one register, matching `tensorProd` (`tensorProd_qubitSplit`). These are
the matrix-side facts a density-operator reading of circuit vectors consumes.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

/-- **Qubit layout of a register pair.** The pair `(p, q)` of a `v`-qubit register and an
`m`-qubit register is the index `p + 2 ^ v * q` of `v + m` qubits: the first register sits on
the low-order `v` qubits, as in `tensorProd`. -/
def qubitSplit (v m : ℕ) : Fin (2 ^ v) × Fin (2 ^ m) ≃ Fin (2 ^ (v + m)) :=
  (Equiv.prodComm _ _).trans (MathlibExt.Quantum.BlockEncoding.qubitAncillaEquiv v m)

theorem qubitSplit_apply_val (v m : ℕ) (p : Fin (2 ^ v)) (q : Fin (2 ^ m)) :
    (qubitSplit v m (p, q)).val = p.val + 2 ^ v * q.val :=
  rfl

theorem tensorProd_qubitSplit {v m : ℕ} (φ : Fin (2 ^ v) → ℂ) (χ : Fin (2 ^ m) → ℂ)
    (p : Fin (2 ^ v)) (q : Fin (2 ^ m)) :
    tensorProd φ χ (qubitSplit v m (p, q)) = φ p * χ q := by
  have hmod : (qubitSplit v m (p, q)).val % 2 ^ v = p.val := by
    rw [qubitSplit_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]
  have hdiv : (qubitSplit v m (p, q)).val / 2 ^ v = q.val := by
    rw [qubitSplit_apply_val, Nat.add_mul_div_left _ _ (Nat.two_pow_pos v),
      Nat.div_eq_of_lt p.isLt, zero_add]
  simp only [tensorProd]
  exact congrArg₂ (· * ·) (congrArg φ (Fin.ext hmod)) (congrArg χ (Fin.ext hdiv))

/-- **Matrix of a gate list.** The product of the gate matrices of a gate list, with the first
gate rightmost. -/
noncomputable def circuitMatrix (N : ℕ) (gs : List QGate) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  gs.foldl (fun M g => gateMatrix N g * M) 1

private theorem foldl_gateMatrix_mulVec {N : ℕ} (gs : List QGate)
    (M : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) (ψ : Fin (2 ^ N) → ℂ) :
    (∀ g ∈ gs, QGateWellFormed N g) →
    (gs.foldl (fun M g => gateMatrix N g * M) M).mulVec ψ =
      applyCircuit N gs (M.mulVec ψ) := by
  revert M ψ
  induction gs with
  | nil => intro M ψ _; simp only [applyCircuit, List.foldl_nil]
  | cons g gs ih =>
      intro M ψ hgs
      have hg : QGateWellFormed N g := hgs g (List.mem_cons.mpr (Or.inl rfl))
      have hgs' : ∀ g' ∈ gs, QGateWellFormed N g' :=
        fun g' hg' => hgs g' (List.mem_cons.mpr (Or.inr hg'))
      simp only [List.foldl_cons]
      rw [ih _ _ hgs', ← Matrix.mulVec_mulVec,
        ← applyGate_eq_gateMatrix_mulVec hg]
      simp only [applyCircuit, List.foldl_cons]

theorem applyCircuit_eq_circuitMatrix_mulVec {N : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g) (ψ : Fin (2 ^ N) → ℂ) :
    applyCircuit N gs ψ = (circuitMatrix N gs).mulVec ψ := by
  have h := foldl_gateMatrix_mulVec gs 1 ψ hgs
  rw [Matrix.one_mulVec] at h
  simp only [circuitMatrix]
  exact h.symm

private theorem foldl_gateMatrix_mem_unitary {N : ℕ} (gs : List QGate)
    (M : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) :
    (∀ g ∈ gs, QGateWellFormed N g) →
    M ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ →
    gs.foldl (fun M g => gateMatrix N g * M) M ∈
      Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  revert M
  induction gs with
  | nil => intro M _ hM; simpa only [List.foldl_nil] using hM
  | cons g gs ih =>
      intro M hgs hM
      have hg : QGateWellFormed N g := hgs g (List.mem_cons.mpr (Or.inl rfl))
      have hgs' : ∀ g' ∈ gs, QGateWellFormed N g' :=
        fun g' hg' => hgs g' (List.mem_cons.mpr (Or.inr hg'))
      simp only [List.foldl_cons]
      exact ih _ hgs' (Submonoid.mul_mem _ (gateMatrix_mem_unitaryGroup hg) hM)

theorem circuitMatrix_mem_unitaryGroup {N : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g) :
    circuitMatrix N gs ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  simp only [circuitMatrix]
  exact foldl_gateMatrix_mem_unitary gs 1 hgs (Submonoid.one_mem _)

theorem tensorProd_zeroState_zero {a : ℕ} (φ : Fin (2 ^ a) → ℂ) :
    tensorProd φ (zeroState 0) = φ := by
  funext s
  have hs : s.val < 2 ^ a := s.isLt
  have hdiv : s.val / 2 ^ a = 0 := Nat.div_eq_of_lt hs
  have hmod : s.val % 2 ^ a = s.val := Nat.mod_eq_of_lt hs
  simp only [tensorProd, zeroState, hdiv, hmod, ite_true, mul_one]
  have hX : (⟨s.val, hs⟩ : Fin (2 ^ a)) = s := Fin.eq_of_val_eq rfl
  exact congrArg φ hX

end Cslib.Complexity.Classes
