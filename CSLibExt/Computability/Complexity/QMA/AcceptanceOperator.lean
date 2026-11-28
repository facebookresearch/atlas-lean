/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitMatrix

/-!
# Acceptance operator of a quantum verifier

A verifier circuit on `|x| + m + a` qubits starts from the basis state of the input `x` on the
`|x|` low-order qubits, a witness vector `ψ` on the next `m` qubits and the all-zero state on the
`a` high-order qubits, and accepts when qubit `0` measures `1`. Its acceptance operator
`Q_x = E_x† U† Π U E_x` acts on the witness register: `E_x` sends a witness vector to that initial
state (`witnessEmbedding`), `U` is the circuit matrix and `Π` is the diagonal projector onto the
basis states whose qubit `0` is `1` (`acceptProjector`). For a circuit of well-formed gates, the
acceptance probability on every witness vector `ψ`, normalized or not, is `Re ⟪ψ, Q_x ψ⟫`, and
`0 ≤ Q_x ≤ 1` in the Loewner order, so completeness and soundness of the verifier on `x` are
bounds on the quadratic form of one operator. For well-formed gates, the sesquilinear forms of
`Q_x` and `1 - Q_x` are the inner products, through `Π` and `1 - Π`, of the circuit images of
the initial states; at basis witnesses they give the entries of `Q_x` and `1 - Q_x`.

This file is about one verifier on one input: it states nothing about repetition, uniform circuit
families or complexity classes.

Sources: C. Marriott and J. Watrous, Quantum Arthur-Merlin games, Computational Complexity 14
(2005), 122-152 (the acceptance operator of a QMA verifier); M. A. Nielsen and I. L. Chuang,
Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 2
(measurement and the Born rule).
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
namespace Cslib.Complexity.Classes.QMA

set_option autoImplicit false

/-- **Accepting projector.** The diagonal projector onto the basis states of `N` qubits whose
qubit `0`, the least significant bit of the index, is `1`. -/
def acceptProjector (N : ℕ) : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  Matrix.diagonal fun s => if qBit 0 s.val = 1 then 1 else 0

/-- The accepting projector is positive semidefinite. -/
theorem acceptProjector_posSemidef (N : ℕ) : (acceptProjector N).PosSemidef := by
  unfold acceptProjector
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs with h
  · simp
  · simp

/-- The complementary projector `1 - Π` is positive semidefinite. -/
theorem one_sub_acceptProjector_posSemidef (N : ℕ) : (1 - acceptProjector N).PosSemidef := by
  unfold acceptProjector
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs with h
  · simp
  · simp

/-- **Born rule as a quadratic form.** The acceptance probability of any vector `φ` on `N`
qubits is `Re ⟪φ, Π φ⟫` for the accepting projector `Π`. -/
theorem acceptProb_eq_re_star_dotProduct_acceptProjector_mulVec {N : ℕ}
    (φ : Fin (2 ^ N) → ℂ) :
    acceptProb φ = (star φ ⬝ᵥ (acceptProjector N *ᵥ φ)).re := by
  simp only [acceptProb, acceptProjector, dotProduct, Pi.star_apply,
    Matrix.mulVec_diagonal, Complex.re_sum, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · simp
  · simp

/-- **Witness embedding.** The `2 ^ (|x| + m + a)` × `2 ^ m` matrix whose column `w` is the initial
verifier state of the basis witness `Pi.single w 1`: the basis state of `x` on the `|x|` low-order
qubits, the witness on the next `m` qubits and the all-zero state on the `a` high-order qubits. -/
def witnessEmbedding (x : List Bool) (m a : ℕ) :
    Matrix (Fin (2 ^ (x.length + m + a))) (Fin (2 ^ m)) ℂ :=
  Matrix.of fun s w =>
    tensorProd (tensorProd (basisState x) (Pi.single w (1 : ℂ))) (zeroState a) s

/-- The witness embedding sends a witness vector `ψ` to the initial verifier state with witness
`ψ`. -/
theorem witnessEmbedding_mulVec (x : List Bool) (m a : ℕ) (ψ : Fin (2 ^ m) → ℂ) :
    witnessEmbedding x m a *ᵥ ψ = tensorProd (tensorProd (basisState x) ψ) (zeroState a) := by
  funext s
  simp only [Matrix.mulVec, dotProduct, witnessEmbedding, Matrix.of_apply,
    tensorProd, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq]
  simp
  ring

private theorem tensorProd_star_dotProduct {v m : ℕ}
    (φ φ' : Fin (2 ^ v) → ℂ) (χ χ' : Fin (2 ^ m) → ℂ) :
    star (tensorProd φ χ) ⬝ᵥ tensorProd φ' χ' =
      (star φ ⬝ᵥ φ') * (star χ ⬝ᵥ χ') := by
  simp only [dotProduct, Pi.star_apply]
  rw [Finset.sum_mul_sum]
  rw [← (qubitSplit v m).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [tensorProd_qubitSplit, tensorProd_qubitSplit, star_mul']
  ring

private theorem star_dotProduct_self_eq_sqNorm {m : ℕ}
    (ψ : Fin (2 ^ m) → ℂ) : star ψ ⬝ᵥ ψ = (sqNorm ψ : ℂ) := by
  simp only [dotProduct, Pi.star_apply, sqNorm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re]

/-- The witness embedding is an isometry: `E_x† E_x = 1`. -/
theorem witnessEmbedding_conjTranspose_mul_self (x : List Bool) (m a : ℕ) :
    (witnessEmbedding x m a)ᴴ * witnessEmbedding x m a = 1 := by
  ext w w'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, witnessEmbedding,
    Matrix.of_apply]
  have h_dot : (∑ j, star (tensorProd
      (tensorProd (basisState x) (Pi.single w (1 : ℂ))) (zeroState a) j) *
      tensorProd (tensorProd (basisState x) (Pi.single w' (1 : ℂ)))
        (zeroState a) j) = star (tensorProd
      (tensorProd (basisState x) (Pi.single w (1 : ℂ))) (zeroState a)) ⬝ᵥ
      tensorProd (tensorProd (basisState x) (Pi.single w' (1 : ℂ)))
        (zeroState a) := by simp [dotProduct, Pi.star_apply]
  rw [h_dot, tensorProd_star_dotProduct, tensorProd_star_dotProduct,
    star_dotProduct_self_eq_sqNorm, star_dotProduct_self_eq_sqNorm,
    sqNorm_basisState, sqNorm_zeroState]
  simp only [Complex.ofReal_one, one_mul, mul_one]
  rw [dotProduct_single]
  simp only [Pi.star_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  split_ifs
  · simp
  · simp

/-- **Acceptance operator.** For an input `x`, a witness register of `m` qubits, `a` ancilla
qubits and a gate list `gs` on `|x| + m + a` qubits, the operator `Q_x = E_x† U† Π U E_x` on the
witness register, where `E_x` is the witness embedding, `U` the circuit matrix and `Π` the
accepting projector. -/
noncomputable def acceptOp (x : List Bool) (m a : ℕ) (gs : List QGate) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)ᴴ *
    acceptProjector (x.length + m + a) *
      (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)

private theorem circuitMatrix_conjTranspose_mul_self {N : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g) :
    (circuitMatrix N gs)ᴴ * circuitMatrix N gs = 1 := by
  have hmem := circuitMatrix_mem_unitaryGroup hgs
  rw [Matrix.mem_unitaryGroup_iff'] at hmem
  have hstar := Matrix.star_eq_conjTranspose (circuitMatrix N gs)
  rw [hstar] at hmem
  exact hmem

/-- **Sesquilinear form of the acceptance operator.** For well-formed gates, `⟪φ, Q_x ψ⟫` is the
inner product, through the accepting projector, of the circuit images of the initial states with
witnesses `φ` and `ψ`. -/
theorem star_dotProduct_acceptOp_mulVec {x : List Bool} {m a : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) (φ ψ : Fin (2 ^ m) → ℂ) :
    star φ ⬝ᵥ (acceptOp x m a gs *ᵥ ψ) =
      star (applyCircuit (x.length + m + a) gs
          (tensorProd (tensorProd (basisState x) φ) (zeroState a))) ⬝ᵥ
        (acceptProjector (x.length + m + a) *ᵥ
          applyCircuit (x.length + m + a) gs
            (tensorProd (tensorProd (basisState x) ψ) (zeroState a))) := by
  rw [← witnessEmbedding_mulVec, ← witnessEmbedding_mulVec,
    applyCircuit_eq_circuitMatrix_mulVec hgs,
    applyCircuit_eq_circuitMatrix_mulVec hgs]
  simp only [acceptOp, Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- **Acceptance probability as a quadratic form.** For well-formed gates, the acceptance
probability of the verifier on every witness vector `ψ`, normalized or not, is
`Re ⟪ψ, Q_x ψ⟫`. -/
theorem acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec {x : List Bool}
    {m a : ℕ} {gs : List QGate} (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g)
    (ψ : Fin (2 ^ m) → ℂ) :
    acceptProb (applyCircuit (x.length + m + a) gs
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a))) =
      (star ψ ⬝ᵥ (acceptOp x m a gs *ᵥ ψ)).re := by
  rw [acceptProb_eq_re_star_dotProduct_acceptProjector_mulVec,
    star_dotProduct_acceptOp_mulVec hgs]

/-- **`0 ≤ Q_x`.** The acceptance operator is positive semidefinite for every gate list. -/
theorem acceptOp_posSemidef (x : List Bool) (m a : ℕ) (gs : List QGate) :
    (acceptOp x m a gs).PosSemidef := by
  have hPi : (acceptProjector (x.length + m + a)).PosSemidef := by
    apply acceptProjector_posSemidef
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hPi
    (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)
  simpa [acceptOp, Matrix.mul_assoc] using h

/-- **Rejection operator.** For well-formed gates, `1 - Q_x = E_x† U† (1 - Π) U E_x`. -/
theorem one_sub_acceptOp_eq {x : List Bool} {m a : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) :
    1 - acceptOp x m a gs =
      (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)ᴴ *
        (1 - acceptProjector (x.length + m + a)) *
          (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a) := by
  have hU := circuitMatrix_conjTranspose_mul_self hgs
  have hE := witnessEmbedding_conjTranspose_mul_self x m a
  have h1 :
      (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)ᴴ *
          (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a) =
        ((witnessEmbedding x m a)ᴴ * (circuitMatrix (x.length + m + a) gs)ᴴ) *
          (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a) := by
    rw [Matrix.conjTranspose_mul]
  have h2 :
      ((witnessEmbedding x m a)ᴴ * (circuitMatrix (x.length + m + a) gs)ᴴ) *
          (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a) =
        (witnessEmbedding x m a)ᴴ *
          (((circuitMatrix (x.length + m + a) gs)ᴴ *
            circuitMatrix (x.length + m + a) gs) * witnessEmbedding x m a) := by
    simp only [Matrix.mul_assoc]
  have h3 :
      (witnessEmbedding x m a)ᴴ *
          (((circuitMatrix (x.length + m + a) gs)ᴴ *
            circuitMatrix (x.length + m + a) gs) * witnessEmbedding x m a) =
        (witnessEmbedding x m a)ᴴ * witnessEmbedding x m a := by
    rw [hU, Matrix.one_mul]
  have hB := h1.trans (h2.trans (h3.trans hE))
  simp only [acceptOp, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB,
    Matrix.mul_assoc]

/-- **`Q_x ≤ 1`.** For well-formed gates, `1 - Q_x` is positive semidefinite. -/
theorem one_sub_acceptOp_posSemidef {x : List Bool} {m a : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) :
    (1 - acceptOp x m a gs).PosSemidef := by
  rw [one_sub_acceptOp_eq hgs]
  have hPi : (1 - acceptProjector (x.length + m + a)).PosSemidef := by
    apply one_sub_acceptProjector_posSemidef
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hPi
    (circuitMatrix (x.length + m + a) gs * witnessEmbedding x m a)
  simpa [Matrix.mul_assoc] using h

/-- **Sesquilinear form of the rejection operator.** For well-formed gates, `⟪φ, (1 - Q_x) ψ⟫` is
the inner product, through the rejecting projector `1 - Π`, of the circuit images of the initial
states with witnesses `φ` and `ψ`. -/
theorem star_dotProduct_one_sub_acceptOp_mulVec {x : List Bool} {m a : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) (φ ψ : Fin (2 ^ m) → ℂ) :
    star φ ⬝ᵥ ((1 - acceptOp x m a gs) *ᵥ ψ) =
      star (applyCircuit (x.length + m + a) gs
          (tensorProd (tensorProd (basisState x) φ) (zeroState a))) ⬝ᵥ
        ((1 - acceptProjector (x.length + m + a)) *ᵥ
          applyCircuit (x.length + m + a) gs
            (tensorProd (tensorProd (basisState x) ψ) (zeroState a))) := by
  rw [one_sub_acceptOp_eq hgs]
  rw [← witnessEmbedding_mulVec, ← witnessEmbedding_mulVec,
    applyCircuit_eq_circuitMatrix_mulVec hgs,
    applyCircuit_eq_circuitMatrix_mulVec hgs]
  simp only [Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

end Cslib.Complexity.Classes.QMA
