/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.AcceptanceOperator
public import CSLibExt.Computability.Complexity.QuantumGates.BQPAudit
public import CSLibExt.Computability.Complexity.QMA.ThresholdAmplification

/-!
# Tests: Acceptance operator of a quantum verifier
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
namespace CslibTest.Complexity.Classes.QMA

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QMA

#print axioms acceptProjector_posSemidef
#print axioms one_sub_acceptProjector_posSemidef
#print axioms acceptProb_eq_re_star_dotProduct_acceptProjector_mulVec
#print axioms witnessEmbedding_mulVec
#print axioms witnessEmbedding_conjTranspose_mul_self
#print axioms star_dotProduct_acceptOp_mulVec
#print axioms acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec
#print axioms acceptOp_posSemidef
#print axioms one_sub_acceptOp_eq
#print axioms one_sub_acceptOp_posSemidef
#print axioms star_dotProduct_one_sub_acceptOp_mulVec

/-- Identity circuit with empty input: the acceptance operator is the accepting projector of the
witness register, whose qubit `0` is the global qubit `0`. -/
theorem acceptOp_nil_nil (m a : ℕ) : acceptOp [] m a [] = acceptProjector m := by
  have hinter : acceptProjector (List.length ([] : List Bool) + m + a) *
      witnessEmbedding [] m a =
      witnessEmbedding [] m a * acceptProjector m := by
    ext s w
    simp only [acceptProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hE : witnessEmbedding [] m a s w = 0
    · simp [hE]
    · simp only [witnessEmbedding, Matrix.of_apply, tensorProd] at hE
      have hA := left_ne_zero_of_mul hE
      have hB := right_ne_zero_of_mul hE
      have hA2 := right_ne_zero_of_mul hA
      have hsingle : ∀ u : Fin (2 ^ m),
          Pi.single (M := fun _ : Fin (2 ^ m) => ℂ) w (1 : ℂ) u ≠ 0 → u = w := by
        intro u hu
        by_contra hcon
        exact hu (Pi.single_eq_of_ne (M := fun _ : Fin (2 ^ m) => ℂ) hcon 1)
      have hval : s.val % 2 ^ (List.length ([] : List Bool) + m) / 2 ^ 0 = w.val :=
        congrArg Fin.val (hsingle _ hA2)
      simp only [pow_zero, Nat.div_one] at hval
      have hB2 : (if s.val / 2 ^ (List.length ([] : List Bool) + m) = 0 then
          (1 : ℂ) else 0) ≠ 0 :=
        hB
      have hzero : s.val / 2 ^ (List.length ([] : List Bool) + m) = 0 := by
        by_contra hcon
        simp only [hcon, ite_false] at hB2
        exact absurd rfl hB2
      have hpos : 0 < 2 ^ (List.length ([] : List Bool) + m) := by positivity
      have hlt : s.val < 2 ^ (List.length ([] : List Bool) + m) :=
        (Nat.div_eq_zero_iff.mp hzero).resolve_left (ne_of_gt hpos)
      have hmod : s.val % 2 ^ (List.length ([] : List Bool) + m) = s.val :=
        Nat.mod_eq_of_lt hlt
      have hsw : s.val = w.val := by rw [← hmod, hval]
      rw [hsw]
      exact mul_comm _ _
  simp only [acceptOp, circuitMatrix, List.foldl_nil, Matrix.one_mul, Matrix.mul_assoc]
  rw [hinter, ← Matrix.mul_assoc, witnessEmbedding_conjTranspose_mul_self,
    Matrix.one_mul]

#print axioms acceptOp_nil_nil

/-- Identity circuit with input `b :: xs`: qubit `0` holds the first input bit, so the acceptance
operator is `1` when that bit is `true` and `0` otherwise. -/
theorem acceptOp_cons_nil (b : Bool) (xs : List Bool) (m a : ℕ) :
    acceptOp (b :: xs) m a [] = if b then 1 else 0 := by
  have hscale : acceptProjector ((b :: xs).length + m + a) *
      witnessEmbedding (b :: xs) m a =
      (if b then (1 : ℂ) else 0) • witnessEmbedding (b :: xs) m a := by
    ext s w
    simp only [acceptProjector, Matrix.diagonal_mul, Matrix.smul_apply,
      smul_eq_mul]
    by_cases hE : witnessEmbedding (b :: xs) m a s w = 0
    · simp [hE]
    · have hscal : (if qBit 0 s.val = 1 then (1 : ℂ) else 0) =
          (if b then (1 : ℂ) else 0) := by
        simp only [witnessEmbedding, Matrix.of_apply, tensorProd] at hE
        have hA := left_ne_zero_of_mul hE
        have hX := left_ne_zero_of_mul hA
        have hX2 : (if s.val % 2 ^ ((b :: xs).length + m) % 2 ^ (b :: xs).length
            = qNumOf (b :: xs) then (1 : ℂ) else 0) ≠ 0 := hX
        have hq : s.val % 2 ^ ((b :: xs).length + m) % 2 ^ (b :: xs).length
            = qNumOf (b :: xs) := by
          by_contra hcon
          simp only [hcon, ite_false] at hX2
          exact absurd rfl hX2
        have hlen : (0 : ℕ) < (b :: xs).length := by simp
        have h2len : (2 : ℕ) ∣ 2 ^ (b :: xs).length := dvd_pow_self 2 hlen.ne'
        have h2lenm : (2 : ℕ) ∣ 2 ^ ((b :: xs).length + m) := by
          have h1 : (1 : ℕ) ≤ (b :: xs).length + m := by
            rw [List.length_cons]
            omega
          simpa only [pow_one] using pow_dvd_pow (2 : ℕ) h1
        have hmod1 : (s.val % 2 ^ ((b :: xs).length + m)) % 2 ^ (b :: xs).length
            % 2 = (s.val % 2 ^ ((b :: xs).length + m)) % 2 :=
          Nat.mod_mod_of_dvd _ h2len
        have hmod2 : (s.val % 2 ^ ((b :: xs).length + m)) % 2 = s.val % 2 :=
          Nat.mod_mod_of_dvd _ h2lenm
        have hsq : s.val % 2 = qNumOf (b :: xs) % 2 := by
          rw [← hmod2, ← hmod1, hq]
        have hqmod : qNumOf (b :: xs) % 2 = (if b then 1 else 0 : ℕ) := by
          simp only [qNumOf, Nat.add_mul_mod_self_left]
          cases b <;> rfl
        have h2 : s.val % 2 = (if b then 1 else 0 : ℕ) := by rw [hsq, hqmod]
        have hqbit : qBit 0 s.val = 1 ↔ s.val % 2 = 1 := by
          simp [qBit, Fin.ext_iff]
        cases b
        · have h20 : s.val % 2 = 0 := by simpa using h2
          have hne : qBit 0 s.val ≠ 1 := by
            intro hcon
            have hcon2 := hqbit.mp hcon
            omega
          simp [hne]
        · have h21 : s.val % 2 = 1 := by simpa using h2
          have hpos : qBit 0 s.val = 1 := hqbit.mpr h21
          simp [hpos]
      rw [hscal]
  simp only [acceptOp, circuitMatrix, List.foldl_nil, Matrix.one_mul,
    Matrix.mul_assoc]
  rw [hscale, Matrix.mul_smul, witnessEmbedding_conjTranspose_mul_self]
  cases b <;> simp

#print axioms acceptOp_cons_nil

/-- For well-formed gates and no witness qubits, the real part of the single entry of the
acceptance operator is the acceptance probability of the circuit on the BQP initial state. -/
theorem re_acceptOp_zero_zero_eq_acceptProb {x : List Bool} {a : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    (acceptOp x 0 a gs 0 0).re =
      acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) := by
  have hgs' : ∀ g ∈ gs, QGateWellFormed (x.length + 0 + a) g := hgs
  have hmain := acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec hgs'
    (fun _ : Fin (2 ^ 0) => (1 : ℂ))
  have hsingle : ∀ s : Fin (2 ^ 0), s = 0 := by
    intro s
    rw [Fin.ext_iff]
    have h0 : s.val = 0 := Nat.lt_one_iff.mp s.isLt
    rw [h0]
    simp
  have hψ : (fun _ : Fin (2 ^ 0) => (1 : ℂ)) = zeroState 0 := by
    funext s
    have hs0 : s.val = 0 := Nat.lt_one_iff.mp s.isLt
    simp only [zeroState, hs0, ite_true]
  have hLHS : acceptProb (applyCircuit (x.length + 0 + a) gs
        (tensorProd (tensorProd (basisState x) (fun _ : Fin (2 ^ 0) => (1 : ℂ)))
          (zeroState a))) =
      acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) := by
    rw [hψ, tensorProd_zeroState_zero]
    simp only [bqpInitState]
    rfl
  have hRHS : (star (fun _ : Fin (2 ^ 0) => (1 : ℂ)) ⬝ᵥ
        (acceptOp x 0 a gs *ᵥ (fun _ : Fin (2 ^ 0) => (1 : ℂ)))).re =
      (acceptOp x 0 a gs 0 0).re := by
    simp only [dotProduct, Matrix.mulVec]
    rw [Finset.sum_eq_single (0 : Fin (2 ^ 0))]
    · rw [Finset.sum_eq_single (0 : Fin (2 ^ 0))]
      · simp
      · intro t _ ht
        exfalso
        exact ht (hsingle t)
      · intro hcon
        exact absurd (Finset.mem_univ (0 : Fin (2 ^ 0))) hcon
    · intro s _ hs
      exfalso
      exact hs (hsingle s)
    · intro hcon
      exact absurd (Finset.mem_univ (0 : Fin (2 ^ 0))) hcon
  rw [hLHS, hRHS] at hmain
  exact hmain.symm

#print axioms re_acceptOp_zero_zero_eq_acceptProb

/-- On at least two qubits, an `X` gate on qubit `0` complements the quadratic form: with
`Q` the acceptance operator of the one-gate circuit on qubit `0` and `Q₀` that of the
empty circuit, `Re ⟪ψ, Q ψ⟫ = sqNorm ψ - Re ⟪ψ, Q₀ ψ⟫` for every witness `ψ`. -/
theorem re_star_dotProduct_acceptOp_xLow_mulVec {x : List Bool} {m a : ℕ}
    (hN : 2 ≤ x.length + m + a) (ψ : Fin (2 ^ m) → ℂ) :
    (star ψ ⬝ᵥ (acceptOp x m a [(0, 1, QuantumGates.xLowEntries)] *ᵥ ψ)).re =
      sqNorm ψ - (star ψ ⬝ᵥ (acceptOp x m a [] *ᵥ ψ)).re := by
  have hgs : ∀ g ∈ [(0, 1, QuantumGates.xLowEntries)],
      QGateWellFormed (x.length + m + a) g := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact QuantumGates.qGateWellFormed_onLow QuantumGates.xGate
      QuantumGates.xGate_unitary (by norm_num) (by omega)
  have hgs0 : ∀ g ∈ ([] : List QGate), QGateWellFormed (x.length + m + a) g := by
    intro g hg
    simp at hg
  have hmain1 :=
    (acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec hgs ψ).symm
  have hmain0 :=
    (acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec hgs0 ψ).symm
  rw [hmain1, hmain0]
  have hcirc : applyCircuit (x.length + m + a) [(0, 1, QuantumGates.xLowEntries)]
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a)) =
      applyGate (x.length + m + a) (0, 1, QuantumGates.xLowEntries)
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a)) := rfl
  have hnil : applyCircuit (x.length + m + a) []
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a)) =
      tensorProd (tensorProd (basisState x) ψ) (zeroState a) := rfl
  rw [hcirc, hnil]
  have hxlow := acceptProb_applyGate_xLow hN
    (tensorProd (tensorProd (basisState x) ψ) (zeroState a))
  rw [hxlow]
  have hsq : sqNorm (tensorProd (tensorProd (basisState x) ψ) (zeroState a)) =
      sqNorm ψ := by
    simp only [sqNorm_tensorProd, sqNorm_basisState, sqNorm_zeroState, mul_one,
      one_mul]
  rw [hsq]

#print axioms re_star_dotProduct_acceptOp_xLow_mulVec

/-- Consumption: for well-formed gates, a soundness bound `s` on the acceptance probabilities
of unit witnesses gives `Re ⟪ψ, Q_x ψ⟫ ≤ s` for every unit witness `ψ`, the quadratic-form
hypothesis of threshold amplification. -/
theorem re_star_dotProduct_acceptOp_mulVec_le_of_acceptProb_le {x : List Bool} {m a : ℕ}
    {gs : List QGate} (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) {s : ℝ}
    (hsound : ∀ ψ : Fin (2 ^ m) → ℂ, sqNorm ψ = 1 →
      acceptProb (applyCircuit (x.length + m + a) gs
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a))) ≤ s) :
    ∀ ψ : Fin (2 ^ m) → ℂ, sqNorm ψ = 1 → (star ψ ⬝ᵥ (acceptOp x m a gs *ᵥ ψ)).re ≤ s :=
  fun ψ hψ => (acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec hgs ψ) ▸
    hsound ψ hψ

#print axioms re_star_dotProduct_acceptOp_mulVec_le_of_acceptProb_le

/--
Amplified soundness for a verifier: for well-formed gates, `s ≤ c` and `2 p ≤ k (c - s) ^ 2`,
if every unit witness is accepted with probability at most `s`, then at threshold
`k (c + s) / 2` every unit `k`-block vector, entangled or not, has threshold expectation at
most `2⁻ᵖ`.-/
theorem acceptOp_amplify_sound {x : List Bool} {m a k p : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) {c s : ℝ} (hsc : s ≤ c)
    (hk : 2 * (p : ℝ) ≤ (k : ℝ) * (c - s) ^ 2)
    (hsound : ∀ ψ : Fin (2 ^ m) → ℂ, sqNorm ψ = 1 →
      acceptProb (applyCircuit (x.length + m + a) gs
        (tensorProd (tensorProd (basisState x) ψ) (zeroState a))) ≤ s)
    (Ψ : Fin (2 ^ (k * m)) → ℂ) (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp k (acceptOp x m a gs) ((k : ℝ) * (c + s) / 2) *ᵥ Ψ)).re ≤
      ((2 : ℝ) ^ p)⁻¹ :=
  thresholdOp_amplify_sound (acceptOp_posSemidef x m a gs)
    (one_sub_acceptOp_posSemidef hgs) hsc hk
    (re_star_dotProduct_acceptOp_mulVec_le_of_acceptProb_le hgs hsound) Ψ hΨ
#print axioms acceptOp_amplify_sound

/--
Amplified completeness for a verifier: for well-formed gates, `s ≤ c` and
`2 p ≤ k (c - s) ^ 2`, a unit witness accepted with probability at least `c` has, at threshold
`k (c + s) / 2`, `k`-fold product threshold expectation at least `1 - 2⁻ᵖ`.-/
theorem acceptOp_amplify_complete {x : List Bool} {m a k p : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + m + a) g) {c s : ℝ} (hsc : s ≤ c)
    (hk : 2 * (p : ℝ) ≤ (k : ℝ) * (c - s) ^ 2) (ψ : Fin (2 ^ m) → ℂ) (hψ : sqNorm ψ = 1)
    (hc : c ≤ acceptProb (applyCircuit (x.length + m + a) gs
      (tensorProd (tensorProd (basisState x) ψ) (zeroState a)))) :
    1 - ((2 : ℝ) ^ p)⁻¹ ≤
      (star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
        (thresholdOp k (acceptOp x m a gs) ((k : ℝ) * (c + s) / 2) *ᵥ
          blockProd (fun _ : Fin k => ψ))).re := by
  have hc' : c ≤ (star ψ ⬝ᵥ (acceptOp x m a gs *ᵥ ψ)).re :=
    acceptProb_applyCircuit_eq_re_star_dotProduct_acceptOp_mulVec hgs ψ ▸ hc
  exact thresholdOp_amplify_complete (acceptOp_posSemidef x m a gs)
    (one_sub_acceptOp_posSemidef hgs) hsc hk ψ hψ hc'
#print axioms acceptOp_amplify_complete

end CslibTest.Complexity.Classes.QMA
