/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# BQP class audit

`BQP` here is Atlas's internal encoding of bounded-error quantum polynomial
time, as defined in `CSLibExt.Computability.Complexity.Classes`: an
input-dependent list of exact 2-local Gaussian-rational gates with separate
ancilla and size polynomials `a, s` and a polynomial-time gate-list generator
such that every input's gates are well-formed on `|x| + a(|x|)` qubits, at most
`s(|x|)` of them, and the acceptance probability on `bqpInitState` is at least
`2/3` on yes-instances and at most `1/3` on no-instances. This module records
that internal encoding as an iff, shows every witness acceptance probability is
a genuine probability in `[0, 1]` (by circuit-semantics norm preservation), and
computes the acceptance probability after flipping the output qubit with an `X`
gate, the semantic step behind complementation.

Background and motivation only: uniform quantum polynomial-time computation
(Arora–Barak Definition 10.9; Bernstein–Vazirani) as in S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009, Definition 10.9, and
E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on
Computing 26 (1997), 1411–1473, where the circuit sequence is generated from
unary size/time inputs and elementary operations act on up to three qubits. No
equivalence between the Atlas encoding and those models is proved here.

Background sources: S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Definition 10.9; E. Bernstein and U. Vazirani, "Quantum
complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

open QuantumGates

/-- Membership in `BQP`, unfolded: Atlas's internal `BQP` encoding (well-formedness, `2/3`–`1/3` thresholds) with
ancilla and size polynomials, a polynomial-time gate generator,
well-formedness of every generated gate, and the `2/3`–`1/3` acceptance
thresholds on the initial state. -/
theorem mem_BQP_iff {L : List Bool → Bool} :
    L ∈ BQP ↔
      ∃ a s : Polynomial ℕ, ∃ gates : List Bool → List QGate,
        IsPolyTime gates ∧
        (∀ x, (gates x).length ≤ s.eval x.length) ∧
        (∀ x, ∀ g ∈ gates x, QGateWellFormed (x.length + a.eval x.length) g) ∧
        ∀ x,
          (L x = true →
            2 / 3 ≤ acceptProb
              (applyCircuit (x.length + a.eval x.length) (gates x)
                (bqpInitState x (a.eval x.length)))) ∧
          (L x = false → acceptProb
              (applyCircuit (x.length + a.eval x.length) (gates x)
                (bqpInitState x (a.eval x.length))) ≤ 1 / 3) := by
  rfl

/-- For any well-formed witness circuit, the acceptance probability on the
BQP initial state is a genuine probability. -/
theorem bqp_witness_acceptProb_mem_Icc (a : Polynomial ℕ)
    (gates : List Bool → List QGate) (x : List Bool)
    (hwf : ∀ g ∈ gates x, QGateWellFormed (x.length + a.eval x.length) g) :
    acceptProb
        (applyCircuit (x.length + a.eval x.length) (gates x)
          (bqpInitState x (a.eval x.length))) ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact acceptProb_nonneg _
  · apply acceptProb_le_one
    rw [sqNorm_applyCircuit hwf, sqNorm_bqpInitState]

private theorem xLow_wellFormed {N : ℕ} (hN : 2 ≤ N) :
    QGateWellFormed N (0, 1, xLowEntries) := by
  unfold xLowEntries
  exact qGateWellFormed_onLow xGate xGate_unitary (by norm_num) (by omega)

private theorem complexOfGRatMatrix_xGate :
    complexOfGRatMatrix xGate = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xGate, complexOfGRatMatrix, toComplex, gaussRatEnc, toRat_ratEncOfRat,
      Complex.ext_iff]

private def toggle0 {N : ℕ} (hN : 1 ≤ N) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  ⟨(if s.val % 2 = 0 then s.val + 1 else s.val - 1), by
    by_cases h : s.val % 2 = 0
    · simp only [ite_eq_left h]
      have hs := s.isLt
      have hNpos : N ≠ 0 := by omega
      obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos
      have h2N : 2 ^ (M + 1) = 2 ^ M * 2 := pow_succ 2 M
      omega
    · simp only [ite_eq_right h]
      have hs := s.isLt
      omega⟩

private theorem toggle0_val {N : ℕ} (hN : 1 ≤ N) (s : Fin (2 ^ N)) :
    (toggle0 hN s).val = if s.val % 2 = 0 then s.val + 1 else s.val - 1 := rfl

private theorem qBit_preserve_succ_add (k : ℕ) (n : ℕ) (hn : n % 2 = 0) :
    qBit (k + 1) (n + 1) = qBit (k + 1) n := by
  unfold qBit
  apply Fin.ext
  simp only
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  rw [h2k]
  have hdiv : ∀ a : ℕ, a / (2 * 2 ^ k) = (a / 2) / 2 ^ k := by
    intro a
    rw [← Nat.div_div_eq_div_mul]
  rw [hdiv, hdiv]
  have : (n + 1) / 2 = n / 2 := by omega
  rw [this]

private theorem qBit_preserve_succ_sub (k : ℕ) (n : ℕ) (hn : n % 2 = 1) :
    qBit (k + 1) (n - 1) = qBit (k + 1) n := by
  unfold qBit
  apply Fin.ext
  simp only
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  rw [h2k]
  have hdiv : ∀ a : ℕ, a / (2 * 2 ^ k) = (a / 2) / 2 ^ k := by
    intro a
    rw [← Nat.div_div_eq_div_mul]
  rw [hdiv, hdiv]
  have : (n - 1) / 2 = n / 2 := by omega
  rw [this]

private theorem qBit_toggle_ne {N : ℕ} (hN : 1 ≤ N) (s : Fin (2 ^ N)) :
    qBit 0 (toggle0 hN s).val ≠ qBit 0 s.val := by
  rw [toggle0_val]
  by_cases h : s.val % 2 = 0
  · simp only [ite_eq_left h]
    apply Fin.ne_of_val_ne
    show ((s.val + 1) / 2 ^ 0) % 2 ≠ (s.val / 2 ^ 0) % 2
    simp only [pow_zero, Nat.div_one]
    omega
  · simp only [ite_eq_right h]
    apply Fin.ne_of_val_ne
    show ((s.val - 1) / 2 ^ 0) % 2 ≠ (s.val / 2 ^ 0) % 2
    simp only [pow_zero, Nat.div_one]
    have : s.val % 2 = 1 := by omega
    omega

private theorem qBit_toggle_eq_of_ne_zero {N : ℕ} (hN : 1 ≤ N)
    (s : Fin (2 ^ N)) {k : ℕ} (hk : k ≠ 0) :
    qBit k (toggle0 hN s).val = qBit k s.val := by
  rw [toggle0_val]
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  by_cases h : s.val % 2 = 0
  · simp only [ite_eq_left h]
    exact qBit_preserve_succ_add M s.val h
  · simp only [ite_eq_right h]
    have h1 : s.val % 2 = 1 := by omega
    exact qBit_preserve_succ_sub M s.val h1

private theorem toggle0_involutive {N : ℕ} (hN : 1 ≤ N) (s : Fin (2 ^ N)) :
    toggle0 hN (toggle0 hN s) = s := by
  apply Fin.ext
  show (if (toggle0 hN s).val % 2 = 0 then _ else _) = s.val
  rw [toggle0_val]
  by_cases h : s.val % 2 = 0
  · simp only [h, ite_true]
    have h1 : (s.val + 1) % 2 = 1 := by omega
    simp only [h1]
    norm_num
  · simp only [h, ite_false]
    have h1 : (s.val - 1) % 2 = 0 := by
      have : 1 ≤ s.val := by omega
      omega
    simp only [h1, ite_true]
    omega

private def toggle0Equiv {N : ℕ} (hN : 1 ≤ N) : Fin (2 ^ N) ≃ Fin (2 ^ N) :=
  ⟨toggle0 hN, toggle0 hN, toggle0_involutive hN, toggle0_involutive hN⟩

private theorem qBit_eq_testBit_eq {k n m : ℕ}
    (h : qBit k n = qBit k m) : n.testBit k = m.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hval : (n / 2 ^ k) % 2 = (m / 2 ^ k) % 2 := Fin.ext_iff.mp h
  rw [hval]

private theorem fin_eq_of_qBit_eq {N : ℕ} {a b : Fin (2 ^ N)}
    (h : ∀ k : Fin N, qBit k.val a.val = qBit k.val b.val) : a = b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact qBit_eq_testBit_eq (h ⟨i, hi⟩)
  · have hi' : N ≤ i := by omega
    have ha : a.val < 2 ^ i :=
      lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) hi')
    have hb : b.val < 2 ^ i :=
      lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) hi')
    rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]

private theorem X_ne_one {a c : Fin 2} (h : a ≠ c) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) a c = 1 := by
  fin_cases a <;> fin_cases c <;> simp_all

private theorem X_eq_zero {a : Fin 2} :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) a a = 0 := by
  fin_cases a <;> rfl

private theorem fin2_eq_of_ne {a b c : Fin 2} (h1 : a ≠ c) (h2 : b ≠ c) :
    a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

private theorem kronecker_X_one_eq_one {a b c d : Fin 2} (hbd : b = d)
    (hac : a ≠ c) :
    Matrix.kronecker (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1
      (a, b) (c, d) = 1 := by
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hbd]
  rw [X_ne_one hac]
  simp

private theorem kronecker_X_one_eq_zero_of_high_ne {a b c d : Fin 2}
    (hbd : b ≠ d) :
    Matrix.kronecker (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1
      (a, b) (c, d) = 0 := by
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  have : (1 : Matrix (Fin 2) (Fin 2) ℂ) b d = 0 := by
    simp [hbd]
  rw [this, mul_zero]

private theorem kronecker_X_one_eq_zero_of_low_eq {a b d : Fin 2}
    (hbd : b = d) :
    Matrix.kronecker (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1
      (a, b) (a, d) = 0 := by
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hbd, X_eq_zero, zero_mul]

private theorem matrixOfEntries_xLow_apply (p q : Fin 2 × Fin 2) :
    matrixOfEntries xLowEntries p q =
      Matrix.kronecker (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 p q := by
  have h1 : matrixOfEntries xLowEntries =
      Matrix.kronecker (complexOfGRatMatrix xGate) 1 := by
    unfold xLowEntries
    exact matrixOfEntries_onLow xGate
  rw [h1, complexOfGRatMatrix_xGate]

private theorem gateMatrix_toggle {N : ℕ} (hN : 2 ≤ N)
    (s : Fin (2 ^ N)) :
    gateMatrix N (0, 1, xLowEntries) s (toggle0 (by omega) s) = 1 := by
  have h1N : 1 ≤ N := by omega
  unfold gateMatrix
  have hagree : ∀ k : Fin N, k.val ≠ (0, 1, xLowEntries).1 →
      k.val ≠ (0, 1, xLowEntries).2.1 →
      qBit k.val s.val = qBit k.val (toggle0 h1N s).val := by
    intro k hk0 hk1
    exact (qBit_toggle_eq_of_ne_zero h1N s hk0).symm
  rw [ite_eq_left hagree]
  rw [matrixOfEntries_xLow_apply]
  apply kronecker_X_one_eq_one
  · exact (qBit_toggle_eq_of_ne_zero (k := 1) h1N s (by norm_num)).symm
  · exact Ne.symm (qBit_toggle_ne h1N s)

private theorem gateMatrix_ne_toggle {N : ℕ} (hN : 2 ≤ N)
    (s t : Fin (2 ^ N)) (hne : t ≠ toggle0 (by omega) s) :
    gateMatrix N (0, 1, xLowEntries) s t = 0 := by
  have h1N : 1 ≤ N := by omega
  unfold gateMatrix
  by_cases hagree : (∀ k : Fin N, k.val ≠ (0, 1, xLowEntries).1 →
      k.val ≠ (0, 1, xLowEntries).2.1 →
      qBit k.val s.val = qBit k.val t.val)
  · rw [ite_eq_left hagree, matrixOfEntries_xLow_apply]
    by_cases h1 : qBit 1 s.val = qBit 1 t.val
    · by_cases h0 : qBit 0 s.val = qBit 0 t.val
      · rw [← h0, ← h1]
        exact kronecker_X_one_eq_zero_of_low_eq rfl
      · exfalso
        apply hne
        apply fin_eq_of_qBit_eq
        intro k
        by_cases hk0 : k.val = 0
        · rw [hk0]
          apply fin2_eq_of_ne _ (qBit_toggle_ne h1N s)
          exact Ne.symm h0
        · by_cases hk1 : k.val = 1
          · rw [hk1, ← h1]
            exact (qBit_toggle_eq_of_ne_zero (k := 1) h1N s
              (by norm_num)).symm
          · have hag := hagree k hk0 hk1
            have hp := qBit_toggle_eq_of_ne_zero h1N s hk0
            rw [← hag]
            exact hp.symm
    · exact kronecker_X_one_eq_zero_of_high_ne h1
  · rw [ite_eq_right hagree]

private theorem applyGate_xLow_val {N : ℕ} (hN : 2 ≤ N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    (applyGate N (0, 1, xLowEntries) ψ) s = ψ (toggle0 (by omega) s) := by
  have hwf := xLow_wellFormed hN
  rw [applyGate_eq_gateMatrix_mulVec hwf, Matrix.mulVec_apply_eq_sum]
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _)]
  · rw [gateMatrix_toggle hN s, one_mul]
  · intro t _ hne
    rw [gateMatrix_ne_toggle hN s t hne, zero_mul]

private theorem fin2_eq_zero_of_ne_one {a : Fin 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a <;> simp_all

private theorem qBit_toggle_eq_one_iff {N : ℕ} (hN : 1 ≤ N)
    (s : Fin (2 ^ N)) :
    qBit 0 (toggle0 hN s).val = 1 ↔ qBit 0 s.val ≠ 1 := by
  constructor
  · intro h_eq h_contra
    have hne := qBit_toggle_ne hN s
    rw [h_eq, h_contra] at hne
    exact hne rfl
  · intro h_ne
    have hs0 : qBit 0 s.val = 0 := fin2_eq_zero_of_ne_one h_ne
    have hne := qBit_toggle_ne hN s
    rw [hs0] at hne
    exact Fin.eq_one_of_ne_zero _ hne

/-- Flipping the output qubit complements the acceptance probability:
after the `X` gate on qubit `0` (embedded on qubits `0, 1`), the acceptance
probability is the squared norm minus the original acceptance probability. -/
theorem acceptProb_applyGate_xLow {N : ℕ} (hN : 2 ≤ N)
    (ψ : Fin (2 ^ N) → ℂ) :
    acceptProb (applyGate N (0, 1, xLowEntries) ψ) =
      sqNorm ψ - acceptProb ψ := by
  have h1N : 1 ≤ N := by omega
  have hφ : ∀ s : Fin (2 ^ N),
      (applyGate N (0, 1, xLowEntries) ψ) s = ψ (toggle0 h1N s) := by
    intro s
    exact applyGate_xLow_val hN ψ s
  have hsum : acceptProb (applyGate N (0, 1, xLowEntries) ψ) =
      ∑ s : Fin (2 ^ N), (if qBit 0 s.val = 1 then (0 : ℝ)
        else (starRingEnd ℂ (ψ s) * ψ s).re) := by
    unfold acceptProb
    have hcongr : ∀ s : Fin (2 ^ N),
        (if qBit 0 s.val = 1 then
          (starRingEnd ℂ ((applyGate N (0, 1, xLowEntries) ψ) s) *
            (applyGate N (0, 1, xLowEntries) ψ) s).re else 0) =
        (if qBit 0 (toggle0 h1N s).val = 1 then (0 : ℝ)
          else (starRingEnd ℂ (ψ (toggle0 h1N s)) *
            ψ (toggle0 h1N s)).re) := by
      intro s
      rw [hφ s]
      by_cases h : qBit 0 s.val = 1
      · have ht : qBit 0 (toggle0 h1N s).val ≠ 1 :=
          fun h_eq => ((qBit_toggle_eq_one_iff h1N s).mp h_eq) h
        rw [ite_eq_left h, ite_eq_right ht]
      · have ht : qBit 0 (toggle0 h1N s).val = 1 := by
          exact (qBit_toggle_eq_one_iff h1N s).mpr h
        rw [ite_eq_right h, ite_eq_left ht]
    rw [Finset.sum_congr rfl (fun s _ => hcongr s)]
    have hreindex := Equiv.sum_comp (toggle0Equiv h1N)
      (fun t : Fin (2 ^ N) => if qBit 0 t.val = 1 then (0 : ℝ)
        else (starRingEnd ℂ (ψ t) * ψ t).re)
    have htoggle_eq : ∀ s : Fin (2 ^ N),
        (if qBit 0 (toggle0 h1N s).val = 1 then (0 : ℝ)
          else (starRingEnd ℂ (ψ (toggle0 h1N s)) *
            ψ (toggle0 h1N s)).re) =
        (fun t : Fin (2 ^ N) => if qBit 0 t.val = 1 then (0 : ℝ)
          else (starRingEnd ℂ (ψ t) * ψ t).re)
          ((toggle0Equiv h1N) s) := by
      intro s
      rfl
    rw [Finset.sum_congr rfl (fun s _ => htoggle_eq s)]
    exact hreindex
  rw [hsum]
  have hadd := acceptProb_add_compl ψ
  linarith

end Cslib.Complexity.Classes
