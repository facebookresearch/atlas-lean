/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates
public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics

/-!
# Computational-basis actions of the exact encoded gates

A `QGate` acts on two qubits of an `N`-qubit register. This file computes
that action on computational-basis indices for the exact gate encodings
of `ExactGates`: one generic lemma for a single-qubit gate embedded at
an arbitrary qubit (the second register qubit is a spectator), one for a
controlled single-qubit gate in either control orientation, and the
five-gate Toffoli decomposition proved equal to the Toffoli permutation
of basis indices at arbitrary distinct positions. Amplitude forms are
stated through the bit operations `flipBit` and `setQBit`, so consumers
never redo `qBit`/`setBits` index arithmetic.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (the
controlled-`V` decomposition of Toffoli with `V² = X`).
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

open scoped Matrix BigOperators

/-! ## Bit-index operations -/

/-- Flip qubit `q` of a basis index; the identity when `q ≥ N`. -/
def flipBit (N q : ℕ) (t : Fin (2 ^ N)) : Fin (2 ^ N) :=
  ⟨(t.val ^^^ 2 ^ q) % 2 ^ N, Nat.mod_lt _ (by positivity)⟩

/-- Set qubit `q` of a basis index to `b` when `q < N`; at `q ≥ N` this
is the identity (an out-of-range qubit of a basis index always reads
`0`, and no bit is flipped). -/
def setQBit (N q : ℕ) (b : Fin 2) (t : Fin (2 ^ N)) : Fin (2 ^ N) :=
  if qBit q t.val = b then t else flipBit N q t

private theorem qBit_eq_if_testBit (k n : ℕ) : qBit k n = if n.testBit k then 1 else 0 := by
  have h := Nat.toNat_testBit n k
  apply Fin.ext
  cases hn : n.testBit k
  · rw [hn] at h; simp at h; simp [qBit]; exact h.symm
  · rw [hn] at h; simp at h; simp [qBit]; exact h.symm

private theorem qBit_eq_of_testBit_eq {k a b : ℕ} (h : a.testBit k = b.testBit k) : qBit k a = qBit k b := by
  rw [qBit_eq_if_testBit, qBit_eq_if_testBit, h]

private theorem testBit_eq_of_qBit_eq {k a b : ℕ} (h : qBit k a = qBit k b) : a.testBit k = b.testBit k := by
  have ha := qBit_eq_if_testBit k a
  have hb := qBit_eq_if_testBit k b
  rw [ha, hb] at h
  cases ha' : a.testBit k <;> cases hb' : b.testBit k <;> simp_all

private theorem testBit_ge {x : ℕ} {N k : ℕ} (hk : N ≤ k) (hx : x < 2 ^ N) : x.testBit k = false := by
  have h : x < 2 ^ k := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  exact Nat.testBit_lt_two_pow h

/-- Two basis indices agreeing on every qubit are equal. -/
theorem fin_eq_of_qBit_eq {N : ℕ} {s t : Fin (2 ^ N)}
    (h : ∀ k, k < N → qBit k s.val = qBit k t.val) : s = t := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < N
  · exact testBit_eq_of_qBit_eq (h k hk)
  · have hk' : N ≤ k := Nat.le_of_not_gt hk
    rw [testBit_ge hk' s.isLt, testBit_ge hk' t.isLt]

/-- `flipBit` toggles its own qubit. -/
theorem qBit_flipBit_self {N q : ℕ} (hq : q < N) (t : Fin (2 ^ N)) :
    qBit q (flipBit N q t).val = qBit q t.val + 1 := by
  have hflip : (flipBit N q t).val.testBit q = !(t.val.testBit q) := by
    show ((t.val ^^^ 2 ^ q) % 2 ^ N).testBit q = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow_self]
    simp [hq]
  have ha := qBit_eq_if_testBit q (flipBit N q t).val
  have hb := qBit_eq_if_testBit q t.val
  rw [ha, hb, hflip]
  cases t.val.testBit q <;> decide

/-- `flipBit` fixes every other qubit. -/
theorem qBit_flipBit_of_ne {N q k : ℕ} (hkq : k ≠ q) (t : Fin (2 ^ N)) :
    qBit k (flipBit N q t).val = qBit k t.val := by
  apply qBit_eq_of_testBit_eq
  show ((t.val ^^^ 2 ^ q) % 2 ^ N).testBit k = t.val.testBit k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  have h2 : (2 ^ q).testBit k = false := Nat.testBit_two_pow_of_ne (Ne.symm hkq)
  rw [h2]
  by_cases hkN : k < N
  · simp [hkN]
  · have hkN' : N ≤ k := Nat.le_of_not_gt hkN
    have ht : t.val.testBit k = false := testBit_ge hkN' t.isLt
    simp [hkN, ht]

/-- `flipBit` is an involution. -/
theorem flipBit_flipBit (N q : ℕ) (t : Fin (2 ^ N)) :
    flipBit N q (flipBit N q t) = t := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro k
  have h1 : (flipBit N q t).val.testBit k =
      (decide (k < N) && (t.val.testBit k ^^ (2 ^ q).testBit k)) := by
    show ((t.val ^^^ 2 ^ q) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  have h2 : (flipBit N q (flipBit N q t)).val.testBit k =
      (decide (k < N) && ((flipBit N q t).val.testBit k ^^ (2 ^ q).testBit k)) := by
    show (((flipBit N q t).val ^^^ 2 ^ q) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  rw [h2, h1]
  by_cases hkN : k < N
  · simp [hkN]
  · have hkN' : N ≤ k := Nat.le_of_not_gt hkN
    have ht : t.val.testBit k = false := testBit_ge hkN' t.isLt
    simp [hkN, ht]

/-- Flips at two qubits commute. -/
theorem flipBit_comm (N q r : ℕ) (t : Fin (2 ^ N)) :
    flipBit N q (flipBit N r t) = flipBit N r (flipBit N q t) := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro k
  have h1 : (flipBit N r t).val.testBit k =
      (decide (k < N) && (t.val.testBit k ^^ (2 ^ r).testBit k)) := by
    show ((t.val ^^^ 2 ^ r) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  have h2 : (flipBit N q (flipBit N r t)).val.testBit k =
      (decide (k < N) && ((flipBit N r t).val.testBit k ^^ (2 ^ q).testBit k)) := by
    show (((flipBit N r t).val ^^^ 2 ^ q) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  have h3 : (flipBit N q t).val.testBit k =
      (decide (k < N) && (t.val.testBit k ^^ (2 ^ q).testBit k)) := by
    show ((t.val ^^^ 2 ^ q) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  have h4 : (flipBit N r (flipBit N q t)).val.testBit k =
      (decide (k < N) && ((flipBit N q t).val.testBit k ^^ (2 ^ r).testBit k)) := by
    show (((flipBit N q t).val ^^^ 2 ^ r) % 2 ^ N).testBit k = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  rw [h2, h1, h4, h3]
  by_cases hkN : k < N
  · simp [hkN]
    cases t.val.testBit k <;> cases (2 ^ q).testBit k <;> cases (2 ^ r).testBit k <;> rfl
  · have hkN' : N ≤ k := Nat.le_of_not_gt hkN
    have ht : t.val.testBit k = false := testBit_ge hkN' t.isLt
    simp [hkN, ht]

private theorem fin2_add_one_eq_of_ne {a b : Fin 2} (h : a ≠ b) : a + 1 = b := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- `setQBit` sets its own qubit. -/
theorem qBit_setQBit_self {N q : ℕ} (hq : q < N) (b : Fin 2) (t : Fin (2 ^ N)) :
    qBit q (setQBit N q b t).val = b := by
  unfold setQBit
  by_cases h : qBit q t.val = b
  · simp [h]
  · simp [h]
    have hflip := qBit_flipBit_self hq t
    rw [hflip]
    exact fin2_add_one_eq_of_ne h

/-- `setQBit` fixes every other qubit. -/
theorem qBit_setQBit_of_ne {N q k : ℕ} (hkq : k ≠ q) (b : Fin 2) (t : Fin (2 ^ N)) :
    qBit k (setQBit N q b t).val = qBit k t.val := by
  unfold setQBit
  by_cases h : qBit q t.val = b
  · simp [h]
  · simp [h, qBit_flipBit_of_ne hkq t]

/-- Setting a qubit to its current value is the identity. -/
theorem setQBit_qBit (N q : ℕ) (t : Fin (2 ^ N)) :
    setQBit N q (qBit q t.val) t = t := by
  simp [setQBit]

/-- The last `setQBit` at a qubit wins. -/
theorem setQBit_setQBit {N q : ℕ} (hq : q < N) (b b' : Fin 2) (t : Fin (2 ^ N)) :
    setQBit N q b (setQBit N q b' t) = setQBit N q b t := by
  apply fin_eq_of_qBit_eq
  intro k hk
  by_cases h : k = q
  · subst h
    rw [qBit_setQBit_self hq, qBit_setQBit_self hq]
  · have h1 := qBit_setQBit_of_ne (N:=N) (q:=q) (k:=k) h b (setQBit N q b' t)
    have h2 := qBit_setQBit_of_ne (N:=N) (q:=q) (k:=k) h b' t
    have h3 := qBit_setQBit_of_ne (N:=N) (q:=q) (k:=k) h b t
    rw [h1, h2, h3]

/-- A flip at another qubit commutes with `setQBit`. -/
theorem flipBit_setQBit_comm {N q r : ℕ} (hqr : q ≠ r) (b : Fin 2) (t : Fin (2 ^ N)) :
    flipBit N r (setQBit N q b t) = setQBit N q b (flipBit N r t) := by
  unfold setQBit
  have h : qBit q (flipBit N r t).val = qBit q t.val := qBit_flipBit_of_ne hqr t
  rw [h]
  by_cases hqb : qBit q t.val = b
  · simp [hqb]
  · simp [hqb, flipBit_comm]

private theorem qBit_ge_of_lt {N k : ℕ} {x : ℕ} (hk : N ≤ k) (hx : x < 2 ^ N) : qBit k x = 0 := by
  rw [qBit_eq_if_testBit, testBit_ge hk hx]
  rfl

private theorem fiber_sum {N q : ℕ} {M : Type*} [AddCommMonoid M] (hq : q < N) (s : Fin (2 ^ N))
    (F : Fin 2 → Fin (2 ^ N) → M) :
    (∑ t, (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
      then F (qBit q t.val) t else 0)) =
      ∑ b : Fin 2, F b (setQBit N q b s) := by
  classical
  let S : Finset (Fin (2 ^ N)) := Finset.image (fun b : Fin 2 => setQBit N q b s) Finset.univ
  have hmem : ∀ t : Fin (2 ^ N),
      (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val) →
      t ∈ S := by
    intro t ht
    have heq : setQBit N q (qBit q t.val) s = t := by
      apply fin_eq_of_qBit_eq
      intro k hk
      by_cases hqk : k = q
      · subst hqk
        rw [qBit_setQBit_self hq]
      · have h1 := qBit_setQBit_of_ne hqk (qBit q t.val) s
        have h2 := ht ⟨k, hk⟩ hqk
        rw [h1]
        exact h2
    have hb : (qBit q t.val) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    have himg : setQBit N q (qBit q t.val) s ∈ S := Finset.mem_image_of_mem _ hb
    rw [heq] at himg
    exact himg
  have hsub : (∑ t ∈ S, (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
      then F (qBit q t.val) t else 0)) =
      (∑ t, (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
      then F (qBit q t.val) t else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro t _ htS
    have hnot : ¬ (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val) := by
      intro hP
      exact htS (hmem t hP)
    simp [hnot]
  rw [← hsub]
  have hinj : Set.InjOn (fun b : Fin 2 => setQBit N q b s) ↑(Finset.univ : Finset (Fin 2)) := by
    intro b1 _ b2 _ heq
    simp only at heq
    have h1 := qBit_setQBit_self (N:=N) (q:=q) hq b1 s
    have h2 := qBit_setQBit_self (N:=N) (q:=q) hq b2 s
    rw [heq] at h1
    rw [h1] at h2
    exact h2
  have himg := Finset.sum_image (s := (Finset.univ : Finset (Fin 2)))
    (f := fun t => (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
      then F (qBit q t.val) t else 0))
    (g := fun b : Fin 2 => setQBit N q b s) hinj
  rw [himg]
  apply Finset.sum_congr rfl
  intro b _
  have hP : (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val (setQBit N q b s).val) := by
    intro k hkq
    exact (qBit_setQBit_of_ne hkq b s).symm
  have hqself := qBit_setQBit_self hq b s
  rw [ite_eq_left hP, hqself]

/-! ## Placement and generic actions -/

/-- **Embedded single-qubit gate:** act with the `2 × 2` Gaussian-rational
matrix `U` on qubit `q`, with qubit `p ≠ q` as spectator. When `q < p`
the `4 × 4` block is `U` on the low qubit tensored with the identity,
otherwise the identity tensored with `U`. -/
def embeddedGate (U : Matrix (Fin 2) (Fin 2) GRat) (q p : ℕ) : QGate :=
  if q < p then (q, p, entriesOf (onLow U)) else (p, q, entriesOf (onHigh U))

/-- An embedded gate of a unitary matrix at two distinct in-range qubits
is well-formed. -/
theorem embeddedGate_wellFormed (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N q p : ℕ} (hqp : q ≠ p) (hqN : q < N) (hpN : p < N) :
    QGateWellFormed N (embeddedGate U q p) := by
  unfold embeddedGate
  by_cases h : q < p
  · simp [h]
    apply qGateWellFormed_onLow
    all_goals assumption
  · simp [h]
    have hpq : p < q := by omega
    apply qGateWellFormed_onHigh
    all_goals assumption

/-- **Generic embedded action:** the amplitude at `s` after an embedded
gate is the `qBit q s` row of `U` against the two amplitudes differing
from `s` at most at qubit `q`. -/
theorem applyGate_embeddedGate {N q p : ℕ} {U : Matrix (Fin 2) (Fin 2) GRat}
    (hg : QGateWellFormed N (embeddedGate U q p)) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (embeddedGate U q p) ψ s =
      ∑ b : Fin 2, complexOfGRatMatrix U (qBit q s.val) b * ψ (setQBit N q b s) := by
  classical
  have h12 : (embeddedGate U q p).1 < (embeddedGate U q p).2.1 := hg.1
  have h2N : (embeddedGate U q p).2.1 < N := hg.2.1
  by_cases hqp : q < p
  · have hpN : p < N := by
      unfold embeddedGate at h2N
      simp [hqp] at h2N
      exact h2N
    have hqN : q < N := by omega
    have hpq_ne : p ≠ q := by omega
    rw [applyGate_eq_gateMatrix_mulVec hg]
    simp only [Matrix.mulVec, dotProduct]
    have hterm : ∀ t : Fin (2 ^ N), gateMatrix N (embeddedGate U q p) s t * ψ t =
        (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
          then complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) * ψ t else 0) := by
      intro t
      by_cases hqAgree : (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
      · have hAgree2 : (∀ k : Fin N, k.val ≠ q → k.val ≠ p → qBit k.val s.val = qBit k.val t.val) :=
          fun k hkq _ => hqAgree k hkq
        have hpEq : qBit p s.val = qBit p t.val :=
          hqAgree ⟨p, hpN⟩ hpq_ne
        have hLHS : gateMatrix N (embeddedGate U q p) s t * ψ t =
            complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) * ψ t := by
          have hgate : gateMatrix N (embeddedGate U q p) s t =
              complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) := by
            unfold gateMatrix embeddedGate
            rw [ite_eq_left hqp, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
            simp [complexOfGRatMatrix, onLow, hpEq]
          rw [hgate]
        rw [hLHS]
        rw [ite_eq_left hqAgree]
      · by_cases hAgree2 : (∀ k : Fin N, k.val ≠ q → k.val ≠ p → qBit k.val s.val = qBit k.val t.val)
        · have hpNe : qBit p s.val ≠ qBit p t.val := by
            intro hpEq
            apply hqAgree
            intro k hkq
            by_cases hkp : k.val = p
            · rw [hkp]
              exact hpEq
            · exact hAgree2 k hkq hkp
          have hLHS0 : gateMatrix N (embeddedGate U q p) s t * ψ t = 0 := by
            have hgate : gateMatrix N (embeddedGate U q p) s t = 0 := by
              unfold gateMatrix embeddedGate
              rw [ite_eq_left hqp, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
              simp [complexOfGRatMatrix, onLow, hpNe, toComplex_gaussRatEnc, Complex.ext_iff]
            rw [hgate, zero_mul]
          rw [hLHS0]
          simp [hqAgree]
        · have hLHS0 : gateMatrix N (embeddedGate U q p) s t * ψ t = 0 := by
            have hgate : gateMatrix N (embeddedGate U q p) s t = 0 := by
              unfold gateMatrix embeddedGate
              rw [ite_eq_left hqp, ite_eq_right hAgree2]
            rw [hgate, zero_mul]
          rw [hLHS0]
          simp [hqAgree]
    simp only [hterm]
    exact fiber_sum hqN s (fun b t => complexOfGRatMatrix U (qBit q s.val) b * ψ t)
  · by_cases hpq : p < q
    · have hqN : q < N := by
        unfold embeddedGate at h2N
        simp [hqp] at h2N
        exact h2N
      have hpN : p < N := by omega
      have hpq_ne : p ≠ q := by omega
      rw [applyGate_eq_gateMatrix_mulVec hg]
      simp only [Matrix.mulVec, dotProduct]
      have hterm : ∀ t : Fin (2 ^ N), gateMatrix N (embeddedGate U q p) s t * ψ t =
          (if (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
            then complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) * ψ t else 0) := by
        intro t
        by_cases hqAgree : (∀ k : Fin N, k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
        · have hAgree2 : (∀ k : Fin N, k.val ≠ p → k.val ≠ q → qBit k.val s.val = qBit k.val t.val) :=
            fun k hkp hkq => hqAgree k hkq
          have hpEq : qBit p s.val = qBit p t.val :=
            hqAgree ⟨p, hpN⟩ hpq_ne
          have hLHS : gateMatrix N (embeddedGate U q p) s t * ψ t =
              complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) * ψ t := by
            have hgate : gateMatrix N (embeddedGate U q p) s t =
                complexOfGRatMatrix U (qBit q s.val) (qBit q t.val) := by
              unfold gateMatrix embeddedGate
              rw [ite_eq_right hqp, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
              simp [complexOfGRatMatrix, onHigh, hpEq]
            rw [hgate]
          rw [hLHS]
          rw [ite_eq_left hqAgree]
        · by_cases hAgree2 : (∀ k : Fin N, k.val ≠ p → k.val ≠ q → qBit k.val s.val = qBit k.val t.val)
          · have hpNe : qBit p s.val ≠ qBit p t.val := by
              intro hpEq
              apply hqAgree
              intro k hkq
              by_cases hkp : k.val = p
              · rw [hkp]
                exact hpEq
              · exact hAgree2 k hkp hkq
            have hLHS0 : gateMatrix N (embeddedGate U q p) s t * ψ t = 0 := by
              have hgate : gateMatrix N (embeddedGate U q p) s t = 0 := by
                unfold gateMatrix embeddedGate
                rw [ite_eq_right hqp, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                simp [complexOfGRatMatrix, onHigh, hpNe, toComplex_gaussRatEnc, Complex.ext_iff]
              rw [hgate, zero_mul]
            rw [hLHS0]
            simp [hqAgree]
          · have hLHS0 : gateMatrix N (embeddedGate U q p) s t * ψ t = 0 := by
              have hgate : gateMatrix N (embeddedGate U q p) s t = 0 := by
                unfold gateMatrix embeddedGate
                rw [ite_eq_right hqp, ite_eq_right hAgree2]
              rw [hgate, zero_mul]
            rw [hLHS0]
            simp [hqAgree]
      simp only [hterm]
      exact fiber_sum hqN s (fun b t => complexOfGRatMatrix U (qBit q s.val) b * ψ t)
    · have heq : q = p := by omega
      subst heq
      unfold embeddedGate at h12
      simp at h12

/-- **Generic controlled action:** a controlled gate applies `U` to the
target qubit exactly on the control-`1` branch, in either orientation. -/
theorem applyGate_controlledGate {N c t : ℕ} {U : Matrix (Fin 2) (Fin 2) GRat}
    (hg : QGateWellFormed N (controlledGate U c t)) (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (controlledGate U c t) ψ s =
      if qBit c s.val = 1 then
        ∑ b : Fin 2, complexOfGRatMatrix U (qBit t s.val) b * ψ (setQBit N t b s)
      else ψ s := by
  classical
  have h12 : (controlledGate U c t).1 < (controlledGate U c t).2.1 := hg.1
  have h2N : (controlledGate U c t).2.1 < N := hg.2.1
  by_cases hc_lt : c < t
  · have htN : t < N := by
      unfold controlledGate at h2N
      simp [hc_lt] at h2N
      exact h2N
    have hcN : c < N := by omega
    have hct_ne : c ≠ t := by omega
    have htc_ne : t ≠ c := by omega
    by_cases hc1 : qBit c s.val = 1
    · have hcs1 : qBit c s.val = 1 := hc1
      rw [applyGate_eq_gateMatrix_mulVec hg]
      simp only [Matrix.mulVec, dotProduct]
      rw [ite_eq_left hc1]
      have hterm : ∀ t0 : Fin (2 ^ N), gateMatrix N (controlledGate U c t) s t0 * ψ t0 =
          (if (∀ k : Fin N, k.val ≠ t → qBit k.val s.val = qBit k.val t0.val)
            then complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) * ψ t0 else 0) := by
        intro t0
        by_cases hqAgree : (∀ k : Fin N, k.val ≠ t → qBit k.val s.val = qBit k.val t0.val)
        · have hAgree2 : (∀ k : Fin N, k.val ≠ c → k.val ≠ t → qBit k.val s.val = qBit k.val t0.val) :=
            fun k _ hkt => hqAgree k hkt
          have hcEq1 : qBit c t0.val = 1 := by
            have hcEq : qBit c s.val = qBit c t0.val :=
              hqAgree ⟨c, hcN⟩ hct_ne
            rw [hcs1] at hcEq
            exact hcEq.symm
          have hLHS : gateMatrix N (controlledGate U c t) s t0 * ψ t0 =
              complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) * ψ t0 := by
            have hgate : gateMatrix N (controlledGate U c t) s t0 =
                complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) := by
              unfold gateMatrix controlledGate
              rw [ite_eq_left hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
              simp [complexOfGRatMatrix, ctrlLow, hcs1, hcEq1]
            rw [hgate]
          rw [hLHS]
          rw [ite_eq_left hqAgree]
        · by_cases hAgree2 : (∀ k : Fin N, k.val ≠ c → k.val ≠ t → qBit k.val s.val = qBit k.val t0.val)
          · have hcNe1 : qBit c t0.val ≠ 1 := by
              intro hc1t0
              apply hqAgree
              intro k hkt
              by_cases hkc : k.val = c
              · rw [hkc, hcs1, hc1t0]
              · exact hAgree2 k hkc hkt
            have hLHS0 : gateMatrix N (controlledGate U c t) s t0 * ψ t0 = 0 := by
              have hgate : gateMatrix N (controlledGate U c t) s t0 = 0 := by
                unfold gateMatrix controlledGate
                rw [ite_eq_left hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                simp [complexOfGRatMatrix, ctrlLow, hcs1, hcNe1, toComplex_gaussRatEnc,
                  Complex.ext_iff]
              rw [hgate, zero_mul]
            rw [hLHS0]
            simp [hqAgree]
          · have hLHS0 : gateMatrix N (controlledGate U c t) s t0 * ψ t0 = 0 := by
              have hgate : gateMatrix N (controlledGate U c t) s t0 = 0 := by
                unfold gateMatrix controlledGate
                rw [ite_eq_left hc_lt, ite_eq_right hAgree2]
              rw [hgate, zero_mul]
            rw [hLHS0]
            simp [hqAgree]
      simp only [hterm]
      exact fiber_sum htN s (fun b t0 => complexOfGRatMatrix U (qBit t s.val) b * ψ t0)
    · have hc0 : qBit c s.val = 0 := by
        generalize e1 : qBit c s.val = v1
        fin_cases v1 <;> simp_all [hc1, e1]
      rw [applyGate_eq_gateMatrix_mulVec hg]
      simp [Matrix.mulVec, dotProduct]
      simp [hc1]
      have hSingle : (∑ t0, gateMatrix N (controlledGate U c t) s t0 * ψ t0) = ψ s := by
        have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (2 ^ N))), b ≠ s → gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
          intro b _ hbNe
          by_cases hAgree2 : (∀ k : Fin N, k.val ≠ c → k.val ≠ t → qBit k.val s.val = qBit k.val b.val)
          · by_cases hcEq : qBit c s.val = qBit c b.val
            · by_cases htEq : qBit t s.val = qBit t b.val
              · have heq : b = s := by
                  apply fin_eq_of_qBit_eq
                  intro k hk
                  by_cases hkc : k = c
                  · subst hkc
                    exact hcEq.symm
                  · by_cases hkt : k = t
                    · subst hkt
                      exact htEq.symm
                    · exact (hAgree2 ⟨k, hk⟩ hkc hkt).symm
                exact absurd heq hbNe
              · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
                  have hcEq0 : qBit c b.val = 0 := by rw [← hcEq, hc0]
                  have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                    unfold gateMatrix controlledGate
                    rw [ite_eq_left hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                    simp [complexOfGRatMatrix, ctrlLow, hc0, hcEq0, htEq, toComplex_gaussRatEnc,
                      Complex.ext_iff]
                  rw [hgate, zero_mul]
                exact hLHS0
            · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
                have hcNe0 : qBit c b.val ≠ 0 := by
                  intro hcon
                  apply hcEq
                  rw [hc0, hcon]
                have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                  unfold gateMatrix controlledGate
                  rw [ite_eq_left hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                  simp [complexOfGRatMatrix, ctrlLow, hc0, hcNe0, toComplex_gaussRatEnc,
                    Complex.ext_iff]
                rw [hgate, zero_mul]
              exact hLHS0
          · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
              have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                unfold gateMatrix controlledGate
                rw [ite_eq_left hc_lt, ite_eq_right hAgree2]
              rw [hgate, zero_mul]
            exact hLHS0
        have h1 : s ∉ Finset.univ → gateMatrix N (controlledGate U c t) s s * ψ s = 0 := by simp
        have hsum := Finset.sum_eq_single (s := Finset.univ) (f := fun t0 => gateMatrix N (controlledGate U c t) s t0 * ψ t0) s h0 h1
        have hsEq : gateMatrix N (controlledGate U c t) s s * ψ s = ψ s := by
          have hAg : ∀ k : Fin N, k.val ≠ c → k.val ≠ t → qBit k.val s.val = qBit k.val s.val :=
            fun k _ _ => rfl
          have hgate : gateMatrix N (controlledGate U c t) s s = 1 := by
            unfold gateMatrix controlledGate
            rw [ite_eq_left hc_lt, ite_eq_left hAg, matrixOfEntries_entriesOf]
            simp [complexOfGRatMatrix, ctrlLow, hc0, toComplex_gaussRatEnc, Complex.ext_iff]
          rw [hgate, one_mul]
        simpa [hsEq] using hsum
      exact hSingle
  · by_cases ht_lt : t < c
    · have hcN : c < N := by
        unfold controlledGate at h2N
        simp [hc_lt, ht_lt] at h2N
        exact h2N
      have htN : t < N := by omega
      have hct_ne : c ≠ t := by omega
      have htc_ne : t ≠ c := by omega
      by_cases hc1 : qBit c s.val = 1
      · have hcs1 : qBit c s.val = 1 := hc1
        rw [applyGate_eq_gateMatrix_mulVec hg]
        simp only [Matrix.mulVec, dotProduct]
        rw [ite_eq_left hc1]
        have hterm : ∀ t0 : Fin (2 ^ N), gateMatrix N (controlledGate U c t) s t0 * ψ t0 =
            (if (∀ k : Fin N, k.val ≠ t → qBit k.val s.val = qBit k.val t0.val)
              then complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) * ψ t0 else 0) := by
          intro t0
          by_cases hqAgree : (∀ k : Fin N, k.val ≠ t → qBit k.val s.val = qBit k.val t0.val)
          · have hAgree2 : (∀ k : Fin N, k.val ≠ t → k.val ≠ c → qBit k.val s.val = qBit k.val t0.val) :=
              fun k hkt _ => hqAgree k hkt
            have hcEq1 : qBit c t0.val = 1 := by
              have hcEq : qBit c s.val = qBit c t0.val :=
                hqAgree ⟨c, hcN⟩ hct_ne
              rw [hcs1] at hcEq
              exact hcEq.symm
            have hLHS : gateMatrix N (controlledGate U c t) s t0 * ψ t0 =
                complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) * ψ t0 := by
              have hgate : gateMatrix N (controlledGate U c t) s t0 =
                  complexOfGRatMatrix U (qBit t s.val) (qBit t t0.val) := by
                unfold gateMatrix controlledGate
                rw [ite_eq_right hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                simp [complexOfGRatMatrix, ctrlHigh, hcs1, hcEq1]
              rw [hgate]
            rw [hLHS]
            rw [ite_eq_left hqAgree]
          · by_cases hAgree2 : (∀ k : Fin N, k.val ≠ t → k.val ≠ c → qBit k.val s.val = qBit k.val t0.val)
            · have hcNe1 : qBit c t0.val ≠ 1 := by
                intro hc1t0
                apply hqAgree
                intro k hkt
                by_cases hkc : k.val = c
                · rw [hkc, hcs1, hc1t0]
                · exact hAgree2 k hkt hkc
              have hLHS0 : gateMatrix N (controlledGate U c t) s t0 * ψ t0 = 0 := by
                have hgate : gateMatrix N (controlledGate U c t) s t0 = 0 := by
                  unfold gateMatrix controlledGate
                  rw [ite_eq_right hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                  simp [complexOfGRatMatrix, ctrlHigh, hcs1, hcNe1, toComplex_gaussRatEnc,
                    Complex.ext_iff]
                rw [hgate, zero_mul]
              rw [hLHS0]
              simp [hqAgree]
            · have hLHS0 : gateMatrix N (controlledGate U c t) s t0 * ψ t0 = 0 := by
                have hgate : gateMatrix N (controlledGate U c t) s t0 = 0 := by
                  unfold gateMatrix controlledGate
                  rw [ite_eq_right hc_lt, ite_eq_right hAgree2]
                rw [hgate, zero_mul]
              rw [hLHS0]
              simp [hqAgree]
        simp only [hterm]
        exact fiber_sum htN s (fun b t0 => complexOfGRatMatrix U (qBit t s.val) b * ψ t0)
      · have hc0 : qBit c s.val = 0 := by
          generalize e1 : qBit c s.val = v1
          fin_cases v1 <;> simp_all [hc1, e1]
        rw [applyGate_eq_gateMatrix_mulVec hg]
        simp [Matrix.mulVec, dotProduct]
        simp [hc1]
        have hSingle : (∑ t0, gateMatrix N (controlledGate U c t) s t0 * ψ t0) = ψ s := by
          have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (2 ^ N))), b ≠ s → gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
            intro b _ hbNe
            by_cases hAgree2 : (∀ k : Fin N, k.val ≠ t → k.val ≠ c → qBit k.val s.val = qBit k.val b.val)
            · by_cases hcEq : qBit c s.val = qBit c b.val
              · by_cases htEq : qBit t s.val = qBit t b.val
                · have heq : b = s := by
                    apply fin_eq_of_qBit_eq
                    intro k hk
                    by_cases hkc : k = c
                    · subst hkc
                      exact hcEq.symm
                    · by_cases hkt : k = t
                      · subst hkt
                        exact htEq.symm
                      · exact (hAgree2 ⟨k, hk⟩ hkt hkc).symm
                  exact absurd heq hbNe
                · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
                    have hcEq0 : qBit c b.val = 0 := by rw [← hcEq, hc0]
                    have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                      unfold gateMatrix controlledGate
                      rw [ite_eq_right hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                      simp [complexOfGRatMatrix, ctrlHigh, hc0, hcEq0, htEq, toComplex_gaussRatEnc,
                        Complex.ext_iff]
                    rw [hgate, zero_mul]
                  exact hLHS0
              · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
                  have hcNe0 : qBit c b.val ≠ 0 := by
                    intro hcon
                    apply hcEq
                    rw [hc0, hcon]
                  have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                    unfold gateMatrix controlledGate
                    rw [ite_eq_right hc_lt, ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                    simp [complexOfGRatMatrix, ctrlHigh, hc0, hcNe0, toComplex_gaussRatEnc,
                      Complex.ext_iff]
                  rw [hgate, zero_mul]
                exact hLHS0
            · have hLHS0 : gateMatrix N (controlledGate U c t) s b * ψ b = 0 := by
                have hgate : gateMatrix N (controlledGate U c t) s b = 0 := by
                  unfold gateMatrix controlledGate
                  rw [ite_eq_right hc_lt, ite_eq_right hAgree2]
                rw [hgate, zero_mul]
              exact hLHS0
          have h1 : s ∉ Finset.univ → gateMatrix N (controlledGate U c t) s s * ψ s = 0 := by simp
          have hsum := Finset.sum_eq_single (s := Finset.univ) (f := fun t0 => gateMatrix N (controlledGate U c t) s t0 * ψ t0) s h0 h1
          have hsEq : gateMatrix N (controlledGate U c t) s s * ψ s = ψ s := by
            have hAg : ∀ k : Fin N, k.val ≠ t → k.val ≠ c → qBit k.val s.val = qBit k.val s.val :=
              fun k _ _ => rfl
            have hgate : gateMatrix N (controlledGate U c t) s s = 1 := by
              unfold gateMatrix controlledGate
              rw [ite_eq_right hc_lt, ite_eq_left hAg, matrixOfEntries_entriesOf]
              simp [complexOfGRatMatrix, ctrlHigh, hc0, toComplex_gaussRatEnc, Complex.ext_iff]
            rw [hgate, one_mul]
          simpa [hsEq] using hsum
        exact hSingle
    · have heq : c = t := by omega
      subst heq
      unfold controlledGate at h12
      simp at h12

/-- **Swap action:** the swap gate exchanges qubits `i` and `j` of a
basis index. -/
theorem applyGate_swap {N i j : ℕ} (hij : i < j) (hjN : j < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (i, j, swapEntries) ψ s =
      ψ (setQBit N i (qBit j s.val) (setQBit N j (qBit i s.val) s)) := by
  classical
  have hiN : i < N := by omega
  have hji_ne : j ≠ i := by omega
  have hgSwap : QGateWellFormed N (i, j, swapEntries) := by
    apply qGateWellFormed_swap
    all_goals assumption
  rw [applyGate_eq_gateMatrix_mulVec hgSwap]
  simp [Matrix.mulVec, dotProduct]
  set t0 : Fin (2 ^ N) := setQBit N i (qBit j s.val) (setQBit N j (qBit i s.val) s) with ht0
  have hi_t0 : qBit i t0.val = qBit j s.val := by
    simp [ht0, qBit_setQBit_self hiN]
  have hj_t0 : qBit j t0.val = qBit i s.val := by
    simp [ht0, qBit_setQBit_of_ne hji_ne, qBit_setQBit_self hjN]
  have hAgree_t0 : (∀ k : Fin N, k.val ≠ i → k.val ≠ j → qBit k.val s.val = qBit k.val t0.val) := by
    intro k hki hkj
    have h1 : qBit k.val t0.val = qBit k.val s.val := by
      simp [ht0, qBit_setQBit_of_ne hki, qBit_setQBit_of_ne hkj]
    exact h1.symm
  have hSingle : (∑ t, gateMatrix N (i, j, swapEntries) s t * ψ t) = ψ t0 := by
    have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (2 ^ N))), b ≠ t0 → gateMatrix N (i, j, swapEntries) s b * ψ b = 0 := by
      intro b _ hbNe
      by_cases hAgree2 : (∀ k : Fin N, k.val ≠ i → k.val ≠ j → qBit k.val s.val = qBit k.val b.val)
      · by_cases hiEq : qBit i b.val = qBit j s.val
        · by_cases hjEq : qBit j b.val = qBit i s.val
          · have heq : b = t0 := by
              apply fin_eq_of_qBit_eq
              intro k hk
              by_cases hki : k = i
              · subst hki
                rw [hiEq]
                exact hi_t0.symm
              · by_cases hkj : k = j
                · subst hkj
                  rw [hjEq]
                  exact hj_t0.symm
                · have hbks : qBit k s.val = qBit k b.val :=
                    hAgree2 ⟨k, hk⟩ hki hkj
                  have hst0 : qBit k s.val = qBit k t0.val :=
                    hAgree_t0 ⟨k, hk⟩ hki hkj
                  exact hbks.symm.trans hst0
            exact absurd heq hbNe
          · have hLHS0 : gateMatrix N (i, j, swapEntries) s b * ψ b = 0 := by
              have h1 : qBit i s.val ≠ qBit j b.val := fun h => hjEq h.symm
              have hgate : gateMatrix N (i, j, swapEntries) s b = 0 := by
                unfold gateMatrix swapEntries
                rw [ite_eq_left hAgree2, matrixOfEntries_entriesOf]
                simp [complexOfGRatMatrix, swapMatrix, hiEq, h1, toComplex_gaussRatEnc,
                  Complex.ext_iff]
              rw [hgate, zero_mul]
            exact hLHS0
        · have hLHS0 : gateMatrix N (i, j, swapEntries) s b * ψ b = 0 := by
            have h2 : qBit j s.val ≠ qBit i b.val := fun h => hiEq h.symm
            have hgate : gateMatrix N (i, j, swapEntries) s b = 0 := by
              unfold gateMatrix swapEntries
              rw [ite_eq_left hAgree2, matrixOfEntries_entriesOf]
              simp [complexOfGRatMatrix, swapMatrix, h2, toComplex_gaussRatEnc, Complex.ext_iff]
            rw [hgate, zero_mul]
          exact hLHS0
      · have hLHS0 : gateMatrix N (i, j, swapEntries) s b * ψ b = 0 := by
          have hgate : gateMatrix N (i, j, swapEntries) s b = 0 := by
            unfold gateMatrix
            rw [ite_eq_right hAgree2]
          rw [hgate, zero_mul]
        exact hLHS0
    have h1 : t0 ∉ Finset.univ → gateMatrix N (i, j, swapEntries) s t0 * ψ t0 = 0 := by simp
    have hsum := Finset.sum_eq_single (s := Finset.univ) (f := fun t => gateMatrix N (i, j, swapEntries) s t * ψ t) t0 h0 h1
    have hsEq : gateMatrix N (i, j, swapEntries) s t0 * ψ t0 = ψ t0 := by
      have hgate : gateMatrix N (i, j, swapEntries) s t0 = 1 := by
        unfold gateMatrix swapEntries
        rw [ite_eq_left hAgree_t0, matrixOfEntries_entriesOf]
        simp [complexOfGRatMatrix, swapMatrix, hi_t0, hj_t0, toComplex_gaussRatEnc, Complex.ext_iff]
      rw [hgate, one_mul]
    simpa [hsEq] using hsum
  exact hSingle

/-- **Locality:** a well-formed gate avoiding qubit `r` preserves the
support condition "vanishes off `qBit r = v`", for every `r`. -/
theorem applyGate_eq_zero_of_qBit_ne {N r : ℕ} {g : QGate} (hg : QGateWellFormed N g)
    (hr₁ : r ≠ g.1) (hr₂ : r ≠ g.2.1) (v : Fin 2) {ψ : Fin (2 ^ N) → ℂ}
    (hψ : ∀ s : Fin (2 ^ N), qBit r s.val ≠ v → ψ s = 0) :
    ∀ s : Fin (2 ^ N), qBit r s.val ≠ v → applyGate N g ψ s = 0 := by
  classical
  intro s hs
  by_cases hrN : r < N
  · rw [applyGate_eq_gateMatrix_mulVec hg]
    simp [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro t _
    by_cases hAgree : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 → qBit k.val s.val = qBit k.val t.val)
    · have hr_eq : qBit r s.val = qBit r t.val :=
        hAgree ⟨r, hrN⟩ hr₁ hr₂
      have ht_ne : qBit r t.val ≠ v := by
        rw [← hr_eq]
        exact hs
      have hψt : ψ t = 0 := hψ t ht_ne
      simp [hψt]
    · have h0 : gateMatrix N g s t = 0 := by
        unfold gateMatrix
        rw [ite_eq_right hAgree]
      simp [h0]
  · have hrN' : N ≤ r := Nat.le_of_not_gt hrN
    have hq0 : ∀ x : Fin (2 ^ N), qBit r x.val = 0 :=
      fun x => qBit_ge_of_lt hrN' x.isLt
    by_cases hv : v = 0
    · have hs0 : qBit r s.val = 0 := hq0 s
      rw [hs0, hv] at hs
      exact absurd rfl hs
    · have hψ0 : ∀ t : Fin (2 ^ N), ψ t = 0 := by
        intro t
        apply hψ t
        have ht0 : qBit r t.val = 0 := hq0 t
        rw [ht0]
        exact Ne.symm hv
      rw [applyGate_eq_gateMatrix_mulVec hg]
      simp [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro t _
      simp [hψ0 t]

/-- **Circuit locality:** a circuit of gates avoiding qubit `r` preserves
the support condition, for every `r`. -/
theorem applyCircuit_eq_zero_of_qBit_ne {N r : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g ∧ r ≠ g.1 ∧ r ≠ g.2.1) (v : Fin 2)
    {ψ : Fin (2 ^ N) → ℂ} (hψ : ∀ s : Fin (2 ^ N), qBit r s.val ≠ v → ψ s = 0) :
    ∀ s : Fin (2 ^ N), qBit r s.val ≠ v → applyCircuit N gs ψ s = 0 := by
  revert hgs
  revert hψ
  revert ψ
  induction gs with
  | nil =>
    intro ψ hψ _ s hs
    simp [applyCircuit]
    exact hψ s hs
  | cons g gs' ih =>
    intro ψ hψ hgs s hs
    have hfold : applyCircuit N (g :: gs') ψ s = applyCircuit N gs' (applyGate N g ψ) s := by
      simp [applyCircuit]
    rw [hfold]
    have hg : QGateWellFormed N g ∧ r ≠ g.1 ∧ r ≠ g.2.1 :=
      hgs g (by simp)
    obtain ⟨hgWf, hr1, hr2⟩ := hg
    have hψ' : ∀ s : Fin (2 ^ N), qBit r s.val ≠ v → applyGate N g ψ s = 0 :=
      applyGate_eq_zero_of_qBit_ne hgWf hr1 hr2 v hψ
    have hgs' : ∀ g' ∈ gs', QGateWellFormed N g' ∧ r ≠ g'.1 ∧ r ≠ g'.2.1 :=
      fun g' hg' => hgs g' (by simp [hg'])
    apply ih
    all_goals assumption
/-! ## Matrix values of the encoded gates -/

/-- The encoded `X` gate as a complex matrix. -/
theorem complexOfGRatMatrix_xGate : complexOfGRatMatrix xGate = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, xGate, toComplex_gaussRatEnc, Complex.ext_iff]

/-- The encoded `Z` gate as a complex matrix. -/
theorem complexOfGRatMatrix_zGate : complexOfGRatMatrix zGate = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, zGate, toComplex_gaussRatEnc, Complex.ext_iff]

/-- The encoded `S` gate as a complex matrix. -/
theorem complexOfGRatMatrix_sGate : complexOfGRatMatrix sGate = !![1, 0; 0, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, sGate, toComplex_gaussRatEnc, Complex.ext_iff]

/-- The encoded `S†` gate as a complex matrix. -/
theorem complexOfGRatMatrix_sDagGate :
    complexOfGRatMatrix sDagGate = !![1, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, sDagGate, toComplex_gaussRatEnc, Complex.ext_iff]

/-- The encoded `e^{iπ/4} H` gate as a complex matrix. -/
theorem complexOfGRatMatrix_omegaH :
    complexOfGRatMatrix omegaH = !![⟨1/2, 1/2⟩, ⟨1/2, 1/2⟩; ⟨1/2, 1/2⟩, ⟨-1/2, -1/2⟩] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, omegaH, toComplex_gaussRatEnc, Complex.ext_iff]

/-- `V² = X` for the encoded square root of `X`. -/
theorem complexOfGRatMatrix_vGate_mul_vGate :
    complexOfGRatMatrix vGate * complexOfGRatMatrix vGate = complexOfGRatMatrix xGate := by
  rw [complexOfGRatMatrix_xGate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, complexOfGRatMatrix, vGate,
      toComplex_gaussRatEnc, Complex.ext_iff]

/-- The encoded `V†` is the conjugate transpose of the encoded `V`. -/
theorem complexOfGRatMatrix_vDagGate :
    complexOfGRatMatrix vDagGate = star (complexOfGRatMatrix vGate) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, vDagGate, vGate, toComplex_gaussRatEnc,
      Matrix.star_apply, Complex.star_def, Complex.ext_iff]

/-! ## Permutation and phase corollaries -/

/-- The CNOT conditional index map: flip the target when the control
is `1`. For distinct in-range control and target this is the CNOT
permutation of basis indices (see `cnotEquiv`). If the target equals
the control in range, both values of that bit are sent to `0`, so
the map is not injective and does not represent CNOT; out of range
it degenerates to the identity. -/
def cnotIndex (N c t : ℕ) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  if qBit c s.val = 1 then flipBit N t s else s

/-- The Toffoli conditional index map: flip `c` when both controls
`a` and `b` are `1`. This is an involution, hence a permutation,
whenever the target differs from both controls (see
`toffoliEquiv`); the controls may coincide with each other, in
which case the map conditions on that single bit and is not a
Toffoli gate. If the target aliases a control, the map need not be
injective and does not represent Toffoli: with all indices in
range, the aliased bit is only ever cleared, never set, so on
inputs where the remaining controls read `1` both of its values
are sent to `0`. -/
def toffoliIndex (N a b c : ℕ) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  if qBit a s.val = 1 ∧ qBit b s.val = 1 then flipBit N c s else s

/-- Pullback of a state vector along `toffoliIndex`; a permutation
pullback whenever the target differs from both controls. -/
def toffoliPerm (N a b c : ℕ) (ψ : Fin (2 ^ N) → ℂ) : Fin (2 ^ N) → ℂ :=
  fun s => ψ (toffoliIndex N a b c s)

/-- In `Fin 2`, anything not `1` is `0`. -/
private theorem fin2_eq_zero_of_ne_one {x : Fin 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x <;> simp_all

/-- Setting a qubit to its current value plus one is flipping it. -/
private theorem setQBit_add_one_eq_flipBit {N q : ℕ} (hqN : q < N)
    (s : Fin (2 ^ N)) :
    setQBit N q (qBit q s.val + 1) s = flipBit N q s := by
  apply fin_eq_of_qBit_eq
  intro k hkN
  by_cases hkq : k = q
  · subst hkq
    simp [qBit_setQBit_self hqN, qBit_flipBit_self hqN]
  · simp [qBit_setQBit_of_ne hkq, qBit_flipBit_of_ne hkq]

/-- The `X` fiber sum collapses to the flipped index. -/
private theorem xFiber_collapse {N q : ℕ} (hqN : q < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    (∑ b : Fin 2, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (qBit q s.val) b *
      ψ (setQBit N q b s)) = ψ (flipBit N q s) := by
  rw [Fin.sum_univ_two]
  by_cases h : qBit q s.val = 1
  · simp only [h]
    simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      one_mul, zero_mul, add_zero]
    congr 1
    have hflip := setQBit_add_one_eq_flipBit hqN s
    rw [h] at hflip
    have h11 : (1 : Fin 2) + 1 = 0 := by decide
    rw [h11] at hflip
    exact hflip
  · have h0 : qBit q s.val = 0 := fin2_eq_zero_of_ne_one h
    simp only [h0]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_mul, one_mul, zero_add]
    congr 1
    have hflip := setQBit_add_one_eq_flipBit hqN s
    rw [h0] at hflip
    have h01 : (0 : Fin 2) + 1 = 1 := by decide
    rw [h01] at hflip
    exact hflip

/-- Entrywise `star V * V = 1`. -/
private theorem starV_mul_V_entrywise (x y : Fin 2) :
    (∑ b : Fin 2, star (complexOfGRatMatrix vGate) x b *
      complexOfGRatMatrix vGate b y) = (if x = y then 1 else 0) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M x y) vGate_unitary
  rw [Matrix.mul_apply] at h
  simpa [Matrix.one_apply] using h

/-- Entrywise `V * star V = 1`. -/
private theorem vGate_mul_starV_entrywise (x y : Fin 2) :
    (∑ b : Fin 2, complexOfGRatMatrix vGate x b * star (complexOfGRatMatrix vGate) b y) =
      (if x = y then 1 else 0) := by
  have hU : complexOfGRatMatrix vGate * star (complexOfGRatMatrix vGate) = 1 :=
    mul_eq_one_comm.mp vGate_unitary
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M x y) hU
  rw [Matrix.mul_apply] at h
  simpa [Matrix.one_apply] using h

/-- Entrywise `V * V = X`. -/
private theorem vGate_mul_vGate_entrywise (x y : Fin 2) :
    (∑ b : Fin 2, complexOfGRatMatrix vGate x b * complexOfGRatMatrix vGate b y) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) x y := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M x y)
    complexOfGRatMatrix_vGate_mul_vGate
  rw [Matrix.mul_apply, complexOfGRatMatrix_xGate] at h
  exact h

/-- Two-step fiber collapse: `V†` after `V` is the identity. -/
private theorem fiber_collapse_starV_V (x : Fin 2) (f : Fin 2 → ℂ) :
    (∑ b₁ : Fin 2, star (complexOfGRatMatrix vGate) x b₁ *
      (∑ b₀ : Fin 2, complexOfGRatMatrix vGate b₁ b₀ * f b₀)) = f x := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, starV_mul_V_entrywise]
  rw [Fin.sum_univ_two]
  fin_cases x <;> simp

/-- Two-step fiber collapse: `V` after `V†` is the identity. -/
private theorem fiber_collapse_V_starV (x : Fin 2) (f : Fin 2 → ℂ) :
    (∑ b₂ : Fin 2, complexOfGRatMatrix vGate x b₂ *
      (∑ b₃ : Fin 2, star (complexOfGRatMatrix vGate) b₂ b₃ * f b₃)) = f x := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, vGate_mul_starV_entrywise]
  rw [Fin.sum_univ_two]
  fin_cases x <;> simp

/-- Two-step fiber collapse: `V` after `V` is the `X` fiber. -/
private theorem fiber_collapse_V_V (x : Fin 2) (f : Fin 2 → ℂ) :
    (∑ b₂ : Fin 2, complexOfGRatMatrix vGate x b₂ *
      (∑ b₁ : Fin 2, complexOfGRatMatrix vGate b₂ b₁ * f b₁)) =
      ∑ b₁ : Fin 2, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) x b₁ * f b₁ := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, vGate_mul_vGate_entrywise]

/-- Embedded `X` flips its qubit. -/
theorem applyGate_embeddedGate_xGate {N q p : ℕ} (hqp : q ≠ p) (hqN : q < N) (hpN : p < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (embeddedGate xGate q p) ψ s = ψ (flipBit N q s) := by
  have hwf : QGateWellFormed N (embeddedGate xGate q p) :=
    embeddedGate_wellFormed xGate xGate_unitary hqp hqN hpN
  rw [applyGate_embeddedGate hwf ψ s, complexOfGRatMatrix_xGate]
  exact xFiber_collapse hqN ψ s

/-- Embedded `Z` phases the `1` branch by `-1`. -/
theorem applyGate_embeddedGate_zGate {N q p : ℕ} (hqp : q ≠ p) (hqN : q < N) (hpN : p < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (embeddedGate zGate q p) ψ s = (if qBit q s.val = 1 then -1 else 1) * ψ s := by
  have hwf : QGateWellFormed N (embeddedGate zGate q p) :=
    embeddedGate_wellFormed zGate zGate_unitary hqp hqN hpN
  rw [applyGate_embeddedGate hwf ψ s, complexOfGRatMatrix_zGate, Fin.sum_univ_two]
  by_cases h : qBit q s.val = 1
  · simp [h, Matrix.of_apply]
    have hset : setQBit N q 1 s = s := by
      have hq := setQBit_qBit N q s
      rw [h] at hq
      exact hq
    rw [hset]
  · have h0 : qBit q s.val = 0 := fin2_eq_zero_of_ne_one h
    simp [h0, Matrix.of_apply]
    have hset : setQBit N q 0 s = s := by
      have hq := setQBit_qBit N q s
      rw [h0] at hq
      exact hq
    rw [hset]

/-- CNOT acts as the CNOT permutation (pullback form). -/
theorem applyGate_cnot {N c t : ℕ} (hct : c ≠ t) (hcN : c < N) (htN : t < N)
    (ψ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    applyGate N (controlledGate xGate c t) ψ s = ψ (cnotIndex N c t s) := by
  have hwf : QGateWellFormed N (controlledGate xGate c t) :=
    controlledGate_wellFormed xGate xGate_unitary hct hcN htN
  rw [applyGate_controlledGate hwf ψ s]
  unfold cnotIndex
  by_cases hc : qBit c s.val = 1
  · simp only [hc, ite_true]
    rw [complexOfGRatMatrix_xGate]
    exact xFiber_collapse htN ψ s
  · simp only [hc, ite_false]

/-- The CNOT index map is an involution. -/
theorem cnotIndex_cnotIndex {N c t : ℕ} (hct : c ≠ t) (s : Fin (2 ^ N)) :
    cnotIndex N c t (cnotIndex N c t s) = s := by
  unfold cnotIndex
  by_cases hc : qBit c s.val = 1
  · have hbit : qBit c (flipBit N t s).val = 1 := by
      rw [qBit_flipBit_of_ne hct]
      exact hc
    simp [hc, hbit, flipBit_flipBit]
  · simp [hc]

/-- The Toffoli index map is an involution. -/
theorem toffoliIndex_toffoliIndex {N a b c : ℕ} (hac : a ≠ c) (hbc : b ≠ c) (s : Fin (2 ^ N)) :
    toffoliIndex N a b c (toffoliIndex N a b c s) = s := by
  unfold toffoliIndex
  by_cases h : qBit a s.val = 1 ∧ qBit b s.val = 1
  · obtain ⟨ha, hb⟩ := h
    have ha' : qBit a (flipBit N c s).val = 1 := by
      rw [qBit_flipBit_of_ne hac]
      exact ha
    have hb' : qBit b (flipBit N c s).val = 1 := by
      rw [qBit_flipBit_of_ne hbc]
      exact hb
    simp [ha, hb, ha', hb', flipBit_flipBit]
  · simp [h]

/-- `cnotIndex` as a permutation of basis indices, for distinct
control and target (the CNOT permutation when both are in range). -/
def cnotEquiv (N c t : ℕ) (hct : c ≠ t) : Equiv.Perm (Fin (2 ^ N)) :=
  Function.Involutive.toPerm (cnotIndex N c t) (cnotIndex_cnotIndex hct)

@[simp]
theorem cnotEquiv_apply (N c t : ℕ) (hct : c ≠ t) (s : Fin (2 ^ N)) :
    cnotEquiv N c t hct s = cnotIndex N c t s :=
  rfl

/-- `toffoliIndex` as a permutation of basis indices, for a target
distinct from both controls (the Toffoli permutation when all
three indices are distinct and in range). -/
def toffoliEquiv (N a b c : ℕ) (hac : a ≠ c) (hbc : b ≠ c) : Equiv.Perm (Fin (2 ^ N)) :=
  Function.Involutive.toPerm (toffoliIndex N a b c) (toffoliIndex_toffoliIndex hac hbc)

@[simp]
theorem toffoliEquiv_apply (N a b c : ℕ) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Fin (2 ^ N)) :
    toffoliEquiv N a b c hac hbc s = toffoliIndex N a b c s :=
  rfl

/-- Embedded `X` on a basis state. -/
theorem applyGate_embeddedGate_xGate_single {N q p : ℕ} (hqp : q ≠ p) (hqN : q < N)
    (hpN : p < N) (s : Fin (2 ^ N)) :
    applyGate N (embeddedGate xGate q p) (Pi.single s 1) = Pi.single (flipBit N q s) 1 := by
  funext u
  rw [applyGate_embeddedGate_xGate hqp hqN hpN _ u, Pi.single_apply, Pi.single_apply]
  by_cases hu : u = flipBit N q s
  · subst hu
    simp [flipBit_flipBit]
  · have hu' : flipBit N q u ≠ s := by
      intro hcon
      apply hu
      have h2 := congrArg (flipBit N q) hcon
      rw [flipBit_flipBit] at h2
      exact h2
    simp [hu, hu']

/-- CNOT on a basis state. -/
theorem applyGate_cnot_single {N c t : ℕ} (hct : c ≠ t) (hcN : c < N) (htN : t < N)
    (s : Fin (2 ^ N)) :
    applyGate N (controlledGate xGate c t) (Pi.single s 1) = Pi.single (cnotIndex N c t s) 1 := by
  funext u
  rw [applyGate_cnot hct hcN htN _ u, Pi.single_apply, Pi.single_apply]
  by_cases hu : u = cnotIndex N c t s
  · subst hu
    simp [cnotIndex_cnotIndex hct s]
  · have hu' : cnotIndex N c t u ≠ s := by
      intro hcon
      apply hu
      have h2 := congrArg (cnotIndex N c t) hcon
      rw [cnotIndex_cnotIndex hct] at h2
      exact h2
    simp [hu, hu']

/-! ## The five-gate Toffoli -/

/-- **Five-gate Toffoli:** the encoded decomposition
`CV(b,c), CNOT(a,b), CV†(b,c), CNOT(a,b), CV(a,c)` is the Toffoli
permutation at arbitrary distinct positions, on every state vector. -/
theorem applyCircuit_toffoliGates {N a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haN : a < N) (hbN : b < N) (hcN : c < N) (ψ : Fin (2 ^ N) → ℂ) :
    applyCircuit N (toffoliGates a b c) ψ = toffoliPerm N a b c ψ := by
  have hwfVbc : QGateWellFormed N (controlledGate vGate b c) :=
    controlledGate_wellFormed vGate vGate_unitary hbc hbN hcN
  have hwfVd : QGateWellFormed N (controlledGate vDagGate b c) :=
    controlledGate_wellFormed vDagGate vDagGate_unitary hbc hbN hcN
  have hwfVac : QGateWellFormed N (controlledGate vGate a c) :=
    controlledGate_wellFormed vGate vGate_unitary hac haN hcN
  have hunfold : applyCircuit N (toffoliGates a b c) ψ =
      applyGate N (controlledGate vGate a c)
        (applyGate N (controlledGate xGate a b)
          (applyGate N (controlledGate vDagGate b c)
            (applyGate N (controlledGate xGate a b)
              (applyGate N (controlledGate vGate b c) ψ)))) := by
    simp [-Fin.sum_univ_two, applyCircuit, toffoliGates]
  funext s
  rw [hunfold]
  simp only [toffoliPerm, toffoliIndex]
  by_cases ha : qBit a s.val = 1
  · by_cases hb : qBit b s.val = 1
    · simp [-Fin.sum_univ_two, ha, hb]
      rw [applyGate_controlledGate hwfVac _ s]
      simp only [ha, ite_true]
      have ha_set : ∀ b2 : Fin 2, qBit a (setQBit N c b2 s).val = 1 := by
        intro b2
        rw [qBit_setQBit_of_ne hac]
        exact ha
      have hb_set : ∀ b2 : Fin 2, qBit b (setQBit N c b2 s).val = 1 := by
        intro b2
        rw [qBit_setQBit_of_ne hbc]
        exact hb
      simp only [applyGate_cnot hab haN hbN, cnotIndex, ha_set, ite_true]
      have hb_flip_ne : ∀ b2 : Fin 2,
          qBit b (flipBit N b (setQBit N c b2 s)).val ≠ 1 := by
        intro b2
        rw [qBit_flipBit_self hbN, hb_set b2]
        decide
      simp only [applyGate_controlledGate hwfVd, hb_flip_ne, ite_false]
      simp only [applyGate_cnot hab haN hbN, cnotIndex]
      have ha_flip : ∀ b2 : Fin 2,
          qBit a (flipBit N b (setQBit N c b2 s)).val = 1 := by
        intro b2
        rw [qBit_flipBit_of_ne hab, qBit_setQBit_of_ne hac]
        exact ha
      simp only [ha_flip, ite_true]
      have hcancel : ∀ b2 : Fin 2,
          flipBit N b (flipBit N b (setQBit N c b2 s)) = setQBit N c b2 s := by
        intro b2
        exact flipBit_flipBit N b (setQBit N c b2 s)
      simp only [hcancel]
      simp only [applyGate_controlledGate hwfVbc, hb_set, ite_true]
      simp only [qBit_setQBit_self hcN, setQBit_setQBit hcN, fiber_collapse_V_V]
      exact xFiber_collapse hcN ψ s
    · simp [-Fin.sum_univ_two, ha, hb]
      rw [applyGate_controlledGate hwfVac _ s]
      simp only [ha, ite_true]
      have ha_set : ∀ b2 : Fin 2, qBit a (setQBit N c b2 s).val = 1 := by
        intro b2
        rw [qBit_setQBit_of_ne hac]
        exact ha
      have hb0 : qBit b s.val = 0 := fin2_eq_zero_of_ne_one hb
      have hb_set0 : ∀ b2 : Fin 2, qBit b (setQBit N c b2 s).val = 0 := by
        intro b2
        rw [qBit_setQBit_of_ne hbc]
        exact hb0
      simp only [applyGate_cnot hab haN hbN, cnotIndex, ha_set, ite_true]
      have hb_flip1 : ∀ b2 : Fin 2,
          qBit b (flipBit N b (setQBit N c b2 s)).val = 1 := by
        intro b2
        rw [qBit_flipBit_self hbN, hb_set0 b2]
        decide
      simp only [applyGate_controlledGate hwfVd, hb_flip1,
        complexOfGRatMatrix_vDagGate, ite_true]
      have ha_flip_set : ∀ b2 b3 : Fin 2,
          qBit a (setQBit N c b3 (flipBit N b (setQBit N c b2 s))).val = 1 := by
        intro b2 b3
        rw [qBit_setQBit_of_ne hac, qBit_flipBit_of_ne hab, qBit_setQBit_of_ne hac]
        exact ha
      simp only [applyGate_cnot hab haN hbN, cnotIndex, ha_flip_set, ite_true]
      have hflip_cancel : ∀ b2 b3 : Fin 2,
          flipBit N b (setQBit N c b3 (flipBit N b (setQBit N c b2 s))) =
            setQBit N c b3 (setQBit N c b2 s) := by
        intro b2 b3
        rw [flipBit_setQBit_comm (q := c) (r := b) hbc.symm, flipBit_flipBit N b _]
      simp only [hflip_cancel, setQBit_setQBit hcN]
      have hb_set3_ne : ∀ b3 : Fin 2,
          qBit b (setQBit N c b3 s).val ≠ 1 := by
        intro b3
        rw [qBit_setQBit_of_ne hbc, hb0]
        decide
      simp only [applyGate_controlledGate hwfVbc, hb_set3_ne, ite_false]
      simp only [qBit_flipBit_of_ne hbc.symm, qBit_setQBit_self hcN,
        fiber_collapse_V_starV, setQBit_qBit]
  · simp [-Fin.sum_univ_two, ha]
    rw [applyGate_controlledGate hwfVac _ s]
    simp only [ha, ite_false]
    simp only [applyGate_cnot hab haN hbN, cnotIndex, ha, ite_false]
    by_cases hb : qBit b s.val = 1
    · simp only [applyGate_controlledGate hwfVd, hb,
        complexOfGRatMatrix_vDagGate, ite_true]
      have ha_set0 : ∀ b1 : Fin 2, qBit a (setQBit N c b1 s).val ≠ 1 := by
        intro b1
        rw [qBit_setQBit_of_ne hac]
        exact ha
      simp only [applyGate_cnot hab haN hbN, cnotIndex, ha_set0, ite_false]
      have hb_set1 : ∀ b1 : Fin 2, qBit b (setQBit N c b1 s).val = 1 := by
        intro b1
        rw [qBit_setQBit_of_ne hbc]
        exact hb
      simp only [applyGate_controlledGate hwfVbc, hb_set1, ite_true]
      simp only [qBit_setQBit_self hcN, setQBit_setQBit hcN,
        fiber_collapse_starV_V, setQBit_qBit]
    · simp only [applyGate_controlledGate hwfVd, hb, ite_false]
      simp only [applyGate_cnot hab haN hbN, cnotIndex, ha, ite_false]
      simp only [applyGate_controlledGate hwfVbc, hb, ite_false]

/-- Five-gate Toffoli on a basis state. -/
theorem applyCircuit_toffoliGates_single {N a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (haN : a < N) (hbN : b < N) (hcN : c < N) (s : Fin (2 ^ N)) :
    applyCircuit N (toffoliGates a b c) (Pi.single s 1) =
      Pi.single (toffoliIndex N a b c s) 1 := by
  have hmain := applyCircuit_toffoliGates hab hac hbc haN hbN hcN (Pi.single s 1)
  funext u
  rw [hmain]
  simp only [toffoliPerm]
  rw [Pi.single_apply, Pi.single_apply]
  by_cases hu : u = toffoliIndex N a b c s
  · subst hu
    simp [toffoliIndex_toffoliIndex hac hbc s]
  · have hu' : toffoliIndex N a b c u ≠ s := by
      intro hcon
      apply hu
      have h2 := congrArg (toffoliIndex N a b c) hcon
      rw [toffoliIndex_toffoliIndex hac hbc] at h2
      exact h2
    simp [hu, hu']

/-- **Clean-target form:** on states vanishing on the target-`1` branch,
the five-gate Toffoli writes the AND of the controls into the target. -/
theorem applyCircuit_toffoliGates_clean {N a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (haN : a < N) (hbN : b < N) (hcN : c < N) {ψ : Fin (2 ^ N) → ℂ}
    (hψ : ∀ s : Fin (2 ^ N), qBit c s.val = 1 → ψ s = 0) (s : Fin (2 ^ N)) :
    applyCircuit N (toffoliGates a b c) ψ s =
      if qBit c s.val = (if qBit a s.val = 1 ∧ qBit b s.val = 1 then 1 else 0)
      then ψ (setQBit N c 0 s) else 0 := by
  have hmain := applyCircuit_toffoliGates hab hac hbc haN hbN hcN ψ
  have hpt : applyCircuit N (toffoliGates a b c) ψ s = ψ (toffoliIndex N a b c s) := by
    rw [hmain]
    rfl
  rw [hpt]
  unfold toffoliIndex
  by_cases hand : qBit a s.val = 1 ∧ qBit b s.val = 1
  · simp [hand]
    by_cases hqc : qBit c s.val = 1
    · simp [hqc]
      congr 1
      have hflip := setQBit_add_one_eq_flipBit hcN s
      rw [hqc] at hflip
      have h11 : (1 : Fin 2) + 1 = 0 := by decide
      rw [h11] at hflip
      exact hflip.symm
    · have hqc0 : qBit c s.val = 0 := fin2_eq_zero_of_ne_one hqc
      simp [hqc]
      have hbit : qBit c (flipBit N c s).val = 1 := by
        rw [qBit_flipBit_self hcN, hqc0]
        decide
      rw [hψ _ hbit]
  · simp [hand]
    by_cases hqc : qBit c s.val = 0
    · simp [hqc]
      have hset : setQBit N c 0 s = s := by
        have hq := setQBit_qBit N c s
        rw [hqc] at hq
        exact hq
      rw [hset]
    · have hqc1 : qBit c s.val = 1 := by
        by_contra hcon
        exact hqc (fin2_eq_zero_of_ne_one hcon)
      simp [hqc]
      rw [hψ _ hqc1]

end Cslib.Complexity.Classes.QuantumGates
