/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PerrinSequence
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# The only zero of the two-sided Perrin sequence

We define the backward extension of the Perrin sequence and show that the two-sided sequence
vanishes only at index one. Modulo eight the backward recurrence restricts any zero to one
residue class. Successive squaring of the transition matrix then forces divisibility of the
shifted index by arbitrarily high powers of two.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Perrin sequence at negative indices.** The Perrin sequence $R_k$, given by $R_0 = 3$,
$R_1 = 0$, $R_2 = 2$ and $R_{k+3} = R_{k+1} + R_k$, extends uniquely to all integers $k$ by
running the recurrence backward. This defines the integers $R_{-n}$ for natural numbers $n$:
$R_0 = 3$, $R_{-1} = -1$, $R_{-2} = 1$ and $R_{-(n+3)} = R_{-n} - R_{-(n+2)}$ for every $n \ge 0$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public def perrinNeg : ℕ → ℤ
  | 0 => 3
  | 1 => -1
  | 2 => 1
  | n + 3 => perrinNeg n - perrinNeg (n + 2)

/-- **The Perrin sequence and its backward extension fit together at index zero.** Write $R_n$
for the Perrin sequence and $R_{-n}$ for its extension to negative indices, for natural numbers
$n$. The two definitions give the same value at index $0$, and the Perrin recurrence holds across
index $0$: $R_2 = R_0 + R_{-1}$ and $R_1 = R_{-1} + R_{-2}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_bridge :
    perrinNeg 0 = (perrinSequence 0 : ℤ) ∧
      (perrinSequence 2 : ℤ) = perrinSequence 0 + perrinNeg 1 ∧
        (perrinSequence 1 : ℤ) = perrinNeg 1 + perrinNeg 2 := by
  decide

/-- **Perrin recurrence at negative indices.** Let $R_{-k}$ denote the Perrin sequence extended
to negative indices. For every natural number $n$, $R_{-n} = R_{-(n+2)} + R_{-(n+3)}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_rec (n : ℕ) :
    perrinNeg n = perrinNeg (n + 2) + perrinNeg (n + 3) := by
  rw [perrinNeg]; ring

/-- **Some values of the Perrin sequence at negative indices.** The Perrin sequence $R_k$
extended to negative indices satisfies $R_{-5} = 4$, $R_{-18} = 25$,
$R_{-1} = R_{-7} = R_{-11} = R_{-29} = -1$ and $R_{-2} = 1$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2 and 4. -/
public theorem perrinNeg_small_values :
    perrinNeg 5 = 4 ∧ perrinNeg 18 = 25 ∧ perrinNeg 1 = -1 ∧ perrinNeg 7 = -1 ∧
      perrinNeg 11 = -1 ∧ perrinNeg 29 = -1 ∧ perrinNeg 2 = 1 := by
  decide

end

namespace perrin_zero_unique

open scoped Matrix

/-- The Perrin term at index `1 - n`, so the known zero is at `n = 0`. -/
private def backwards : ℕ → ℤ
  | 0 => 0
  | n + 1 => perrinNeg n

private theorem backwards_rec (n : ℕ) :
    backwards (n + 3) = backwards n - backwards (n + 2) := by
  cases n with
  | zero => decide
  | succ n => exact perrinNeg.eq_4 n

private def state (n : ℕ) : Fin 3 → ℤ :=
  ![backwards n, backwards (n + 1), backwards (n + 2)]

private def step : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, -1]

private theorem step_state (n : ℕ) : step *ᵥ state n = state (n + 1) := by
  ext i
  fin_cases i <;>
    simp [step, state, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      backwards_rec, sub_eq_add_neg, Nat.add_assoc]

private theorem pow_mulVec_state (m n : ℕ) : step ^ m *ᵥ state n = state (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, step_state]
    rfl

/-- The integral matrix `(step ^ 28 - 1) / 8`. -/
private def block : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -3, 2; 2, 1, -5; -5, 2, 6]

private theorem step_pow_twenty_eight : step ^ 28 = 1 + (8 : ℤ) • block := by
  have h : step ^ 7 = !![-1, 0, 2; 2, -1, -2; -2, 2, 1] := by decide
  rw [show (28 : ℕ) = 7 * 2 * 2 by decide, pow_mul, pow_mul, h]
  decide

/-- After doubling the block length `k` times, the scaled deviation from the identity still
agrees with `block` modulo two. Taking `q` such steps multiplies the coefficient by `q`. -/
private theorem step_pow_blocks (k q : ℕ) :
    ∃ C : Matrix (Fin 3) (Fin 3) ℤ,
      step ^ (28 * 2 ^ k * q) = 1 + (8 * 2 ^ k : ℤ) • ((q : ℤ) • block + (2 : ℤ) • C) := by
  have h (k : ℕ) : ∃ C : Matrix (Fin 3) (Fin 3) ℤ,
      step ^ (28 * 2 ^ k) = 1 + (8 * 2 ^ k : ℤ) • (block + (2 : ℤ) • C) := by
    induction k with
    | zero => exact ⟨0, by simpa using step_pow_twenty_eight⟩
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      let D := block + (2 : ℤ) • C
      refine ⟨C + (2 * 2 ^ k : ℤ) • (D * D), ?_⟩
      rw [pow_succ (2 : ℕ), ← Nat.mul_assoc, pow_mul, hC, pow_two, pow_succ (2 : ℤ)]
      change (1 + (8 * 2 ^ k : ℤ) • D) * (1 + (8 * 2 ^ k : ℤ) • D) = _
      simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc]
      dsimp only [D]
      module
  obtain ⟨B, hB⟩ := h k
  rw [pow_mul]
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨C, hC⟩ := ih
    let D := block + (2 : ℤ) • B
    let E := (q : ℤ) • block + (2 : ℤ) • C
    refine ⟨C + B + (4 * 2 ^ k : ℤ) • (E * D), ?_⟩
    rw [pow_succ, hC, hB, Nat.cast_succ]
    change (1 + (8 * 2 ^ k : ℤ) • E) * (1 + (8 * 2 ^ k : ℤ) • D) = _
    simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    dsimp only [D, E]
    module

private theorem backwards_blocks (k q r : ℕ) :
    ∃ t : ℤ, backwards (r + 28 * 2 ^ k * q) =
      backwards r + (8 * 2 ^ k : ℤ) * ((q : ℤ) * (block *ᵥ state r) 0 + 2 * t) := by
  obtain ⟨C, hC⟩ := step_pow_blocks k q
  have h := congrFun (pow_mulVec_state (28 * 2 ^ k * q) r) 0
  rw [hC] at h
  refine ⟨(C *ᵥ state r) 0, ?_⟩
  simpa only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, state, Matrix.cons_val_zero, Nat.add_assoc] using h.symm

private theorem dvd_of_backwards_eq_zero {n : ℕ} (hn : backwards n = 0) : 28 ∣ n := by
  have hsmall : ∀ r : Fin 28, backwards r.val % 8 = 0 → r.val = 0 := by decide
  obtain ⟨t, ht⟩ := backwards_blocks 0 (n / 28) (n % 28)
  have hm := Nat.mod_add_div n 28
  simp only [pow_zero, mul_one] at ht
  rw [hm, hn] at ht
  have hmod : backwards (n % 28) % 8 = 0 := by
    have h := congrArg (· % 8) ht
    simpa [Int.add_emod, Int.mul_emod] using h.symm
  exact Nat.dvd_of_mod_eq_zero (hsmall ⟨n % 28, Nat.mod_lt _ (by decide)⟩ hmod)

private theorem backwards_eq_zero {n : ℕ} (hn : backwards n = 0) : n = 0 := by
  obtain ⟨m, rfl⟩ := dvd_of_backwards_eq_zero hn
  have hdvd (k : ℕ) : 2 ^ k ∣ m := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨q, rfl⟩ := ih
      obtain ⟨t, ht⟩ := backwards_blocks k q 0
      have hfirst : (block *ᵥ state 0) 0 = -11 := by decide
      rw [zero_add, mul_assoc, hn, hfirst] at ht
      have hzero : (8 * 2 ^ k : ℤ) * ((q : ℤ) * -11 + 2 * t) = 0 := by
        simpa [backwards] using ht.symm
      have hcoeff := (mul_eq_zero.mp hzero).resolve_left (by positivity)
      have hq : 2 ∣ q := by omega
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hq
  have hm : m = 0 := by
    by_contra h
    exact (Nat.lt_two_pow_self (n := m)).not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (hdvd m))
  simp [hm]

private theorem perrinSequence_pos (n : ℕ) (hn : 2 ≤ n) : 0 < perrinSequence n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : n < 4
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
      rw [Nat.add_comm 3 m, perrinSequence.eq_4]
      exact Nat.add_pos_left (ih (m + 1) (by omega) (by omega)) _

end perrin_zero_unique

/-- **The only zero of the two-sided Perrin sequence.** Let $R_n$ denote the $n$-th term of
the Perrin sequence and $R_{-n}$ the term at index $-n$ of its backward extension to negative
indices. For every natural number $n$, $R_n = 0$ if and only if $n = 1$, and $R_{-n} \ne 0$.
Thus $R_1 = 0$ is the only zero of the sequence $(R_k)_{k \in \mathbb{Z}}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 5
(`integers-2025-A70-thm-5`). -/
public theorem perrin_zero_unique :
    (∀ n : ℕ, perrinSequence n = 0 ↔ n = 1) ∧ ∀ n : ℕ, perrinNeg n ≠ 0 := by
  constructor
  · intro n
    constructor
    · intro hn
      by_contra h
      by_cases hzero : n = 0
      · subst n
        exact (by decide : perrinSequence 0 ≠ 0) hn
      · exact (perrin_zero_unique.perrinSequence_pos n (by omega)).ne' hn
    · rintro rfl
      rfl
  · intro n hn
    have hi : perrin_zero_unique.backwards (n + 1) = 0 := hn
    have := perrin_zero_unique.backwards_eq_zero hi
    omega

end MetaMathlibExt
