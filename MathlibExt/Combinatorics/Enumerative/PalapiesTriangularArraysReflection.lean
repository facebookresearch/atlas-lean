/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PalapiesTriangularArrays
import Mathlib.Tactic.Ring

/-!
# Reflection of triangular recurrence arrays

Reflection exchanges the negative-positive and negative-negative extensions of a triangular
recurrence, including their divisor conditions.
-/

namespace MetaMathlibExt.TriangularRecurrence

private theorem reflect_weight_swap (P : TriangularRecurrence) (n k : ℤ) :
    P.reflect.weight n k = P.weight' n (n + 1 - k) := by
  simp [reflect, weight, weight']
  ring

private theorem reflect_weight'_swap (P : TriangularRecurrence) (n k : ℤ) :
    P.reflect.weight' n k = P.weight n (n + 1 - k) := by
  simp [reflect, weight, weight']
  ring

private theorem negPos_ofNat_succ (P : TriangularRecurrence) (n : ℕ) (k : ℤ) :
    P.negPos (↑(n + 1) : ℤ) k =
      P.weight n k * P.negPos (n : ℤ) k + P.weight' n k * P.negPos (n : ℤ) (k - 1) := by
  cases k with
  | ofNat k =>
    cases k with
    | zero =>
      change P.array (n + 1) 0 =
        P.weight n 0 * P.array n 0 + P.weight' n 0 * 0
      simp [array, weight]
    | succ k =>
      rw [show Int.ofNat (k + 1) - 1 = (k : ℤ) by rw [Int.ofNat_eq_natCast]; omega]
      change P.array (n + 1) (k + 1) =
        P.weight n (k + 1) * P.array n (k + 1) +
          P.weight' n (k + 1) * P.array n k
      simp [array, weight, weight']
  | negSucc k =>
    rw [show Int.negSucc k - 1 = Int.negSucc (k + 1) by omega]
    simp [negPos]

private theorem reflect_negPos_ofNat (P : TriangularRecurrence) (n : ℕ) (k : ℤ) :
    P.reflect.negPos (n : ℤ) k = P.negPos (n : ℤ) (n - k) := by
  induction n generalizing k with
  | zero =>
    rw [Nat.cast_zero, zero_sub]
    have row_zero (Q : TriangularRecurrence) (j : ℤ) :
        Q.negPos 0 j = if j = 0 then 1 else 0 := by
      cases j <;> simp [negPos, array, Int.ofNat_eq_natCast]
    simp [row_zero]
  | succ n ih =>
    rw [negPos_ofNat_succ, negPos_ofNat_succ, reflect_weight_swap, reflect_weight'_swap, ih, ih]
    rw [show (↑(n + 1) : ℤ) - k = n + 1 - k by push_cast; ring,
      show (n : ℤ) - (k - 1) = n + 1 - k by ring,
      show (n : ℤ) + 1 - k - 1 = n - k by ring, add_comm]

-- In a negative row, the offset from the diagonal in the NN array equals the NP column.
private theorem reflect_negPosAux_eq_negNegAux (P : TriangularRecurrence) (p k : ℕ) :
    P.reflect.negPosAux p k = P.negNegAux p k := by
  induction p generalizing k with
  | zero =>
    induction k with
    | zero =>
      simp [negPosAux, negNegAux, reflect_weight_swap]
    | succ k ih =>
      rw [negPosAux, negNegAux, ih, reflect_weight_swap, reflect_weight'_swap]
      simp
  | succ p ih =>
    induction k with
    | zero =>
      rw [negPosAux, negNegAux, ih, reflect_weight_swap]
      ring_nf
    | succ k hk =>
      rw [negPosAux, negNegAux, ih, hk, reflect_weight_swap, reflect_weight'_swap]
      ring_nf

private theorem reflect_negPos_eq_negNeg_aux (P : TriangularRecurrence) (n k : ℤ) :
    P.reflect.negPos n k = P.negNeg n (n - k) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, reflect_negPos_ofNat]
    generalize (n : ℤ) - k = j
    cases n <;> cases j <;> simp [negPos, negNeg, array.eq_1, Int.ofNat_eq_natCast]
  | negSucc p =>
    cases k with
    | ofNat k =>
      rw [negPos, negNeg, Int.ofNat_eq_natCast]
      rw [ite_eq_left (by omega), sub_sub_cancel, Int.toNat_natCast,
        reflect_negPosAux_eq_negNegAux]
    | negSucc k =>
      have h : ¬ Int.negSucc p - Int.negSucc k ≤ Int.negSucc p := by omega
      simp [negPos, negNeg, h]

/-- **NP/NN duality.** Let $a$ be the array of a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, with weights
$w(n, k) = \alpha(n + 1) + \beta k + \gamma$ and $w'(n, k) = \alpha'(n + 1) + \beta' k + \gamma'$,
and let $\tilde a$ be the array of the reflected recurrence, with parameters
$(\alpha' + \beta', -\beta', \gamma'; \alpha + \beta, -\beta, \gamma)$ and weights $\tilde w$,
$\tilde w'$. Then for all integers $n, k$ the negative-positive and negative-negative numbers
satisfy $\tilde a^{NP}_{n,k} = a^{NN}_{n,n-k}$ and $\tilde a^{NN}_{n,n-k} = a^{NP}_{n,k}$.
Moreover, $\tilde w(n, k) \ne 0$ for all integers $n < 0 \le k$ if and only if
$w'(n, k + 1) \ne 0$ for all integers $k \le n < 0$; and $\tilde w'(n, k + 1) \ne 0$ for all
integers $k \le n < 0$ if and only if $w(n, k) \ne 0$ for all integers $n < 0 \le k$.

Thus the divisor condition of Definition 1 for $\tilde a$ is equivalent to that of Definition 2
for $a$, and conversely, so the left-hand sides exist exactly when the right-hand sides do.
With junk value $0$ for a zero divisor, the two identities need no existence hypothesis.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 3. -/
public theorem reflect_negPos_eq_negNeg
    (P : TriangularRecurrence) :
    (∀ n k : ℤ, P.reflect.negPos n k = P.negNeg n (n - k)) ∧
    (∀ n k : ℤ, P.reflect.negNeg n (n - k) = P.negPos n k) ∧
    ((∀ n k : ℤ, n < 0 → 0 ≤ k → P.reflect.weight n k ≠ 0) ↔
      ∀ n k : ℤ, k ≤ n → n < 0 → P.weight' n (k + 1) ≠ 0) ∧
    ((∀ n k : ℤ, k ≤ n → n < 0 → P.reflect.weight' n (k + 1) ≠ 0) ↔
      ∀ n k : ℤ, n < 0 → 0 ≤ k → P.weight n k ≠ 0) := by
  refine ⟨reflect_negPos_eq_negNeg_aux P, ?_, ?_, ?_⟩
  · intro n k
    simpa only [reflect_reflect] using (reflect_negPos_eq_negNeg_aux P.reflect n k).symm
  · constructor
    · intro h n k hkn hn
      simpa only [reflect_weight_swap, show n + 1 - (n - k) = k + 1 by omega] using
        h n (n - k) hn (by omega)
    · intro h n k hn hk
      simpa only [reflect_weight_swap, show n - k + 1 = n + 1 - k by omega] using
        h n (n - k) (by omega) hn
  · constructor
    · intro h n k hn hk
      simpa only [reflect_weight'_swap, show n + 1 - (n - k + 1) = k by omega] using
        h n (n - k) (by omega) hn
    · intro h n k hkn hn
      simpa only [reflect_weight'_swap, show n + 1 - (k + 1) = n - k by omega] using
        h n (n - k) hn (by omega)

end MetaMathlibExt.TriangularRecurrence
