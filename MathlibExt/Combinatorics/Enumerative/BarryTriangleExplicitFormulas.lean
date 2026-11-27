/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Matrix.Mul

/-!
# Explicit formulas for Barry's triangle

The matrix-free formula expresses entries of Barry's triangle as sums of weighted monomials
over tuples of natural numbers with prescribed sum. The matrix power formula obtains the same
entries from the first column of a power of a lower bidiagonal matrix.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Barry's triangle recurrence.** The function $s(\beta, n, k)$ of natural numbers
$\beta, n, k$, with natural-number values, is defined by $s(\beta, 0, 0) = 1$, by
$s(\beta, n, k) = 0$ if exactly one of $n, k$ is $0$, and by
$$s(\beta, n, k) = s(\beta + 1, n - 1, k - 1) + \beta k\, s(\beta, n - 1, k)$$
if $n, k \ge 1$.

The triangle OEIS A080416 is $s(0, n, k)$ for $2 \le k \le n$.

Source: Bulat Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of
Integer Sequences 29 (2026), Article 26.2.8, equation (1). -/
public def barryTriangleAux : ℕ → ℕ → ℕ → ℕ
  | _, 0, 0 => 1
  | _, 0, _ + 1 => 0
  | _, _ + 1, 0 => 0
  | β, n + 1, k + 1 => barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1)

/-- **Defining recurrence of Barry's triangle.** For all natural numbers $\beta, n, k$, Barry's
triangle recurrence $s$ satisfies
$s(\beta, n + 1, k + 1) = s(\beta + 1, n, k) + \beta (k + 1)\, s(\beta, n, k + 1)$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, equation (1). -/
public theorem barryTriangleAux_succ_succ (β n k : ℕ) :
    barryTriangleAux β (n + 1) (k + 1) =
      barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1) :=
  rfl

/-- **Small values of Barry's triangle.** Barry's triangle recurrence $s$ takes the values
$s(0, 2, 2) = 1$, $s(0, 4, 3) = 4$ and $s(0, 6, 4) = 67$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, Table 1. -/
public theorem barryTriangleAux_small_values :
    barryTriangleAux 0 2 2 = 1 ∧ barryTriangleAux 0 4 3 = 4 ∧ barryTriangleAux 0 6 4 = 67 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

namespace BarryTriangle

open Finset.Nat (antidiagonalTuple mem_antidiagonalTuple)

private def weightedSum {k : ℕ} (w : Fin k → ℕ) (d : ℕ) : ℕ :=
  ∑ p ∈ antidiagonalTuple k d, ∏ i, w i ^ p i

private theorem weightedSum_zero {k : ℕ} (w : Fin k → ℕ) : weightedSum w 0 = 1 := by
  simp [weightedSum, Finset.Nat.antidiagonalTuple_zero_right]

-- A tuple either starts with zero, or can be obtained by incrementing its first exponent.
private theorem weightedSum_succ {k : ℕ} (w : Fin (k + 1) → ℕ) (d : ℕ) :
    weightedSum w (d + 1) = weightedSum (Fin.tail w) (d + 1) + w 0 * weightedSum w d := by
  classical
  unfold weightedSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p 0 = 0), Finset.mul_sum]
  congr 1
  · apply Finset.sum_nbij' Fin.tail (Fin.cons 0)
    · intro p hp
      obtain ⟨hs, hz⟩ := Finset.mem_filter.mp hp
      simpa [mem_antidiagonalTuple, Fin.sum_univ_succ p, hz, Fin.tail] using hs
    · intro p hp
      simpa [mem_antidiagonalTuple, Fin.sum_cons] using hp
    · intro p hp
      rw [← (Finset.mem_filter.mp hp).2, Fin.cons_self_tail]
    · simp
    · intro p hp
      rw [Fin.prod_univ_succ]
      simp [(Finset.mem_filter.mp hp).2, Fin.tail]
  · apply Finset.sum_nbij'
      (fun p => Fin.cons (p 0 - 1) (Fin.tail p))
      (fun p => Fin.cons (p 0 + 1) (Fin.tail p))
    · intro p hp
      obtain ⟨hs, hn⟩ := Finset.mem_filter.mp hp
      rw [mem_antidiagonalTuple, Fin.sum_univ_succ] at hs
      rw [mem_antidiagonalTuple, Fin.sum_cons]
      unfold Fin.tail
      omega
    · intro p hp
      rw [mem_antidiagonalTuple, Fin.sum_univ_succ] at hp
      simp [mem_antidiagonalTuple, Fin.sum_cons, Fin.tail, ← hp, Nat.add_right_comm]
    · intro p hp
      have hn := (Finset.mem_filter.mp hp).2
      simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    · simp
    · intro p hp
      have hn := (Finset.mem_filter.mp hp).2
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]

private theorem barryTriangleAux_of_lt (β n k : ℕ) (h : n < k) : barryTriangleAux β n k = 0 := by
  induction n generalizing β k with
  | zero => cases k <;> simp_all [barryTriangleAux]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [barryTriangleAux_succ_succ, ih _ k (by omega), ih _ (k + 1) (by omega)]

private theorem barryTriangleAux_self (β k : ℕ) : barryTriangleAux β k k = 1 := by
  induction k generalizing β with
  | zero => rfl
  | succ k ih =>
    simp [barryTriangleAux_succ_succ, ih, barryTriangleAux_of_lt β k (k + 1) (by omega)]

-- After k obligatory diagonal steps, d counts the remaining steps at the k possible weights.
private theorem barryTriangleAux_add (β k d : ℕ) :
    barryTriangleAux β (k + d) k =
      weightedSum (fun i : Fin k => (β + i.val) * (k - i.val)) d := by
  induction k generalizing β d with
  | zero => cases d <;> simp [weightedSum, barryTriangleAux]
  | succ k ih =>
    induction d with
    | zero => simp [barryTriangleAux_self, weightedSum_zero]
    | succ d ihd =>
      rw [Nat.add_succ, barryTriangleAux_succ_succ, weightedSum_succ, ihd]
      rw [Nat.succ_add, ← Nat.add_succ, ih]
      simp +unfoldPartialApp [Fin.tail, Nat.add_right_comm, Nat.add_assoc]

-- Row i corresponds to column i + 1 of the triangle.
private def barryTriangleMatrix (a : ℕ) : Matrix (Fin (a - 1)) (Fin (a - 1)) ℕ :=
  Matrix.of fun i j =>
    if i = j then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1))
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

private theorem barryTriangleMatrix_mul_apply (a : ℕ)
    (X : Matrix (Fin (a - 1)) (Fin (a - 1)) ℕ) (i j : Fin (a - 1)) :
    (barryTriangleMatrix a * X) i j =
      ((i : ℕ) + 1) * (a - ((i : ℕ) + 1)) * X i j +
        (if h : 0 < (i : ℕ) then X ⟨(i : ℕ) - 1, by omega⟩ j else 0) := by
  rw [Matrix.mul_apply]
  have hterm (k : Fin (a - 1)) :
      barryTriangleMatrix a i k * X k j =
        (if i = k then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1)) * X k j else 0) +
          (if (i : ℕ) = (k : ℕ) + 1 then X k j else 0) := by
    by_cases hik : i = k
    · subst k
      simp [barryTriangleMatrix]
    · by_cases h : (i : ℕ) = (k : ℕ) + 1 <;> simp [barryTriangleMatrix, hik, h]
  simp only [hterm, Finset.sum_add_distrib, Fintype.sum_ite_eq]
  congr 1
  by_cases hi : 0 < (i : ℕ)
  · rw [dite_eq_left hi]
    let p : Fin (a - 1) := ⟨(i : ℕ) - 1, by omega⟩
    change _ = X p j
    rw [Finset.sum_eq_single p]
    · have hp : (i : ℕ) = (p : ℕ) + 1 := by
        change (i : ℕ) = (i : ℕ) - 1 + 1
        omega
      simp [hp]
    · intro k _ hk
      have hne : (i : ℕ) ≠ (k : ℕ) + 1 := by
        intro h
        apply hk
        apply Fin.ext
        change (k : ℕ) = (i : ℕ) - 1
        omega
      simp [hne]
    · simp
  · rw [dite_eq_right hi]
    exact Finset.sum_eq_zero fun k _ => ite_eq_right (by omega)

-- Fixing β + k = a, one multiplication advances n by one in every column.
private theorem barryTriangleAux_eq_pow_entry (a : ℕ) (ha : 2 ≤ a) (d : ℕ)
    (i : Fin (a - 1)) :
    barryTriangleAux (a - ((i : ℕ) + 1)) (d + 1) ((i : ℕ) + 1) =
      (barryTriangleMatrix a ^ d) i ⟨0, by omega⟩ := by
  let z : Fin (a - 1) := ⟨0, by omega⟩
  change _ = (barryTriangleMatrix a ^ d) i z
  induction d generalizing i with
  | zero =>
    rw [pow_zero]
    by_cases hi : i = z
    · subst i
      rw [Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne hi]
      have hz : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      exact barryTriangleAux_of_lt _ _ _ (by omega)
  | succ d ih =>
    rw [barryTriangleAux_succ_succ, pow_succ', barryTriangleMatrix_mul_apply, ← ih i]
    by_cases hi : 0 < (i : ℕ)
    · rw [dite_eq_left hi]
      let p : Fin (a - 1) := ⟨(i : ℕ) - 1, by omega⟩
      change _ = _ + (barryTriangleMatrix a ^ d) p z
      rw [← ih p]
      have hp : (p : ℕ) + 1 = (i : ℕ) := by
        change (i : ℕ) - 1 + 1 = (i : ℕ)
        omega
      have hβ : a - ((i : ℕ) + 1) + 1 = a - (i : ℕ) := by omega
      rw [hp, hβ, Nat.mul_comm (a - _) _, Nat.add_comm]
    · rw [dite_eq_right hi, show (i : ℕ) = 0 by omega]
      simp [barryTriangleAux]

end BarryTriangle

open BarryTriangle in
/-- **Matrix power formula for Barry's triangle.** Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Let $M$ be the $(a - 1) \times (a - 1)$ lower bidiagonal matrix of natural
numbers with diagonal entries $M_{i,i} = i(a - i)$ for $i = 1, \dots, a - 1$, entries
$M_{i+1,i} = 1$ just below the diagonal, and all other entries $0$. Then $s(0, n, a)$ is the
bottom-left entry $(M^{n-2})_{a-1,1}$ of the power $M^{n-2}$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, equation (4), taking the last entry of the resulting vector
(`jis-2026-26.2.8-abstract-main`). -/
public theorem barryTriangleAux_eq_matrix_pow (n a : ℕ) (ha : 2 ≤ a) (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ((Matrix.of fun i j : Fin (a - 1) =>
          if i = j then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1))
          else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) ^ (n - 2))
        ⟨a - 2, by omega⟩ ⟨0, by omega⟩ := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  rw [barryTriangleAux_succ_succ, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
  simpa [barryTriangleMatrix, show b + 2 - (b + 1) = 1 by omega] using
    barryTriangleAux_eq_pow_entry (b + 2) ha d ⟨b, by omega⟩

open BarryTriangle in
/-- **Matrix-free formula for Barry's triangle.** Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Then
$$s(0, n, a) = \sum_{p_1 + \dots + p_{a-1} = n - a} \prod_{i=1}^{a-1} \bigl(i(a - i)\bigr)^{p_i},$$
where the sum runs over all tuples $(p_1, \dots, p_{a-1})$ of natural numbers with sum $n - a$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, main result announced in the abstract, equation (11)
(`jis-2026-26.2.8-abstract-main`). -/
public theorem barryTriangleAux_eq_sum_antidiagonalTuple (n a : ℕ) (ha : 2 ≤ a)
    (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ∑ p ∈ Finset.Nat.antidiagonalTuple (a - 1) (n - a),
        ∏ i : Fin (a - 1), (((i : ℕ) + 1) * (a - ((i : ℕ) + 1))) ^ p i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le han
  rw [Nat.succ_add, barryTriangleAux_succ_succ]
  simp [barryTriangleAux_add, weightedSum, Nat.add_comm]

end

end MetaMathlibExt
