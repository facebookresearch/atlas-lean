/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Sum of the Delannoy triangle entries in rows `0` to `p - 1`

This module proves `MathlibExt.NumberTheory.DelannoyTriangleWanted.sum_delannoy`: for an
odd prime `p`, the sum of the entries `T(n, k; 1)` of the Delannoy triangle over
`0 ≤ n < p` and `0 ≤ k ≤ n` is congruent to the Legendre symbol `(2 / p)` modulo `p`.

Statements from Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle Coefficients",
*Journal of Integer Sequences* 29 (2026), Article 26.5.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Djadi/djadi6.html>).
-/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- Row sum of the Delannoy triangle. -/
private def rowSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1

/-- Trinomial identity for the Delannoy summand. -/
private theorem choose_mul_choose (n k j : ℕ) (hjk : j ≤ k) :
    (k.choose j : ℤ) * ((n - j).choose k : ℤ)
      = ((n - j).choose j : ℤ) * ((n - 2 * j).choose (k - j) : ℤ) := by
  have h := Nat.choose_mul (n := n - j) hjk
  have hsub : (n - j) - j = n - 2 * j := by omega
  rw [hsub] at h
  rw [mul_comm ((k.choose j : ℕ) : ℤ)]
  exact_mod_cast h

/-- The `r = 1` entry sum extends from `k + 1` to `n + 1` terms. -/
private theorem sum_entry_eq (n k : ℕ) (hkn : k ≤ n) :
    MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1
      = ∑ j ∈ Finset.range (n + 1),
        (k.choose j : ℤ) * ((n - j).choose k : ℤ) := by
  unfold MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
  simp only [one_pow, mul_one]
  have hss : Finset.range (k + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  apply Finset.sum_subset hss
  intro x _ hx
  simp only [Finset.mem_range] at hx
  have h0 : k.choose x = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h0]

/-- Inner sum over `k` for fixed `n` and `j`. -/
private theorem sum_k_choose_mul (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (k.choose j : ℤ) * ((n - j).choose k : ℤ)
      = ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j) := by
  by_cases hj : j ≤ n - j
  · have hsub : Finset.Ico j (n + 1) ⊆ Finset.range (n + 1) := by
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    have hvan : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.Ico j (n + 1) →
        (x.choose j : ℤ) * ((n - j).choose x : ℤ) = 0 := by
      intro x hxmem hxnot
      simp only [Finset.mem_range, Finset.mem_Ico] at hxmem hxnot
      have hxj : x < j := by omega
      have h0 : x.choose j = 0 := Nat.choose_eq_zero_of_lt hxj
      simp [h0]
    rw [← Finset.sum_subset hsub hvan]
    have hterm : ∀ k ∈ Finset.Ico j (n + 1),
        (k.choose j : ℤ) * ((n - j).choose k : ℤ)
          = ((n - j).choose j : ℤ) * ((n - 2 * j).choose (k - j) : ℤ) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      exact choose_mul_choose n k j hk.1
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    have harg : ∀ t ∈ Finset.range (n + 1 - j),
        ((n - 2 * j).choose (j + t - j) : ℤ) = (((n - 2 * j).choose t : ℕ) : ℤ) := by
      intro t _
      have ht : j + t - j = t := by omega
      rw [ht]
    rw [Finset.sum_congr rfl harg]
    have hsub2 : Finset.range (n - 2 * j + 1) ⊆ Finset.range (n + 1 - j) :=
      Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
    have hvan2 : ∀ x ∈ Finset.range (n + 1 - j), x ∉ Finset.range (n - 2 * j + 1) →
        (((n - 2 * j).choose x : ℕ) : ℤ) = 0 := by
      intro x _ hx
      simp only [Finset.mem_range] at hx
      have h0 : (n - 2 * j).choose x = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
    rw [← Finset.sum_subset hsub2 hvan2]
    exact_mod_cast Nat.sum_range_choose (n - 2 * j)
  · have hj' : n - j < j := not_le.mp hj
    have hR : ((n - j).choose j : ℤ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt hj'
    rw [hR, zero_mul]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkj : k < j
    · have h0 : k.choose j = 0 := Nat.choose_eq_zero_of_lt hkj
      simp [h0]
    · have hkj' : j ≤ k := not_lt.mp hkj
      have h0 : (n - j).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]

/-- Closed form of the row sum. -/
private theorem rowSum_eq (n : ℕ) :
    rowSum n = ∑ j ∈ Finset.range (n + 1),
      ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j) := by
  unfold rowSum
  have h1 : ∀ k ∈ Finset.range (n + 1),
      MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1
        = ∑ j ∈ Finset.range (n + 1),
          (k.choose j : ℤ) * ((n - j).choose k : ℤ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    exact sum_entry_eq n k (by omega)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_k_choose_mul n j

/-- The row sums satisfy the Pell recurrence. -/
private theorem rowSum_succ_succ (n : ℕ) :
    rowSum (n + 2) = 2 * rowSum (n + 1) + rowSum n := by
  simp only [rowSum_eq]
  have h2 : (∑ j ∈ Finset.range (n + 2 + 1),
        ((n + 2 - j).choose j : ℤ) * 2 ^ (n + 2 - 2 * j))
      = (∑ j ∈ Finset.range (n + 2),
        ((n + 2 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 2 - 2 * (j + 1)))
        + ((n + 2 - 0).choose 0 : ℤ) * 2 ^ (n + 2 - 2 * 0) :=
    Finset.sum_range_succ' _ _
  have h1 : (∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1 - j).choose j : ℤ) * 2 ^ (n + 1 - 2 * j))
      = (∑ j ∈ Finset.range (n + 1),
        ((n + 1 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 1 - 2 * (j + 1)))
        + ((n + 1 - 0).choose 0 : ℤ) * 2 ^ (n + 1 - 2 * 0) :=
    Finset.sum_range_succ' _ _
  have hext0 : (∑ j ∈ Finset.range (n + 1),
        ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j))
      = ∑ j ∈ Finset.range (n + 2),
        ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j) := by
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro x _ hx
    simp only [Finset.mem_range] at hx
    have h0c : (n - x).choose x = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0c]
  have hext1 : (∑ j ∈ Finset.range (n + 1),
        ((n + 1 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 1 - 2 * (j + 1)))
      = ∑ j ∈ Finset.range (n + 2),
        ((n + 1 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 1 - 2 * (j + 1)) := by
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro x _ hx
    simp only [Finset.mem_range] at hx
    have he : n + 1 - (x + 1) = n - x := by omega
    have h0c : (n - x).choose (x + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [he]
    simp [h0c]
  rw [h2, h1, hext1, hext0]
  have hterm : ∀ j ∈ Finset.range (n + 2),
      ((n + 2 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 2 - 2 * (j + 1))
      = 2 * (((n + 1 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 1 - 2 * (j + 1)))
        + ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j) := by
    intro j _
    by_cases hA : 2 * (j + 1) ≤ n + 1
    · have hP := Nat.choose_succ_succ (n - j) j
      have e1 : n + 2 - (j + 1) = (n - j) + 1 := by omega
      have e2 : n + 1 - (j + 1) = n - j := by omega
      have hexp0 : n + 2 - 2 * (j + 1) = n - 2 * j := by omega
      have hE : (2 : ℤ) * 2 ^ (n + 1 - 2 * (j + 1)) = 2 ^ (n - 2 * j) := by
        rw [← pow_succ']
        congr 1
        omega
      have hPc : (((n - j) + 1).choose (j + 1) : ℤ)
          = ((n - j).choose (j + 1) : ℤ) + ((n - j).choose j : ℤ) := by
        exact_mod_cast hP.trans (add_comm _ _)
      rw [e1, e2, hexp0, hPc, add_mul]
      congr 1
      rw [← mul_assoc, mul_comm (2 : ℤ), mul_assoc, hE]
    · have hB : n + 1 < 2 * (j + 1) := by omega
      by_cases hJn : j ≤ n
      · have e1 : n + 2 - (j + 1) = (n - j) + 1 := by omega
        have e2 : n + 1 - (j + 1) = n - j := by omega
        have hexp0 : n + 2 - 2 * (j + 1) = n - 2 * j := by omega
        have hP := Nat.choose_succ_succ (n - j) j
        have hC2 : ((n - j).choose (j + 1) : ℤ) = 0 := by
          exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n - j < j + 1)
        have hC1 : (((n - j) + 1).choose (j + 1) : ℤ)
            = ((n - j).choose j : ℤ) := by
          have hPc : (((n - j) + 1).choose (j + 1) : ℤ)
              = ((n - j).choose (j + 1) : ℤ) + ((n - j).choose j : ℤ) := by
            exact_mod_cast hP.trans (add_comm _ _)
          rw [hPc, hC2, zero_add]
        rw [e1, e2, hexp0, hC1, hC2]
        ring
      · have hJn' : n < j := by omega
        have hC1 : ((n + 2 - (j + 1)).choose (j + 1) : ℤ) = 0 := by
          exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n + 2 - (j + 1) < j + 1)
        have hC2 : ((n + 1 - (j + 1)).choose (j + 1) : ℤ) = 0 := by
          exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n + 1 - (j + 1) < j + 1)
        have hC3 : ((n - j).choose j : ℤ) = 0 := by
          exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n - j < j)
        rw [hC1, hC2, hC3]
        ring
  have hsum : (∑ j ∈ Finset.range (n + 2),
        ((n + 2 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 2 - 2 * (j + 1)))
      = (∑ j ∈ Finset.range (n + 2),
        2 * (((n + 1 - (j + 1)).choose (j + 1) : ℤ) * 2 ^ (n + 1 - 2 * (j + 1))))
        + ∑ j ∈ Finset.range (n + 2),
          ((n - j).choose j : ℤ) * 2 ^ (n - 2 * j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hbase : ((n + 2 - 0).choose 0 : ℤ) * 2 ^ (n + 2 - 2 * 0)
      = 2 * (((n + 1 - 0).choose 0 : ℤ) * 2 ^ (n + 1 - 2 * 0)) := by
    simp only [mul_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have he : n + 2 = (n + 1) + 1 := by omega
    rw [he, pow_succ']
  rw [hsum, mul_add, Finset.mul_sum, hbase]
  abel

/-- Initial row sums. -/
private theorem rowSum_zero : rowSum 0 = 1 := by decide

private theorem rowSum_one : rowSum 1 = 2 := by decide

/-- Row sums viewed in `ZMod p`. -/
private def r (p n : ℕ) : ZMod p := (rowSum n : ZMod p)

/-- The Pell recurrence in `ZMod p`. -/
private theorem r_succ_succ (p n : ℕ) :
    r p (n + 2) = 2 * r p (n + 1) + r p n := by
  have h := congrArg (Int.cast : ℤ → ZMod p) (rowSum_succ_succ n)
  simpa [r] using h

/-- The `0`-th row sum in `ZMod p`. -/
private theorem r_zero (p : ℕ) : r p 0 = 1 := by
  have h := congrArg (Int.cast : ℤ → ZMod p) rowSum_zero
  simpa [r] using h

/-- The first row sum in `ZMod p`. -/
private theorem r_one (p : ℕ) : r p 1 = 2 := by
  have h := congrArg (Int.cast : ℤ → ZMod p) rowSum_one
  simpa [r] using h

/-- The second row sum in `ZMod p`. -/
private theorem r_two (p : ℕ) : r p 2 = 5 := by
  have h := r_succ_succ p 0
  rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl,
    r_zero, r_one] at h
  rw [h]
  ring

/-- Multiplication by the Pell matrix. -/
private theorem mat_mul_entries (p : ℕ) (a b c d : ZMod p) :
    (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![a, b; c, d]
      = !![2 * a + c, 2 * b + d; a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Powers of the Pell matrix hold consecutive row sums. -/
private theorem mat_pow (p n : ℕ) :
    (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (n + 2)
      = !![r p (n + 2), r p (n + 1); r p (n + 1), r p n] := by
  induction n with
  | zero =>
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl,
      pow_two, r_zero, r_one, r_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  | succ n ih =>
    have e2 : n + 1 + 1 = n + 2 := by omega
    rw [e2]
    have hMn : (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (n + 1 + 2)
        = (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
          * (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (n + 2) := by
      rw [show n + 1 + 2 = (n + 2) + 1 from by omega, pow_succ']
    rw [hMn, ih, mat_mul_entries]
    have hrec1 : r p (n + 1 + 2) = 2 * r p (n + 2) + r p (n + 1) := by
      have h := r_succ_succ p (n + 1)
      rw [e2] at h
      exact h
    have hrec2 : r p (n + 2) = 2 * r p (n + 1) + r p n := r_succ_succ p n
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hrec1, hrec2]

/-- Splitting the Pell matrix for Frobenius. -/
private theorem mat_freshman (p : ℕ) [Fact p.Prime] :
    (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = 1 + (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p := by
  have hM : (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      = 1 + !![1, 1; 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  rw [hM, add_pow_char_of_commute p (Commute.one_left _), one_pow]

/-- The square of the traceless part. -/
private theorem mat_K_sq (p : ℕ) :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2 = !![2, 0; 0, 2] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Powers of the diagonal square. -/
private theorem mat_diag_pow (p m : ℕ) :
    (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ m
      = !![(2 : ZMod p) ^ m, 0; 0, (2 : ZMod p) ^ m] := by
  induction m with
  | zero =>
    rw [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ m ih =>
    rw [pow_succ', ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ']

/-- The `p`-th power of the traceless part for odd `p`. -/
private theorem mat_K_pow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = !![(2 : ZMod p) ^ (p / 2), (2 : ZMod p) ^ (p / 2);
           (2 : ZMod p) ^ (p / 2), -((2 : ZMod p) ^ (p / 2))] := by
  have hprime : p.Prime := Fact.out
  have hmod : p % 2 = 1 := by
    rcases hprime.eq_two_or_odd with h | h
    · omega
    · exact h
  have hKK : ∀ t : ℕ, (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (2 * t + 1)
      = (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p))
        * ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2) ^ t := by
    intro t
    rw [pow_succ', pow_mul]
  have hexp : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod p),
      M ^ p = M ^ (2 * (p / 2) + 1) := by
    intro M
    congr 1
    omega
  rw [hexp, hKK, mat_K_sq, mat_diag_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The `p`-th power of the Pell matrix. -/
private theorem mat_pow_p (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (!![2, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = !![1 + (2 : ZMod p) ^ (p / 2), (2 : ZMod p) ^ (p / 2);
           (2 : ZMod p) ^ (p / 2), 1 - (2 : ZMod p) ^ (p / 2)] := by
  rw [mat_freshman p, mat_K_pow p hp2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

/-- Reading the entries of `M ^ p`. -/
private theorem mat_pow_p_entries (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    !![r p p, r p (p - 1); r p (p - 1), r p (p - 2)]
      = !![1 + (2 : ZMod p) ^ (p / 2), (2 : ZMod p) ^ (p / 2);
           (2 : ZMod p) ^ (p / 2), 1 - (2 : ZMod p) ^ (p / 2)] := by
  have hprime : p.Prime := Fact.out
  have h2le : 2 ≤ p := hprime.two_le
  have hEq := mat_pow p (p - 2)
  have e1 : p - 2 + 2 = p := by omega
  have e2 : p - 2 + 1 = p - 1 := by omega
  rw [e1, e2] at hEq
  have hF := mat_pow_p p hp2
  rw [hEq] at hF
  exact hF

/-- The `(p - 1)`-st row sum is `2 ^ (p / 2)`. -/
private theorem r_pred_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    r p (p - 1) = (2 : ZMod p) ^ (p / 2) := by
  have hF := mat_pow_p_entries p hp2
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 1) hF
  simpa using h01

/-- The `(p - 2)`-nd row sum. -/
private theorem r_pred_pred_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    r p (p - 2) = 1 - (2 : ZMod p) ^ (p / 2) := by
  have hF := mat_pow_p_entries p hp2
  have h11 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 1) hF
  simpa using h11

/-- Euler's criterion for `2`. -/
private theorem euler_two (p : ℕ) [Fact p.Prime] :
    (2 : ZMod p) ^ (p / 2) = ((legendreSym p 2 : ℤ) : ZMod p) := by
  have h := legendreSym.eq_pow p (2 : ℤ)
  simpa using h.symm

/-- Peeling one term off the top of the total sum. -/
private theorem sum_top_one (p : ℕ) [Fact p.Prime] :
    (∑ n ∈ Finset.range p, r p n)
      = (∑ n ∈ Finset.range (p - 1), r p n) + r p (p - 1) := by
  have hprime : p.Prime := Fact.out
  have h1le : 1 ≤ p := by
    have h2le := hprime.two_le
    omega
  have h := Finset.sum_range_succ (fun n => r p n) (p - 1)
  have e : (p - 1) + 1 = p := by omega
  rw [e] at h
  exact h

/-- Peeling two terms off the top of the total sum. -/
private theorem sum_top_two (p : ℕ) [Fact p.Prime] :
    (∑ n ∈ Finset.range p, r p n)
      = (∑ i ∈ Finset.range (p - 2), r p i) + r p (p - 2) + r p (p - 1) := by
  have hprime : p.Prime := Fact.out
  have h2le : 2 ≤ p := hprime.two_le
  have h1 := sum_top_one p
  have h2 : (∑ n ∈ Finset.range (p - 1), r p n)
      = (∑ i ∈ Finset.range (p - 2), r p i) + r p (p - 2) := by
    have h := Finset.sum_range_succ (fun n => r p n) (p - 2)
    have e : (p - 2) + 1 = p - 1 := by omega
    rw [e] at h
    exact h
  rw [h1, h2]

/-- The shifted middle sum. -/
private theorem sum_mid_shift (p : ℕ) [Fact p.Prime] :
    (∑ i ∈ Finset.range (p - 2), r p (i + 1))
      = (∑ n ∈ Finset.range p, r p n) - r p 0 - r p (p - 1) := by
  have hprime : p.Prime := Fact.out
  have h2le : 2 ≤ p := hprime.two_le
  have h := Finset.sum_range_succ' (fun n => r p n) (p - 2)
  have e : (p - 2) + 1 = p - 1 := by omega
  rw [e] at h
  have h1 := sum_top_one p
  linear_combination -h - h1

/-- The doubly shifted sum. -/
private theorem sum_top_shift (p : ℕ) [Fact p.Prime] :
    (∑ i ∈ Finset.range (p - 2), r p (i + 2))
      = (∑ n ∈ Finset.range p, r p n) - r p 0 - r p 1 := by
  have hprime : p.Prime := Fact.out
  have h2le : 2 ≤ p := hprime.two_le
  have h2 : (∑ n ∈ Finset.range 2, r p n) = r p 0 + r p 1 := by
    have h := Finset.sum_range_succ (fun n => r p n) 1
    have h' := Finset.sum_range_succ (fun n => r p n) 0
    have e2 : (1 : ℕ) + 1 = 2 := rfl
    have e1 : (0 : ℕ) + 1 = 1 := rfl
    rw [e2] at h
    rw [e1] at h'
    rw [h'] at h
    rw [Finset.sum_range_zero, zero_add] at h
    exact h
  have hsplit := Finset.sum_range_add_sum_Ico (fun n => r p n) h2le
  have hIco : (∑ n ∈ Finset.Ico 2 p, r p n)
      = ∑ i ∈ Finset.range (p - 2), r p (i + 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show r p (2 + i) = r p (i + 2)
    rw [add_comm (2 : ℕ) i]
  linear_combination hsplit - hIco - h2

/-- Twice the total sum in terms of the top row sums. -/
private theorem two_mul_sum (p : ℕ) [Fact p.Prime] :
    2 * (∑ n ∈ Finset.range p, r p n)
      = 3 * r p (p - 1) + r p (p - 2) - 1 := by
  have hvan : (∑ i ∈ Finset.range (p - 2), r p (i + 2))
      - 2 * (∑ i ∈ Finset.range (p - 2), r p (i + 1))
      - (∑ i ∈ Finset.range (p - 2), r p i) = 0 := by
    have h0 : ∑ i ∈ Finset.range (p - 2),
        (r p (i + 2) - 2 * r p (i + 1) - r p i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have h := r_succ_succ p i
      linear_combination h
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
    exact h0
  have htop2 := sum_top_two p
  have hmid := sum_mid_shift p
  have hbot := sum_top_shift p
  rw [r_zero p] at hmid
  rw [r_zero p, r_one p] at hbot
  linear_combination htop2 + hbot - hvan - 2 * hmid

/-- Two is nonzero modulo an odd prime. -/
private theorem two_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hprime : p.Prime := Fact.out
  have h2le := hprime.two_le
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega

/-- **Sum of the Delannoy triangle entries in rows $0$ to $p - 1$ modulo $p$.** Let $p$ be an
odd prime and let $T(n, k; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle
with $r = 1$ (the Delannoy triangle). Then
$$\sum_{n=0}^{p-1} \sum_{k=0}^{n} T(n, k; 1) \equiv \left(\frac{2}{p}\right) \pmod{p},$$
where $\left(\frac{2}{p}\right)$ is the Legendre symbol.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 9. -/
public theorem sum_delannoy (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (∑ n ∈ Finset.range p, ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            n k 1 : ZMod p)) =
      (legendreSym p 2 : ZMod p) := by
  have hS : (∑ n ∈ Finset.range p, ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1 : ZMod p))
      = ∑ n ∈ Finset.range p, r p n := by
    apply Finset.sum_congr rfl
    intro n _
    unfold r rowSum
    exact (Int.cast_sum _ _).symm
  rw [hS]
  have h2S := two_mul_sum p
  have hr1 := r_pred_eq p hp2
  have hr2 := r_pred_pred_eq p hp2
  have he := euler_two p
  rw [hr1, hr2, he] at h2S
  have h2ne := two_ne_zero p hp2
  have hfin : 2 * (∑ n ∈ Finset.range p, r p n)
      = 2 * ((legendreSym p 2 : ℤ) : ZMod p) := by
    linear_combination h2S
  exact mul_left_cancel₀ h2ne hfin

end MathlibExt.NumberTheory.DelannoyTriangleWanted
