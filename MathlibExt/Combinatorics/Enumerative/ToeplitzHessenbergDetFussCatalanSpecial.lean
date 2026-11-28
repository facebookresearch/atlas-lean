/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK
import MathlibExt.Combinatorics.Enumerative.TrudiFussCatalan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Special Toeplitz–Hessenberg determinants of Fuss–Catalan numbers

The theorem `toeplitzHessenbergDet_fussCatalan_special` evaluates the signed Toeplitz–Hessenberg
determinants $D_n(p, r) = (-1)^{n-1} \det(1; A_1(p, r), \dots, A_n(p, r))$ of the Fuss–Catalan
numbers for $(p, r) = (2, 3), (2, 4), (3, 1), (3, 2)$: the first two are differences of Catalan
numbers, the last two are single binomial coefficients. The theorem `toeplitzHessenbergDet_ternary`
evaluates two determinants with shifted ternary Fuss–Catalan entries. The proofs combine Trudi's
formula with evaluations of the corresponding partition sums.

## References

* Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan
  Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, pp. 1–23. Corollary 4 and
  Theorem 8 give the determinant evaluations; Lemma 1 and Corollary 9 give the Trudi formula and
  the partition-sum evaluations used here.
* Taras Goy and Mark Shattuck, *Determinants of Some Hessenberg–Toeplitz Matrices with Motzkin
  Number Entries*, Journal of Integer Sequences 26 (2023), Article 23.3.4, pp. 1–21, Lemma 1
  (the determinant-to-sum conversion).
* Mircea Merca, *A note on the determinant of a Toeplitz-Hessenberg matrix*, Special Matrices
  1 (2013), pp. 10–16, Theorem 1 (Trudi's formula).
-/

namespace MetaMathlibExt
namespace toeplitzHessenbergDet_fussCatalan_special

-- Trudi's partition sum does not read the value at `0`.
private lemma trudi_congr (s : ℚ) (a b : ℕ → ℚ) (h : ∀ i, 0 < i → a i = b i) (n : ℕ) :
    trudiPartitionSum s a n = trudiPartitionSum s b n := by
  unfold trudiPartitionSum
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h _ (Nat.succ_pos _)]

-- Brioschi's formula and the Trudi multi-sum evaluation give `r/n * binom(pn - r - 1, n - 1)`.
private lemma signed_det (p r n : ℕ) (hn : 1 ≤ n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ) := by
  rw [toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum _ (by simp),
    trudi_congr _ _ (fun i => (generalizedFussCatalanNumber p i r : ℚ))
      (fun i hi => by simp [hi.ne']),
    ← trudiPartitionSum_fussCatalan.1 p r n hn]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel, pow_succ]
  rcases neg_one_pow_eq_or ℚ k with h | h <;> rw [h] <;> ring

-- The upper index `pn - r - 1` is a natural number once `r + 1 ≤ pn`.
private lemma signed_det_nat (p r n : ℕ) (hn : 1 ≤ n) (hr : r + 1 ≤ p * n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      (r : ℚ) / n * ((p * n - r - 1).choose (n - 1) : ℚ) := by
  rw [signed_det p r n hn, ← Ring.choose_natCast, Nat.sub_sub, Nat.cast_sub hr]
  push_cast
  ring_nf

-- Catalan numbers through central binomial coefficients.
private lemma catalan_eq (m : ℕ) : (catalan m : ℚ) = m.centralBinom / (m + 1) := by
  have h : ((m + 1 : ℕ) : ℚ) * catalan m = m.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom m
  push_cast at h
  field_simp
  linear_combination h

private lemma centralBinom_succ (m : ℕ) :
    ((m + 1).centralBinom : ℚ) = 2 * (2 * m + 1) * m.centralBinom / (m + 1) := by
  have h : ((m + 1 : ℕ) : ℚ) * (m + 1).centralBinom = 2 * (2 * m + 1) * m.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  push_cast at h
  field_simp
  linear_combination h

-- `D_n(2, 3) = 3/n * binom(2n - 4, n - 1)`, and `binom(2m, m + 1) = binom(2m, m) * m/(m + 1)`.
private lemma case_two_three (n : ℕ) (hn : 2 ≤ n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) n =
      (catalan (n - 1) : ℚ) - catalan (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [signed_det_nat 2 3 (m + 2) (by omega) (by omega),
    show 2 * (m + 2) - 3 - 1 = 2 * m by omega, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega]
  have hX : (((2 * m).choose (m + 1) : ℕ) : ℚ) = m.centralBinom * m / (m + 1) := by
    have h := Nat.choose_succ_right_eq (2 * m) m
    rw [show 2 * m - m = m by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
    have h' : (((2 * m).choose (m + 1) : ℕ) : ℚ) * (m + 1) = m.centralBinom * m := by
      exact_mod_cast h
    field_simp
    linear_combination h'
  rw [catalan_eq, catalan_eq, centralBinom_succ, hX]
  push_cast
  field_simp
  ring

-- `D_n(2, 4) = 4/n * binom(2n - 5, n - 1)`, rewritten through `binom(2m + 1, m + 1)`.
private lemma case_two_four (n : ℕ) (hn : 3 ≤ n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) n =
      (catalan (n - 1) : ℚ) - 2 * catalan (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [signed_det_nat 2 4 (m + 3) (by omega) (by omega),
    show 2 * (m + 3) - 4 - 1 = 2 * m + 1 by omega, show m + 3 - 1 = m + 2 by omega,
    show m + 3 - 2 = m + 1 by omega]
  have hZ : (((2 * m + 1).choose (m + 1) : ℕ) : ℚ) =
      (2 * m + 1) * m.centralBinom / (m + 1) := by
    have h := Nat.add_one_mul_choose_eq (2 * m) m
    rw [← Nat.centralBinom_eq_two_mul_choose] at h
    have h' : (((2 * m + 1).choose (m + 1) : ℕ) : ℚ) * (m + 1) =
        (2 * m + 1) * m.centralBinom := by
      exact_mod_cast h.symm
    field_simp
    linear_combination h'
  have hY : (((2 * m + 1).choose (m + 2) : ℕ) : ℚ) =
      ((2 * m + 1).choose (m + 1) : ℕ) * m / (m + 2) := by
    have h := Nat.choose_succ_right_eq (2 * m + 1) (m + 1)
    rw [show 2 * m + 1 - (m + 1) = m by omega] at h
    have h' : (((2 * m + 1).choose (m + 2) : ℕ) : ℚ) * (m + 2) =
        ((2 * m + 1).choose (m + 1) : ℕ) * m := by
      exact_mod_cast h
    field_simp
    linear_combination h'
  rw [catalan_eq, catalan_eq, centralBinom_succ, centralBinom_succ, hY, hZ]
  push_cast
  field_simp
  ring

private lemma case_three_one (n : ℕ) (hn : 1 ≤ n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 1 : ℚ)) n =
      1 / (n : ℚ) * ((3 * n - 2).choose (n - 1) : ℚ) := by
  rw [signed_det_nat 3 1 n hn (by omega), show 3 * n - 1 - 1 = 3 * n - 2 by omega,
    Nat.cast_one]

private lemma case_three_two (n : ℕ) (hn : 1 ≤ n) :
    (-1) ^ (n - 1) * toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 2 : ℚ)) n =
      2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ) := by
  rw [signed_det_nat 3 2 n hn (by omega), show 3 * n - 2 - 1 = 3 * n - 3 by omega,
    Nat.cast_ofNat]

end toeplitzHessenbergDet_fussCatalan_special

open toeplitzHessenbergDet_fussCatalan_special

/-- **Special Toeplitz–Hessenberg determinants of Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal. For natural numbers $p, r \ge 1$ let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$
be the generalized Fuss–Catalan number, put
$D_n(p, r) = (-1)^{n-1} \det(1; A_1(p, r), \dots, A_n(p, r))$, and let $C_n$ be the $n$-th
Catalan number. Then, in $\mathbb{Q}$: $D_n(2, 3) = C_{n-1} - C_{n-2}$ for every $n \ge 2$;
$D_n(2, 4) = C_{n-1} - 2 C_{n-2}$ for every $n \ge 3$;
$D_n(3, 1) = \frac{1}{n} \binom{3n - 2}{n - 1}$ for every $n \ge 1$; and
$D_n(3, 2) = \frac{2}{n} \binom{3n - 3}{n - 1}$ for every $n \ge 1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 4
(`jis-2026-26.1.2-cor-4`). -/
public theorem toeplitzHessenbergDet_fussCatalan_special :
    (∀ n : ℕ, 2 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) n =
        (catalan (n - 1) : ℚ) - catalan (n - 2)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) n =
        (catalan (n - 1) : ℚ) - 2 * catalan (n - 2)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 1 : ℚ)) n =
        1 / (n : ℚ) * ((3 * n - 2).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 2 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ) :=
  ⟨case_two_three, case_two_four, case_three_one, case_three_two⟩

/-- **Toeplitz–Hessenberg determinants of ternary Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal, and let $H_n = \frac{1}{3n + 1} \binom{3n + 1}{n}$ and
$J_n = \frac{2}{3n + 2} \binom{3n + 2}{n}$. Then, in $\mathbb{Q}$,
$\det(1; H_2, H_3, \dots, H_{n+1}) = \frac{2 (-1)^{n-1}}{n} \binom{3n - 3}{n - 1}$ for every
$n \ge 2$, and $\det(-1; J_0, J_1, \dots, J_{n-1}) = H_n$ for every $n \ge 1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 8, equations
(21) and (23) (`jis-2026-26.1.2-thm-8`). -/
public theorem toeplitzHessenbergDet_ternary :
    (∀ n : ℕ, 2 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 * (-1) ^ (n - 1) / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ) := by
  constructor
  · intro n hn
    have hsign : (-1 : ℚ) ^ n = (-1) ^ (n - 1) * (-1) := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
    rw [toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum _ (by simp),
      trudi_congr _ _ (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ))
        (fun i hi => by simp [hi.ne']),
      hsign, mul_assoc, neg_one_mul, trudiPartitionSum_fussCatalan.2.2.2.1 n hn]
    ring
  · intro n hn
    rw [toeplitzHessenbergDet_eq_trudiPartitionSum_one _ (by simp),
      trudi_congr _ _ (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ))
        (fun i hi => by simp [hi.ne'])]
    exact trudiPartitionSum_fussCatalan.2.2.2.2 n hn

end MetaMathlibExt
