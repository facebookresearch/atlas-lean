/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.Combinatorics.Enumerative.StirlingMatrix
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Block
import MathlibExt.Combinatorics.Enumerative.StirlingMatrices
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Matrices whose entries are Stirling numbers of the second kind

Results from M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima
Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind
(I)*, INTEGERS 25 (2025), Article A27.

Conventions. `S(n, k)` is `Nat.stirlingSecond` and the signed Stirling number of
the first kind `s(n, k)` is MathlibExt's `signedStirlingFirst`. The `n × n`
matrices are `Matrix (Fin n) (Fin n) ℚ`, entry `(a, b)` being the paper's
`(a + 1, b + 1)` entry. The Stirling matrix of the second kind `S(n)` is the
existing `stirlingMatrix2`. The paper takes `n` positive; for `n = 0` every
matrix identity below is trivial, so no hypothesis on `n` is added.

## Main results

* `stirlingVMatrix_inv` (Lemma 1): `V(n)⁻¹ = Ṽ(n)`.
* `stirlingQMatrix_succ` (Lemma 2) and `stirlingQMatrix_eq_one_mul_pow`
  (Corollary 1): `Q^[N](n) = Q^[1](n) (V(n) - I_n)^{N-1}`.
* `stirlingMatrix2_mul_sub_one` (Lemma 3) and `stirlingMatrix2_mul_sub_one_pow`
  (Theorem 1): `S(n) (V(n) - I_n)^N = E(n) Q^[N](n)`.
* `stirlingSecondShiftMatrix_eq_mul_pow` (Theorem 2):
  `S^[m](n) = S(n) V(n)^m` and `det S^[m](n) = n!^m`.
* `stirlingSecondShiftMatrix_succ` (Corollary 2) and
  `stirlingSecondShiftMatrix_add` (Corollary 3).
* `stirlingSecondShiftMatrix_inv` (Theorem 3): `S^[m](n)⁻¹ = Ṽ(n)^m s(n)`.
* The summation identities `sum_signedStirlingFirst_mul_stirlingSecond_add`
  (Theorem 4), `sum_choose_stirlingSecond_eq` (Theorem 5),
  `stirlingSecond_succ_sub_eq_sum` (Corollary 4),
  `sum_sum_stirlingSecond_signedStirlingFirst_eq_ite` (Theorem 6),
  `sum_stirlingSecond_succ_eq_ite` (Theorem 7) and
  `sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond` (Theorem 8).

## Proof outline

Column `c` of `M V(n)` is `c + 1` times column `c` of `M` plus column `c - 1`
(`mul_stirlingVMatrix_apply`). For `M = S^[m](n)` this is the recurrence
`Nat.stirlingSecond_succ_succ`, so `S^[m+1](n) = S^[m](n) V(n)`; Theorem 2
follows by induction on `m`, with `det S(n) = 1` (`det_stirlingMatrix2`) and
`det V(n) = n!` (`det_stirlingVMatrix`) because both matrices are triangular.
The row form `stirlingVMatrix_mul_apply` gives `V(n) Ṽ(n) = I_n` and hence
Lemma 1. The orthogonality `sum_signedStirlingFirst_mul_stirlingSecond` gives
`s(n) S(n) = I_n` (`stirlingFirstMatrix_mul_stirlingMatrix2`); with Theorem 2
this yields Corollary 3, `s(n) S^[m](n) = V(n)^m` and Theorem 3.

Lemma 2 is an entrywise computation with the column formula for
`M (V(n) - I_n)`, and Corollary 1 follows by induction. Theorem 5 is proved
directly from the explicit formula `stirlingSecond_mul_factorial_eq_sum` and
the binomial theorem (`sum_choose_stirlingSecond_eq_sum_pow`); Corollary 4 is
its case `N = 1`. Lemma 3 is Corollary 4 read entrywise, and Theorem 1 combines
Lemma 3 with Corollary 1.

Theorems 4, 6, 7 and 8 are single entries of matrix identities:
`s(i) S^[m](i) = V(i)^m` for Theorem 4 (the lower triangle of `V(n)^m` is
`stirlingVMatrix_pow_apply_of_le`), `S^[1](n) Ṽ(n) s(n) = I_n` for Theorem 6,
`S^[1](n') Ṽ(n') = S(n')` with `n' = max i j` for Theorem 7, and Corollary 3
for Theorem 8. In Theorems 6, 7 and 8 the case `j = 0` (outside the matrix)
is checked directly: both sides vanish. In Theorem 7 the right side equals
`S(i, j)` in all cases, since `S(i, j) = 0` for `j > i`.
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- The shifted Stirling matrix `S^[m](n)` with entries `S(i + m, j)`,
`1 ≤ i, j ≤ n`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
def stirlingSecondShiftMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (Nat.stirlingSecond (a.val + 1 + m) (b.val + 1) : ℚ)

/-- `S^[0](n) = S(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
theorem stirlingSecondShiftMatrix_zero (n : ℕ) :
    stirlingSecondShiftMatrix 0 n = stirlingMatrix2 n := by
  ext a b
  simp [stirlingSecondShiftMatrix, stirlingMatrix2]

/-- The first column of `S^[m](n)` is all ones: `S(i + m, 1) = 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1, Equation (5). -/
theorem stirlingSecondShiftMatrix_apply_zero_right {m n : ℕ} (a : Fin n)
    (h : 0 < n) : stirlingSecondShiftMatrix m n a ⟨0, h⟩ = 1 := by
  simp only [stirlingSecondShiftMatrix, Matrix.of_apply]
  rw [show a.val + 1 + m = (a.val + m) + 1 by omega,
    Nat.stirlingSecond_one_right]
  simp

/-- The Stirling matrix of the first kind `s(n)` with entries `s(i, j)`
(zero above the diagonal).

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `s(n)`). -/
def stirlingFirstMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (signedStirlingFirst (a.val + 1) (b.val + 1) : ℚ)

/-- The diagonal of `s(n)` is all ones.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (`s(n, n) = 1`). -/
theorem stirlingFirstMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingFirstMatrix n a a = 1 := by
  simp [stirlingFirstMatrix, signedStirlingFirst, Nat.stirlingFirst_self]

/-- The upper bidiagonal matrix `V(n)`: `V_{i,i} = i`, `V_{i,i+1} = 1`, zero
elsewhere.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
def stirlingVMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if b = a then (a.val + 1 : ℚ) else if b.val = a.val + 1 then 1 else 0

/-- `V(n)_{i,i} = i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
theorem stirlingVMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVMatrix n a a = a.val + 1 := by
  simp [stirlingVMatrix]

/-- The upper triangular matrix `Ṽ(n)` with `Ṽ_{i,j} = (-1)^{j-i} (i-1)! / j!`
for `j ≥ i`, zero otherwise.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
def stirlingVTildeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a ≤ b then
      (-1 : ℚ) ^ (b.val - a.val) * (a.val.factorial : ℚ) /
        ((b.val + 1).factorial : ℚ)
    else 0

/-- `Ṽ(n)_{i,i} = 1 / i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
theorem stirlingVTildeMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVTildeMatrix n a a = 1 / (a.val + 1 : ℚ) := by
  simp only [stirlingVTildeMatrix, Matrix.of_apply, le_refl, ite_true,
    Nat.sub_self, pow_zero, one_mul, Nat.factorial_succ, Nat.cast_mul]
  have h : (a.val.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  push_cast
  ring

/-- The matrix `E(n)` with `E_{i,j} = (j + 1)^{i-1}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
def shiftedVandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 2 : ℕ) : ℚ) ^ a.val

/-- The first row of `E(n)` is all ones.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
theorem shiftedVandermondeMatrix_apply_zero_left {n : ℕ} (h : 0 < n)
    (b : Fin n) : shiftedVandermondeMatrix n ⟨0, h⟩ b = 1 := by
  simp [shiftedVandermondeMatrix]

/-- The strictly upper triangular matrix `Q^[N](n)` with
`Q^[N]_{i,j} = (-1)^{j-i+1} i^{N-1} / ((i-1)! (j-i-1)!)` for `j ≥ i + 1`, zero
otherwise.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
def stirlingQMatrix (N n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a.val + 1 ≤ b.val then
      (-1 : ℚ) ^ (b.val - a.val + 1) * ((a.val + 1 : ℕ) : ℚ) ^ (N - 1) /
        ((a.val.factorial : ℚ) * ((b.val - a.val - 1).factorial : ℚ))
    else 0

/-- `Q^[N](n)` vanishes on and below the diagonal.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
theorem stirlingQMatrix_apply_of_le {N n : ℕ} {a b : Fin n} (h : b ≤ a) :
    stirlingQMatrix N n a b = 0 := by
  have : ¬ a.val + 1 ≤ b.val := by
    have := Fin.le_iff_val_le_val.1 h
    omega
  simp only [stirlingQMatrix, Matrix.of_apply, this, ↓reduceIte]

open Finset Matrix
open scoped Nat

/-! ### Reindexing finite sums -/

/-- For `c ≤ n`, a sum over `range c` is the sum over `Fin n` of the terms
with index `< c`. -/
theorem sum_range_eq_sum_fin_ite {M : Type*} [AddCommMonoid M]
    {c n : ℕ} (hc : c ≤ n) (f : ℕ → M) :
    ∑ k ∈ range c, f k = ∑ b : Fin n, if b.val < c then f b.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < c then f k else 0) n,
    ← sum_subset (range_subset_range.2 hc)]
  · exact sum_congr rfl fun k hk => (ite_eq_left (mem_range.1 hk)).symm
  · intro k _ hk
    exact ite_eq_right (by simpa using hk)

/-- For `1 ≤ k`, a sum over `Icc k n` is the sum over `Icc 1 n` of the terms
with index `≥ k`. -/
theorem sum_Icc_eq_sum_Icc_one_ite {M : Type*} [AddCommMonoid M]
    {k n : ℕ} (hk : 1 ≤ k) (f : ℕ → M) :
    ∑ l ∈ Icc k n, f l = ∑ l ∈ Icc 1 n, if k ≤ l then f l else 0 := by
  rw [← sum_filter]
  congr 1
  ext l
  simp only [mem_Icc, mem_filter]
  omega

/-! ### Multiplication by `V(n)` -/

/-- Column `c` of `M V(n)` is `c + 1` times column `c` of `M`, plus column
`c - 1` of `M` when `c ≥ 1` (`0`-based indices). -/
theorem mul_stirlingVMatrix_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n) :
    (M * stirlingVMatrix n) a c =
      M a c * (c.val + 1) +
        if h : c.val = 0 then 0 else M a ⟨c.val - 1, by omega⟩ := by
  have hV : ∀ b : Fin n, stirlingVMatrix n b c =
      (if c = b then (b.val + 1 : ℚ) else 0) +
        if c.val = b.val + 1 then 1 else 0 := fun b => by
    by_cases hcb : c = b
    · subst hcb
      simp [stirlingVMatrix]
    · simp [stirlingVMatrix, hcb]
  simp only [mul_apply, hV, mul_add, sum_add_distrib, mul_ite, mul_zero,
    mul_one, sum_ite_eq, mem_univ, ite_true]
  congr 1
  split_ifs with h
  · exact sum_eq_zero fun b _ => ite_eq_right (by omega)
  · rw [sum_eq_single ⟨c.val - 1, by omega⟩, ite_eq_left (by simp only; omega)]
    · intro b _ hb
      exact ite_eq_right fun h' => hb (Fin.ext (by simp only; omega))
    · simp

/-- Row `a` of `V(n) M` is `a + 1` times row `a` of `M`, plus row `a + 1` of
`M` when `a + 1 < n` (`0`-based indices). -/
theorem stirlingVMatrix_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n) :
    (stirlingVMatrix n * M) a c =
      (a.val + 1) * M a c +
        if h : a.val + 1 < n then M ⟨a.val + 1, h⟩ c else 0 := by
  have hV : ∀ b : Fin n, stirlingVMatrix n a b =
      (if a = b then (a.val + 1 : ℚ) else 0) +
        if b.val = a.val + 1 then 1 else 0 := fun b => by
    by_cases hab : a = b
    · subst hab
      simp [stirlingVMatrix]
    · simp [stirlingVMatrix, Ne.symm hab, hab]
  simp only [mul_apply, hV, add_mul, sum_add_distrib, ite_mul, zero_mul,
    one_mul, sum_ite_eq, mem_univ, ite_true]
  congr 1
  split_ifs with h
  · rw [sum_eq_single ⟨a.val + 1, h⟩, ite_eq_left rfl]
    · intro b _ hb
      exact ite_eq_right fun h' => hb (Fin.ext h')
    · simp
  · exact sum_eq_zero fun b _ => ite_eq_right (by omega)

/-- `V(n) Ṽ(n) = I_n`. -/
theorem stirlingVMatrix_mul_stirlingVTildeMatrix (n : ℕ) :
    stirlingVMatrix n * stirlingVTildeMatrix n = 1 := by
  ext a c
  rw [stirlingVMatrix_mul_apply, one_apply]
  simp only [stirlingVTildeMatrix, of_apply, Fin.le_def]
  rcases lt_trichotomy a.val c.val with h | h | h
  · obtain ⟨d, hd⟩ : ∃ d, c.val = a.val + 1 + d :=
      ⟨c.val - (a.val + 1), by omega⟩
    rw [dite_eq_left (by omega), ite_eq_left h.le, ite_eq_left (by omega),
      ite_eq_right (Fin.ne_of_lt h), show c.val - a.val = d + 1 by omega,
      show c.val - (a.val + 1) = d by omega, Nat.factorial_succ a.val]
    push_cast
    ring
  · obtain rfl : a = c := Fin.ext h
    have : (a.val ! : ℚ) ≠ 0 := by positivity
    rw [ite_eq_left le_rfl, ite_eq_left rfl, Nat.sub_self,
      Nat.factorial_succ a.val]
    split_ifs with h1 h2
    · omega
    all_goals
      push_cast
      field_simp
      ring
  · rw [ite_eq_right (by omega), ite_eq_right (Fin.ne_of_gt h)]
    split_ifs with h1 h2
    · omega
    all_goals ring

/-- Lemma 1: `V(n)⁻¹ = Ṽ(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 1 (`integers-2025-A27-lem-1`).

Proves `Wanted` entry `stirlingVMatrix_inv`. -/
theorem stirlingVMatrix_inv (n : ℕ) :
    (stirlingVMatrix n)⁻¹ = stirlingVTildeMatrix n :=
  inv_eq_right_inv (stirlingVMatrix_mul_stirlingVTildeMatrix n)

/-- `V(n)` is upper triangular with diagonal `1, 2, …, n`, so
`det V(n) = n!`. -/
theorem det_stirlingVMatrix (n : ℕ) : (stirlingVMatrix n).det = n ! := by
  rw [det_of_isUpperTriangular fun a b h => by
      have h' : b.val < a.val := h
      simp only [stirlingVMatrix, of_apply, Fin.ext_iff]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]]
  simp only [stirlingVMatrix_apply_self]
  rw [Fin.prod_univ_eq_prod_range (fun i => (i : ℚ) + 1),
    ← prod_range_add_one_eq_factorial]
  push_cast
  rfl

/-- `V(n)^m` is upper triangular with diagonal entries `(a + 1)^m`. -/
theorem stirlingVMatrix_pow_apply_of_le {n : ℕ} (m : ℕ) {a b : Fin n}
    (h : b ≤ a) :
    (stirlingVMatrix n ^ m) a b = if a = b then (a.val + 1 : ℚ) ^ m else 0 := by
  induction m generalizing b with
  | zero => simp [one_apply]
  | succ m ih =>
    have hz : (if hb : b.val = 0 then (0 : ℚ) else
        (stirlingVMatrix n ^ m) a ⟨b.val - 1, by omega⟩) = 0 := by
      split_ifs with hb
      · rfl
      · rw [ih (Fin.le_def.2 (by simp only [Fin.le_def] at h ⊢; omega)),
          ite_eq_right]
        intro hab
        have := congrArg Fin.val hab
        simp only at this
        omega
    rw [pow_succ, mul_stirlingVMatrix_apply, ih h, hz, add_zero]
    split_ifs with hab
    · subst hab
      ring
    · ring

/-! ### `s(n)` and `S(n)` -/

/-- `S(n)` is lower unitriangular, so `det S(n) = 1`. -/
theorem det_stirlingMatrix2 (n : ℕ) : (stirlingMatrix2 n).det = 1 := by
  rw [det_of_isLowerTriangular _ fun a b h => by
    simp only [stirlingMatrix2, of_apply]
    rw [Nat.stirlingSecond_eq_zero_of_lt (by simpa using h), Nat.cast_zero]]
  simp [stirlingMatrix2, Nat.stirlingSecond_self]

/-- `s(n) S(n) = I_n`: the orthogonality relation
`sum_signedStirlingFirst_mul_stirlingSecond` for `1 ≤ i, j ≤ n`. -/
theorem stirlingFirstMatrix_mul_stirlingMatrix2 (n : ℕ) :
    stirlingFirstMatrix n * stirlingMatrix2 n = 1 := by
  ext a b
  have h := congrArg (Int.cast : ℤ → ℚ)
    (sum_signedStirlingFirst_mul_stirlingSecond (a.val + 1) (b.val + 1))
  rw [sum_range_succ', signedStirlingFirst_succ_zero, zero_mul, add_zero]
    at h
  push_cast at h
  rw [mul_apply, one_apply]
  simp only [stirlingFirstMatrix, stirlingMatrix2, of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (signedStirlingFirst (a.val + 1)
      (k + 1) : ℚ) * (Nat.stirlingSecond (k + 1) (b.val + 1) : ℚ)) n,
    ← sum_subset (range_subset_range.2 (by omega : a.val + 1 ≤ n)), h]
  · simp only [Fin.ext_iff]
  · intro k _ hk
    rw [mem_range, not_lt] at hk
    rw [signedStirlingFirst_eq_zero_of_lt (by omega), Int.cast_zero, zero_mul]

/-- `S(n) s(n) = I_n`. -/
theorem stirlingMatrix2_mul_stirlingFirstMatrix (n : ℕ) :
    stirlingMatrix2 n * stirlingFirstMatrix n = 1 :=
  mul_eq_one_comm.mp (stirlingFirstMatrix_mul_stirlingMatrix2 n)

/-! ### The shifted matrices `S^[m](n)` -/

/-- `S^[m+1](n) = S^[m](n) V(n)`; entrywise this is the recurrence
`Nat.stirlingSecond_succ_succ`. -/
private theorem stirlingSecondShiftMatrix_succ_eq_mul (m n : ℕ) :
    stirlingSecondShiftMatrix (m + 1) n =
      stirlingSecondShiftMatrix m n * stirlingVMatrix n := by
  ext a c
  rw [mul_stirlingVMatrix_apply]
  simp only [stirlingSecondShiftMatrix, of_apply]
  rw [show a.val + 1 + (m + 1) = a.val + 1 + m + 1 by omega,
    Nat.stirlingSecond_succ_succ]
  push_cast
  split_ifs with h
  · rw [h, show a.val + 1 + m = a.val + m + 1 by omega,
      Nat.stirlingSecond_succ_zero]
    push_cast
    ring
  · rw [Nat.sub_add_cancel (by omega)]
    ring

/-- Theorem 2: `S^[m](n) = S(n) V(n)^m`, and
`det S^[m](n) = det_{1 ≤ i, j ≤ n} [S(i + m, j)] = ∏_{i=1}^{n} i^m = n!^m`.
The paper takes `m, n ≥ 1`; `m = 0` and `n = 0` also hold and are included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 2, Equation (18)
(`integers-2025-A27-thm-2`).

Proves `Wanted` entry `stirlingSecondShiftMatrix_eq_mul_pow`. -/
theorem stirlingSecondShiftMatrix_eq_mul_pow (m n : ℕ) :
    stirlingSecondShiftMatrix m n =
        stirlingMatrix2 n * stirlingVMatrix n ^ m ∧
      (stirlingSecondShiftMatrix m n).det = (n.factorial : ℚ) ^ m := by
  have h : stirlingSecondShiftMatrix m n =
      stirlingMatrix2 n * stirlingVMatrix n ^ m := by
    induction m with
    | zero => rw [stirlingSecondShiftMatrix_zero, pow_zero, mul_one]
    | succ m ih =>
      rw [stirlingSecondShiftMatrix_succ_eq_mul, ih, pow_succ, mul_assoc]
  refine ⟨h, ?_⟩
  rw [h, det_mul, det_pow, det_stirlingMatrix2, det_stirlingVMatrix, one_mul]

/-- Corollary 2: `S^[m+1](n) = S^[m](n) V(n)`, hence
`det S^[m+1](n) = n! det S^[m](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 2 (`integers-2025-A27-cor-2`).

Proves `Wanted` entry `stirlingSecondShiftMatrix_succ`. -/
theorem stirlingSecondShiftMatrix_succ (m n : ℕ) :
    stirlingSecondShiftMatrix (m + 1) n =
        stirlingSecondShiftMatrix m n * stirlingVMatrix n ∧
      (stirlingSecondShiftMatrix (m + 1) n).det =
        (n.factorial : ℚ) * (stirlingSecondShiftMatrix m n).det := by
  refine ⟨stirlingSecondShiftMatrix_succ_eq_mul m n, ?_⟩
  rw [stirlingSecondShiftMatrix_succ_eq_mul, det_mul, det_stirlingVMatrix,
    mul_comm]

/-- `s(n) S^[m](n) = V(n)^m`. -/
theorem stirlingFirstMatrix_mul_stirlingSecondShiftMatrix (m n : ℕ) :
    stirlingFirstMatrix n * stirlingSecondShiftMatrix m n =
      stirlingVMatrix n ^ m := by
  rw [(stirlingSecondShiftMatrix_eq_mul_pow m n).1, ← mul_assoc,
    stirlingFirstMatrix_mul_stirlingMatrix2, one_mul]

/-- Corollary 3: `S^[m₁+m₂](n) = S^[m₁](n) s(n) S^[m₂](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 3 (`integers-2025-A27-cor-3`).

Proves `Wanted` entry `stirlingSecondShiftMatrix_add`. -/
theorem stirlingSecondShiftMatrix_add (m₁ m₂ n : ℕ) :
    stirlingSecondShiftMatrix (m₁ + m₂) n =
      stirlingSecondShiftMatrix m₁ n * stirlingFirstMatrix n *
        stirlingSecondShiftMatrix m₂ n := by
  rw [mul_assoc, stirlingFirstMatrix_mul_stirlingSecondShiftMatrix,
    (stirlingSecondShiftMatrix_eq_mul_pow _ n).1,
    (stirlingSecondShiftMatrix_eq_mul_pow _ n).1, pow_add, mul_assoc]

/-- `S^[m](n) Ṽ(n)^m s(n) = I_n`. -/
theorem stirlingSecondShiftMatrix_mul_stirlingVTildeMatrix_pow_mul
    (m n : ℕ) :
    stirlingSecondShiftMatrix m n *
      (stirlingVTildeMatrix n ^ m * stirlingFirstMatrix n) = 1 := by
  have hV := stirlingVMatrix_mul_stirlingVTildeMatrix n
  have hc : Commute (stirlingVMatrix n) (stirlingVTildeMatrix n) :=
    hV.trans (mul_eq_one_comm.mp hV).symm
  rw [(stirlingSecondShiftMatrix_eq_mul_pow m n).1, mul_assoc,
    ← mul_assoc (_ ^ m), ← hc.mul_pow, hV, one_pow, one_mul,
    stirlingMatrix2_mul_stirlingFirstMatrix]

/-- Theorem 3: `S^[m](n)⁻¹ = Ṽ(n)^m s(n)`. The paper takes `m ≥ 1`; the case
`m = 0` (`S(n)⁻¹ = s(n)`) also holds and is included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 3 (`integers-2025-A27-thm-3`).

Proves `Wanted` entry `stirlingSecondShiftMatrix_inv`. -/
theorem stirlingSecondShiftMatrix_inv (m n : ℕ) :
    (stirlingSecondShiftMatrix m n)⁻¹ =
      stirlingVTildeMatrix n ^ m * stirlingFirstMatrix n :=
  inv_eq_right_inv
    (stirlingSecondShiftMatrix_mul_stirlingVTildeMatrix_pow_mul m n)

/-- `S^[1](n) Ṽ(n) = S(n)`. -/
theorem stirlingSecondShiftMatrix_one_mul_stirlingVTildeMatrix (n : ℕ) :
    stirlingSecondShiftMatrix 1 n * stirlingVTildeMatrix n =
      stirlingMatrix2 n := by
  rw [(stirlingSecondShiftMatrix_succ 0 n).1, stirlingSecondShiftMatrix_zero,
    mul_assoc, stirlingVMatrix_mul_stirlingVTildeMatrix, mul_one]

/-! ### The matrices `Q^[N](n)` and `E(n)` -/

/-- Column `c` of `M (V(n) - I_n)` is `c` times column `c` of `M`, plus
column `c - 1` of `M` when `c ≥ 1` (`0`-based indices). -/
theorem mul_stirlingVMatrix_sub_one_apply {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n) :
    (M * (stirlingVMatrix n - 1)) a c =
      M a c * c.val +
        if h : c.val = 0 then 0 else M a ⟨c.val - 1, by omega⟩ := by
  rw [mul_sub, mul_one, Matrix.sub_apply, mul_stirlingVMatrix_apply]
  ring

/-- Lemma 2: `Q^[N+1](n) = Q^[N](n) (V(n) - I_n)` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 2 (`integers-2025-A27-lem-2`).

Proves `Wanted` entry `stirlingQMatrix_succ`. -/
theorem stirlingQMatrix_succ {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix (N + 1) n =
      stirlingQMatrix N n * (stirlingVMatrix n - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  ext a c
  rw [mul_stirlingVMatrix_sub_one_apply]
  simp only [stirlingQMatrix, of_apply, Nat.add_sub_cancel]
  split_ifs with h1 h2 h3 h3
  · omega
  · obtain ⟨d, hd⟩ : ∃ d, c.val = a.val + 2 + d :=
      ⟨c.val - (a.val + 2), by omega⟩
    rw [show c.val - a.val + 1 = d + 3 by omega,
      show c.val - a.val - 1 = d + 1 by omega,
      show c.val - 1 - a.val + 1 = d + 2 by omega,
      show c.val - 1 - a.val - 1 = d by omega, hd, Nat.factorial_succ d]
    push_cast
    field_simp
    ring
  · rw [show c.val = a.val + 1 by omega, Nat.add_sub_cancel_left,
      Nat.sub_self]
    push_cast
    ring
  · ring
  · omega
  · ring

/-- Corollary 1: `Q^[N](n) = Q^[1](n) (V(n) - I_n)^{N-1}` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 1 (`integers-2025-A27-cor-1`).

Proves `Wanted` entry `stirlingQMatrix_eq_one_mul_pow`. -/
theorem stirlingQMatrix_eq_one_mul_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix N n =
      stirlingQMatrix 1 n * (stirlingVMatrix n - 1) ^ (N - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  clear hN
  rw [Nat.add_sub_cancel]
  induction N with
  | zero => rw [pow_zero, mul_one]
  | succ N ih =>
    rw [stirlingQMatrix_succ (by omega), ih, pow_succ, mul_assoc]

/-! ### Binomial sums of shifted Stirling numbers -/

/-- The explicit formula `S(t, k) = ∑_{l=0}^{k} (-1)^{k-l} C(k, l) l^t / k!`
over `ℚ`, transferred from `stirlingSecond_mul_factorial_eq_sum` over `ℝ`. -/
private theorem stirlingSecond_eq_sum_rat (t k : ℕ) :
    (Nat.stirlingSecond t k : ℚ) =
      ∑ l ∈ range (k + 1),
        (-1 : ℚ) ^ (k - l) * (k.choose l : ℚ) * (l : ℚ) ^ t / k ! := by
  rw [← sum_div, eq_div_iff (by positivity)]
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact stirlingSecond_mul_factorial_eq_sum t k

/-- The left side of Theorem 5 in closed form:
`∑_{l=0}^{N} (-1)^{N-l} C(N, l) S(i + l, j) =
∑_{k=0}^{j} (-1)^{j-k} C(j, k) k^i (k - 1)^N / j!`. -/
theorem sum_choose_stirlingSecond_eq_sum_pow (i j N : ℕ) :
    ∑ l ∈ range (N + 1),
        (-1 : ℚ) ^ (N - l) * (N.choose l : ℚ) *
          (Nat.stirlingSecond (i + l) j : ℚ) =
      ∑ k ∈ range (j + 1),
        (-1 : ℚ) ^ (j - k) * (j.choose k : ℚ) * (k : ℚ) ^ i *
          ((k : ℚ) - 1) ^ N / j ! := by
  simp only [stirlingSecond_eq_sum_rat, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sub_eq_add_neg, add_pow, mul_sum, sum_div]
  refine sum_congr rfl fun l _ => ?_
  ring

/-- Theorem 5: for `i, j, N ≥ 1`,
`∑_{l=0}^{N} (-1)^{N-l} C(N, l) S(i + l, j) =
∑_{k=1}^{j-1} (-1)^{j-k+1} k^{N-1} (k + 1)^{i-1} / ((k - 1)! (j - k - 1)!)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 5 (`integers-2025-A27-thm-5`).

Proves `Wanted` entry `sum_choose_stirlingSecond_eq`. -/
theorem sum_choose_stirlingSecond_eq {i j N : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hN : 1 ≤ N) :
    ∑ l ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (N - l) * (N.choose l : ℚ) *
          (Nat.stirlingSecond (i + l) j : ℚ) =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * (k : ℚ) ^ (N - 1) *
          ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
            (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ)) := by
  rw [sum_choose_stirlingSecond_eq_sum_pow]
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ', sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.add_sub_cancel]
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, sub_self,
    ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero, zero_mul, zero_div, add_zero]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨e, rfl⟩ : ∃ e, j = k + 1 + e :=
    ⟨j - (k + 1), by rw [mem_range] at hk; omega⟩
  rw [Nat.cast_choose ℚ (by omega),
    show k + 1 + e + 1 - (k + 1 + 1) = e by omega,
    show k + 1 + e + 1 - (1 + k) + 1 = e + 2 by omega,
    show k + 1 + e + 1 - (1 + k) - 1 = e by omega,
    show 1 + k - 1 = k by omega, Nat.factorial_succ (k + 1),
    Nat.factorial_succ k]
  push_cast
  field_simp
  ring

/-- Corollary 4: for `i, j ≥ 1`,
`S(i + 1, j) - S(i, j) =
∑_{k=1}^{j-1} (-1)^{j-k+1} (k + 1)^{i-1} / ((k - 1)! (j - k - 1)!)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 4 (`integers-2025-A27-cor-4`).

Proves `Wanted` entry `stirlingSecond_succ_sub_eq_sum`. -/
theorem stirlingSecond_succ_sub_eq_sum {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (Nat.stirlingSecond (i + 1) j : ℚ) - Nat.stirlingSecond i j =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
          (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ)) := by
  have h := sum_choose_stirlingSecond_eq hi hj le_rfl
  rw [sum_range_succ, sum_range_one] at h
  simp only [Nat.sub_zero, Nat.sub_self, pow_one, pow_zero,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one,
    add_zero] at h
  linear_combination h

/-- Lemma 3: `S(n) (V(n) - I_n) = E(n) Q^[1](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 3, Equation (7)
(`integers-2025-A27-lem-3`).

Proves `Wanted` entry `stirlingMatrix2_mul_sub_one`. -/
theorem stirlingMatrix2_mul_sub_one (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) =
      shiftedVandermondeMatrix n * stirlingQMatrix 1 n := by
  ext a c
  rw [mul_stirlingVMatrix_sub_one_apply, mul_apply]
  trans (Nat.stirlingSecond (a.val + 1 + 1) (c.val + 1) : ℚ) -
    Nat.stirlingSecond (a.val + 1) (c.val + 1)
  · simp only [stirlingMatrix2, of_apply]
    rw [Nat.stirlingSecond_succ_succ (a.val + 1) c.val]
    push_cast
    split_ifs with h
    · rw [h, Nat.stirlingSecond_succ_zero]
      push_cast
      ring
    · rw [Nat.sub_add_cancel (by omega)]
      ring
  rw [stirlingSecond_succ_sub_eq_sum (by omega) (by omega),
    sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    sum_range_eq_sum_fin_ite c.is_lt.le]
  refine sum_congr rfl fun b _ => ?_
  simp only [shiftedVandermondeMatrix, stirlingQMatrix, of_apply]
  split_ifs with h1 h2 h2
  · rw [show c.val + 1 - (1 + b.val) + 1 = c.val - b.val + 1 by omega,
      show c.val + 1 - (1 + b.val) - 1 = c.val - b.val - 1 by omega,
      show 1 + b.val - 1 = b.val by omega, Nat.add_sub_cancel, Nat.sub_self,
      pow_zero, add_comm 1 b.val]
    ring
  · omega
  · omega
  · rw [mul_zero]

/-- Theorem 1: `S(n) (V(n) - I_n)^N = E(n) Q^[N](n)` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 1 (`integers-2025-A27-thm-1`).

Proves `Wanted` entry `stirlingMatrix2_mul_sub_one_pow`. -/
theorem stirlingMatrix2_mul_sub_one_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) ^ N =
      shiftedVandermondeMatrix n * stirlingQMatrix N n := by
  rw [stirlingQMatrix_eq_one_mul_pow hN, ← mul_assoc,
    ← stirlingMatrix2_mul_sub_one, mul_assoc, ← pow_succ',
    Nat.sub_add_cancel hN]

/-! ### Entrywise identities -/

/-- Theorem 4: for `i ≥ j ≥ 1`, `∑_{l=1}^{i} s(i, l) S(l + m, j)` is `i^m` if
`i = j` and `0` if `i > j`. The paper takes `m ≥ 1`; `m = 0` also holds and is
included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 4 (`integers-2025-A27-thm-4`).

Proves `Wanted` entry `sum_signedStirlingFirst_mul_stirlingSecond_add`. -/
theorem sum_signedStirlingFirst_mul_stirlingSecond_add {i j : ℕ} (hj : 1 ≤ j)
    (hji : j ≤ i) (m : ℕ) :
    ∑ l ∈ Finset.Icc 1 i,
        signedStirlingFirst i l * (Nat.stirlingSecond (l + m) j : ℤ) =
      if i = j then (i : ℤ) ^ m else 0 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have h := congrFun (congrFun
    (stirlingFirstMatrix_mul_stirlingSecondShiftMatrix m (i + 1))
    ⟨i, by omega⟩) ⟨j, by omega⟩
  rw [stirlingVMatrix_pow_apply_of_le m (Fin.le_def.2 (show j ≤ i by omega)),
    mul_apply] at h
  simp only [stirlingFirstMatrix, stirlingSecondShiftMatrix, of_apply,
    Fin.mk.injEq] at h
  rw [sum_fin_eq_sum_Icc (fun k => (signedStirlingFirst (i + 1) k : ℚ) *
    (Nat.stirlingSecond (k + m) (j + 1) : ℚ)) (i + 1)] at h
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h]

/-- Theorem 6: for `n ≥ max {i, j}`,
`∑_{k₁=1}^{n} ∑_{k₂=k₁}^{n} (-1)^{k₂-k₁} (k₁ - 1)! / k₂! · S(i + 1, k₁) s(k₂, j)
= δ_{i,j}`.
The hypothesis `i ≥ 1` (the paper's indices are positive) is needed: for
`i = j = 0` the left side is `0`; `j ≥ 1` is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 6 (`integers-2025-A27-thm-6`).

Proves `Wanted` entry `sum_sum_stirlingSecond_signedStirlingFirst_eq_ite`. -/
theorem sum_sum_stirlingSecond_signedStirlingFirst_eq_ite {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc k₁ n,
        (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k₁ : ℚ) * (signedStirlingFirst k₂ j : ℚ) =
      if i = j then 1 else 0 := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases j with _ | j
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun k₁ hk₁ => sum_eq_zero fun k₂ hk₂ => ?_
    rw [mem_Icc] at hk₁ hk₂
    obtain ⟨k, rfl⟩ : ∃ k, k₂ = k + 1 := ⟨k₂ - 1, by omega⟩
    rw [signedStirlingFirst_succ_zero, Int.cast_zero, mul_zero]
  have h := congrFun (congrFun
    (stirlingSecondShiftMatrix_mul_stirlingVTildeMatrix_pow_mul 1 n)
    ⟨i, by omega⟩) ⟨j, by omega⟩
  rw [one_apply, pow_one] at h
  simp only [Fin.mk.injEq] at h
  simp only [Nat.add_right_cancel_iff]
  rw [← h, mul_apply, ← sum_fin_eq_sum_Icc]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_Icc_eq_sum_Icc_one_ite (by omega), ← sum_fin_eq_sum_Icc, mul_apply,
    mul_sum]
  refine sum_congr rfl fun d _ => ?_
  simp only [stirlingSecondShiftMatrix, stirlingVTildeMatrix,
    stirlingFirstMatrix, of_apply, Fin.le_def, Nat.add_le_add_iff_right]
  split_ifs with hcd
  · rw [Nat.add_sub_add_right, Nat.add_sub_cancel]
    ring
  · ring

/-- Theorem 7: for `i ≥ 1`,
`∑_{k=1}^{min {i+1, j}} (-1)^{j-k} (k - 1)! / j! · S(i + 1, k)` is `S(i, j)` if
`i ≥ j` and `0` otherwise. The paper also assumes `j ≥ 1`; the case `j = 0`
holds (both sides vanish) and is included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 7 (`integers-2025-A27-thm-7`).

Proves `Wanted` entry `sum_stirlingSecond_succ_eq_ite`. -/
theorem sum_stirlingSecond_succ_eq_ite {i j : ℕ} (hi : 1 ≤ i) :
    ∑ k ∈ Finset.Icc 1 (min (i + 1) j),
        (-1 : ℚ) ^ (j - k) * ((k - 1).factorial : ℚ) / (j.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k : ℚ) =
      if j ≤ i then (Nat.stirlingSecond i j : ℚ) else 0 := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases j with _ | j
  · simp
  have hR : (if j + 1 ≤ i + 1 then (Nat.stirlingSecond (i + 1) (j + 1) : ℚ)
      else 0) = Nat.stirlingSecond (i + 1) (j + 1) := by
    split_ifs with hji
    · rfl
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero]
  rw [hR]
  set n := max (i + 1) (j + 1) with hn
  have h := congrFun (congrFun
    (stirlingSecondShiftMatrix_one_mul_stirlingVTildeMatrix n)
    ⟨i, by omega⟩) ⟨j, by omega⟩
  simp only [mul_apply, stirlingMatrix2, of_apply] at h
  let g : ℕ → ℚ := fun k =>
    (if k ≤ j + 1 then (-1 : ℚ) ^ (j + 1 - k) * ((k - 1).factorial : ℚ) /
      ((j + 1).factorial : ℚ) else 0) * (Nat.stirlingSecond (i + 1 + 1) k : ℚ)
  calc _ = ∑ k ∈ Icc 1 (min (i + 1 + 1) (j + 1)), g k := by
        refine sum_congr rfl fun k hk => ?_
        rw [mem_Icc] at hk
        simp only [g]
        rw [ite_eq_left (by omega)]
    _ = ∑ k ∈ Icc 1 n, g k := by
        refine sum_subset (Icc_subset_Icc_right (by omega)) fun k hk hk' => ?_
        simp only [mem_Icc] at hk hk'
        simp only [g]
        by_cases hkj : k ≤ j + 1
        · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero,
            mul_zero]
        · rw [ite_eq_right hkj, zero_mul]
    _ = ∑ c : Fin n, g (c.val + 1) := (sum_fin_eq_sum_Icc g n).symm
    _ = _ := by
      rw [← h]
      refine sum_congr rfl fun c _ => ?_
      simp only [g, stirlingSecondShiftMatrix, stirlingVTildeMatrix, of_apply,
        Fin.le_def, Nat.add_le_add_iff_right]
      split_ifs with hc
      · rw [Nat.add_sub_add_right, Nat.add_sub_cancel]
        ring
      · ring

/-- Theorem 8: for `n ≥ max {i, j}` and `m₁, m₂ ≥ 0`,
`∑_{k₁=1}^{n} ∑_{k₂=1}^{k₁} S(i + m₁, k₁) s(k₁, k₂) S(k₂ + m₂, j) =
S(i + m₁ + m₂, j)`.
The shifts `m₁, m₂` are those of Corollary 3 (the statement leaves them
unquantified); `i ≥ 1` is kept, `j ≥ 1` is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 8 (`integers-2025-A27-thm-8`).

Proves `Wanted` entry
`sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond`. -/
theorem sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) (m₁ m₂ : ℕ) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc 1 k₁,
        (Nat.stirlingSecond (i + m₁) k₁ : ℤ) * signedStirlingFirst k₁ k₂ *
          (Nat.stirlingSecond (k₂ + m₂) j : ℤ) =
      Nat.stirlingSecond (i + m₁ + m₂) j := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases j with _ | j
  · rw [show i + 1 + m₁ + m₂ = i + m₁ + m₂ + 1 by omega,
      Nat.stirlingSecond_succ_zero, Nat.cast_zero]
    refine sum_eq_zero fun k₁ _ => sum_eq_zero fun k₂ hk₂ => ?_
    rw [mem_Icc] at hk₂
    rw [show k₂ + m₂ = k₂ - 1 + m₂ + 1 by omega, Nat.stirlingSecond_succ_zero,
      Nat.cast_zero, mul_zero]
  have h := congrFun (congrFun (stirlingSecondShiftMatrix_add m₁ m₂ n)
    ⟨i, by omega⟩) ⟨j, by omega⟩
  rw [mul_assoc, mul_apply] at h
  simp only [stirlingSecondShiftMatrix, of_apply] at h
  have key : ∑ k₁ ∈ Icc 1 n, ∑ k₂ ∈ Icc 1 k₁,
      (Nat.stirlingSecond (i + 1 + m₁) k₁ : ℚ) *
        (signedStirlingFirst k₁ k₂ : ℚ) *
          (Nat.stirlingSecond (k₂ + m₂) (j + 1) : ℚ) =
      Nat.stirlingSecond (i + 1 + m₁ + m₂) (j + 1) := by
    rw [add_assoc (i + 1) m₁ m₂, h, ← sum_fin_eq_sum_Icc]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_subset (Icc_subset_Icc_right (show c.val + 1 ≤ n by omega)),
      ← sum_fin_eq_sum_Icc, mul_apply, mul_sum]
    · refine sum_congr rfl fun d _ => ?_
      simp only [stirlingFirstMatrix, of_apply]
      ring
    · intro k hk hk'
      rw [mem_Icc] at hk hk'
      rw [signedStirlingFirst_eq_zero_of_lt (by omega), Int.cast_zero,
        mul_zero, zero_mul]
  exact_mod_cast key

end

end MetaMathlibExt
