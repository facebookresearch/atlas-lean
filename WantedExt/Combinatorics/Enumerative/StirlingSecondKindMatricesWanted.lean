/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import WantedExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-!
# Matrices whose entries are Stirling numbers of the second kind

Statements from M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima
Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27.

Conventions. `S(n, k)` is `Nat.stirlingSecond` and the signed Stirling number of
the first kind `s(n, k)` is MathlibExt's `signedStirlingFirst`. The `n × n`
matrices are `Matrix (Fin n) (Fin n) ℚ`, entry `(a, b)` being the paper's
`(a + 1, b + 1)` entry. The Stirling matrix of the second kind `S(n)` is the
existing `stirlingMatrix2`. The paper takes `n` positive; for `n = 0` every
matrix identity below is trivial, so no hypothesis on `n` is added.
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- The shifted Stirling matrix `S^[m](n)` with entries `S(i + m, j)`,
`1 ≤ i, j ≤ n`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
public def stirlingSecondShiftMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (Nat.stirlingSecond (a.val + 1 + m) (b.val + 1) : ℚ)

/-- `S^[0](n) = S(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
public theorem stirlingSecondShiftMatrix_zero (n : ℕ) :
    stirlingSecondShiftMatrix 0 n = stirlingMatrix2 n := by
  ext a b
  simp [stirlingSecondShiftMatrix, stirlingMatrix2]

/-- The first column of `S^[m](n)` is all ones: `S(i + m, 1) = 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1, Equation (5). -/
public theorem stirlingSecondShiftMatrix_apply_zero_right {m n : ℕ} (a : Fin n)
    (h : 0 < n) : stirlingSecondShiftMatrix m n a ⟨0, h⟩ = 1 := by
  simp only [stirlingSecondShiftMatrix, Matrix.of_apply]
  rw [show a.val + 1 + m = (a.val + m) + 1 by omega, Nat.stirlingSecond_one_right]
  simp

/-- The Stirling matrix of the first kind `s(n)` with entries `s(i, j)`
(zero above the diagonal).

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `s(n)`). -/
public def stirlingFirstMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (signedStirlingFirst (a.val + 1) (b.val + 1) : ℚ)

/-- The diagonal of `s(n)` is all ones.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (`s(n, n) = 1`). -/
public theorem stirlingFirstMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingFirstMatrix n a a = 1 := by
  simp [stirlingFirstMatrix, signedStirlingFirst, Nat.stirlingFirst_self]

/-- The upper bidiagonal matrix `V(n)`: `V_{i,i} = i`, `V_{i,i+1} = 1`, zero
elsewhere.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
public def stirlingVMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if b = a then (a.val + 1 : ℚ) else if b.val = a.val + 1 then 1 else 0

/-- `V(n)_{i,i} = i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
public theorem stirlingVMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVMatrix n a a = a.val + 1 := by
  simp [stirlingVMatrix]

/-- The upper triangular matrix `Ṽ(n)` with `Ṽ_{i,j} = (-1)^{j-i} (i-1)! / j!`
for `j ≥ i`, zero otherwise.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
public def stirlingVTildeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a ≤ b then
      (-1 : ℚ) ^ (b.val - a.val) * (a.val.factorial : ℚ) / ((b.val + 1).factorial : ℚ)
    else 0

/-- `Ṽ(n)_{i,i} = 1 / i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
public theorem stirlingVTildeMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVTildeMatrix n a a = 1 / (a.val + 1 : ℚ) := by
  simp only [stirlingVTildeMatrix, Matrix.of_apply, le_refl, ite_true, Nat.sub_self,
    pow_zero, one_mul, Nat.factorial_succ, Nat.cast_mul]
  have h : (a.val.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  push_cast
  ring

/-- The matrix `E(n)` with `E_{i,j} = (j + 1)^{i-1}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
public def shiftedVandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 2 : ℕ) : ℚ) ^ a.val

/-- The first row of `E(n)` is all ones.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
public theorem shiftedVandermondeMatrix_apply_zero_left {n : ℕ} (h : 0 < n) (b : Fin n) :
    shiftedVandermondeMatrix n ⟨0, h⟩ b = 1 := by
  simp [shiftedVandermondeMatrix]

/-- The strictly upper triangular matrix `Q^[N](n)` with
`Q^[N]_{i,j} = (-1)^{j-i+1} i^{N-1} / ((i-1)! (j-i-1)!)` for `j ≥ i + 1`, zero
otherwise.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
public def stirlingQMatrix (N n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a.val + 1 ≤ b.val then
      (-1 : ℚ) ^ (b.val - a.val + 1) * ((a.val + 1 : ℕ) : ℚ) ^ (N - 1) /
        ((a.val.factorial : ℚ) * ((b.val - a.val - 1).factorial : ℚ))
    else 0

/-- `Q^[N](n)` vanishes on and below the diagonal.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
public theorem stirlingQMatrix_apply_of_le {N n : ℕ} {a b : Fin n} (h : b ≤ a) :
    stirlingQMatrix N n a b = 0 := by
  have : ¬ a.val + 1 ≤ b.val := by
    have := Fin.le_iff_val_le_val.1 h
    omega
  simp only [stirlingQMatrix, Matrix.of_apply, this, ↓reduceIte]

/-- Lemma 1: `V(n)⁻¹ = Ṽ(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 1 (`integers-2025-A27-lem-1`). -/
public theorem_wanted stirlingVMatrix_inv (n : ℕ) :
    (stirlingVMatrix n)⁻¹ = stirlingVTildeMatrix n

/-- Lemma 2: `Q^[N+1](n) = Q^[N](n) (V(n) - I_n)` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 2 (`integers-2025-A27-lem-2`). -/
public theorem_wanted stirlingQMatrix_succ {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix (N + 1) n = stirlingQMatrix N n * (stirlingVMatrix n - 1)

/-- Corollary 1: `Q^[N](n) = Q^[1](n) (V(n) - I_n)^{N-1}` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 1 (`integers-2025-A27-cor-1`). -/
public theorem_wanted stirlingQMatrix_eq_one_mul_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix N n = stirlingQMatrix 1 n * (stirlingVMatrix n - 1) ^ (N - 1)

/-- Lemma 3: `S(n) (V(n) - I_n) = E(n) Q^[1](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 3, Equation (7) (`integers-2025-A27-lem-3`). -/
public theorem_wanted stirlingMatrix2_mul_sub_one (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) =
      shiftedVandermondeMatrix n * stirlingQMatrix 1 n

/-- Theorem 1: `S(n) (V(n) - I_n)^N = E(n) Q^[N](n)` for `N ≥ 1`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 1 (`integers-2025-A27-thm-1`). -/
public theorem_wanted stirlingMatrix2_mul_sub_one_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) ^ N =
      shiftedVandermondeMatrix n * stirlingQMatrix N n

/-- Theorem 2: `S^[m](n) = S(n) V(n)^m`, and
`det S^[m](n) = det_{1 ≤ i, j ≤ n} [S(i + m, j)] = ∏_{i=1}^{n} i^m = n!^m`. The paper takes
`m, n ≥ 1`; `m = 0` and `n = 0` also hold and are included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 2, Equation (18) (`integers-2025-A27-thm-2`). -/
public theorem_wanted stirlingSecondShiftMatrix_eq_mul_pow (m n : ℕ) :
    stirlingSecondShiftMatrix m n = stirlingMatrix2 n * stirlingVMatrix n ^ m ∧
      (stirlingSecondShiftMatrix m n).det = (n.factorial : ℚ) ^ m

/-- Corollary 2: `S^[m+1](n) = S^[m](n) V(n)`, hence
`det S^[m+1](n) = n! det S^[m](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 2 (`integers-2025-A27-cor-2`). -/
public theorem_wanted stirlingSecondShiftMatrix_succ (m n : ℕ) :
    stirlingSecondShiftMatrix (m + 1) n = stirlingSecondShiftMatrix m n * stirlingVMatrix n ∧
      (stirlingSecondShiftMatrix (m + 1) n).det =
        (n.factorial : ℚ) * (stirlingSecondShiftMatrix m n).det

/-- Corollary 3: `S^[m₁+m₂](n) = S^[m₁](n) s(n) S^[m₂](n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 3 (`integers-2025-A27-cor-3`). -/
public theorem_wanted stirlingSecondShiftMatrix_add (m₁ m₂ n : ℕ) :
    stirlingSecondShiftMatrix (m₁ + m₂) n =
      stirlingSecondShiftMatrix m₁ n * stirlingFirstMatrix n * stirlingSecondShiftMatrix m₂ n

/-- Theorem 3: `S^[m](n)⁻¹ = Ṽ(n)^m s(n)`. The paper takes `m ≥ 1`; the case
`m = 0` (`S(n)⁻¹ = s(n)`) also holds and is included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 3 (`integers-2025-A27-thm-3`). -/
public theorem_wanted stirlingSecondShiftMatrix_inv (m n : ℕ) :
    (stirlingSecondShiftMatrix m n)⁻¹ = stirlingVTildeMatrix n ^ m * stirlingFirstMatrix n

/-- Theorem 4: for `i ≥ j ≥ 1`, `∑_{l=1}^{i} s(i, l) S(l + m, j)` is `i^m` if
`i = j` and `0` if `i > j`. The paper takes `m ≥ 1`; `m = 0` also holds and is
included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 4 (`integers-2025-A27-thm-4`). -/
public theorem_wanted sum_signedStirlingFirst_mul_stirlingSecond_add {i j : ℕ} (hj : 1 ≤ j)
    (hji : j ≤ i) (m : ℕ) :
    ∑ l ∈ Finset.Icc 1 i, signedStirlingFirst i l * (Nat.stirlingSecond (l + m) j : ℤ) =
      if i = j then (i : ℤ) ^ m else 0

/-- Theorem 5: for `i, j, N ≥ 1`,
`∑_{l=0}^{N} (-1)^{N-l} C(N, l) S(i + l, j) =
∑_{k=1}^{j-1} (-1)^{j-k+1} k^{N-1} (k + 1)^{i-1} / ((k - 1)! (j - k - 1)!)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 5 (`integers-2025-A27-thm-5`). -/
public theorem_wanted sum_choose_stirlingSecond_eq {i j N : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hN : 1 ≤ N) :
    ∑ l ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (N - l) * (N.choose l : ℚ) * (Nat.stirlingSecond (i + l) j : ℚ) =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * (k : ℚ) ^ (N - 1) * ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
          (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ))

/-- Corollary 4: for `i, j ≥ 1`,
`S(i + 1, j) - S(i, j) = ∑_{k=1}^{j-1} (-1)^{j-k+1} (k + 1)^{i-1} / ((k - 1)! (j - k - 1)!)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 4 (`integers-2025-A27-cor-4`). -/
public theorem_wanted stirlingSecond_succ_sub_eq_sum {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (Nat.stirlingSecond (i + 1) j : ℚ) - Nat.stirlingSecond i j =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
          (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ))

/-- Theorem 6: for `n ≥ max {i, j}`,
`∑_{k₁=1}^{n} ∑_{k₂=k₁}^{n} (-1)^{k₂-k₁} (k₁ - 1)! / k₂! · S(i + 1, k₁) s(k₂, j) = δ_{i,j}`.
The hypothesis `i ≥ 1` (the paper's indices are positive) is needed: for
`i = j = 0` the left side is `0`; `j ≥ 1` is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 6 (`integers-2025-A27-thm-6`). -/
public theorem_wanted sum_sum_stirlingSecond_signedStirlingFirst_eq_ite {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc k₁ n,
        (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k₁ : ℚ) * (signedStirlingFirst k₂ j : ℚ) =
      if i = j then 1 else 0

/-- Theorem 7: for `i ≥ 1`,
`∑_{k=1}^{min {i+1, j}} (-1)^{j-k} (k - 1)! / j! · S(i + 1, k)` is `S(i, j)` if
`i ≥ j` and `0` otherwise. The paper also assumes `j ≥ 1`; the case `j = 0`
holds (both sides vanish) and is included.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 7 (`integers-2025-A27-thm-7`). -/
public theorem_wanted sum_stirlingSecond_succ_eq_ite {i j : ℕ} (hi : 1 ≤ i) :
    ∑ k ∈ Finset.Icc 1 (min (i + 1) j),
        (-1 : ℚ) ^ (j - k) * ((k - 1).factorial : ℚ) / (j.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k : ℚ) =
      if j ≤ i then (Nat.stirlingSecond i j : ℚ) else 0

/-- Theorem 8: for `n ≥ max {i, j}` and `m₁, m₂ ≥ 0`,
`∑_{k₁=1}^{n} ∑_{k₂=1}^{k₁} S(i + m₁, k₁) s(k₁, k₂) S(k₂ + m₂, j) = S(i + m₁ + m₂, j)`.
The shifts `m₁, m₂` are those of Corollary 3 (the statement leaves them
unquantified); `i ≥ 1` is kept, `j ≥ 1` is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 8 (`integers-2025-A27-thm-8`). -/
public theorem_wanted sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) (m₁ m₂ : ℕ) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc 1 k₁,
        (Nat.stirlingSecond (i + m₁) k₁ : ℤ) * signedStirlingFirst k₁ k₂ *
          (Nat.stirlingSecond (k₂ + m₂) j : ℤ) =
      Nat.stirlingSecond (i + m₁ + m₂) j

end

end MetaMathlibExt
