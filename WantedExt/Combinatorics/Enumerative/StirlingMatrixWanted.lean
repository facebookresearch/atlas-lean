/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Some identities involving Stirling numbers arising from matrix decompositions

Statements from M. Bahrami-Taghanaki, A. R. Moghaddamfar,
Nima Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
*Journal of Integer Sequences* 27 (2024), Article 24.5.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Moghaddamfar/mogh14.tex>).

For a sequence `α : ℕ → ℚ`, the paper's Stirling-like
matrix `S_α` is given entrywise (in the paper's 1-based
indexing) by `stirlingLikeEntry`, defined by the recurrence
`S_{i,j} = S_{i-1,j-1} + j S_{i-1,j}` with first row
`α_{j-1}` and first column `α₀`; `uEntry` is the analogous
recurrence for `U_α`, and `rEntry`/`rTildeEntry` are the
closed forms for `R_α` and its inverse candidate
`R̃_α`, built from `psi` (`Ψ_α(k) = ∑_{l<k} α_l/(k-1-l)!`)
and `omega` (`Ω(α,j) = ∑_{l<j} (j-1)↓_l α_l`). The paper's
`Λ(α,k₁,k₂)` is `lambda`; `s(i,j)` is MathlibExt's
`signedStirlingFirst` and `S(i,j)` is
`Nat.stirlingSecond`. Finite matrices are `Matrix (Fin n)
(Fin n) ℚ` with entry `(a,b)` the paper's
`(a+1, b+1)`-entry. Entry values at index `0` are junk
(`0`); all statements quantify over indices `≥ 1` as in the
paper. All identities were verified numerically for a test
sequence `α` before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- Entries of the Stirling-like matrix `S_α` in 1-based
indexing, by the paper's recurrence (value `0` at index
`0`). -/
def stirlingLikeEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j = 1 then α 0
      else if j = 0 then 0
      else stirlingLikeEntry α (i + 1) (j - 1) +
        (j : ℚ) * stirlingLikeEntry α (i + 1) j

/-- Entries of the matrix `U_α` in 1-based indexing, by
the paper's recurrence (value `0` at index `0` and in the
first column below the top entry). -/
def uEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j ≤ 1 then 0
      else uEntry α (i + 1) (j - 1) +
        ((j : ℚ) - (i + 2) + 1) * uEntry α (i + 1) j

/-- The paper's `Ψ_α(k) = ∑_{l=0}^{k-1} α_l/(k-1-l)!`. -/
def psi (α : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k, α l / (k - 1 - l).factorial

/-- The paper's `Ω(α, j) = ∑_{l=0}^{j-1} (j-1)↓_l α_l`. -/
def omega (α : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range j,
    (Nat.descFactorial (j - 1) l : ℚ) * α l

/-- The paper's `Λ(α, k₁, k₂) = ∑_{l=0}^{k₁-1} C(k₁-1, l)
(l+k₂-k₁)!/(k₂-k₁)! α_{l+k₂-k₁}`. -/
def lambda (α : ℕ → ℚ) (k₁ k₂ : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k₁, (Nat.choose (k₁ - 1) l : ℚ) *
    ((l + k₂ - k₁).factorial : ℚ) / (k₂ - k₁).factorial *
    α (l + k₂ - k₁)

/-- Entries of the matrix `R_α` in 1-based indexing, by
the paper's closed form. -/
def rEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then (-1 : ℚ) ^ (j - i) / (j - i).factorial * psi α i
  else 0

/-- Entries of the matrix `R̃_α` in 1-based indexing, by
the paper's closed form. -/
def rTildeEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then
    (Nat.descFactorial (j - 1) (i - 1) : ℚ) / omega α j
  else 0

/-- The finite Stirling-like matrix `S_α(n)`. -/
def stirlingLikeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => stirlingLikeEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `U_α(n)`. -/
def uMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => uEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `R_α(n)`. -/
def rMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `R̃_α(n)`. -/
def rTildeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rTildeEntry α (a.val + 1) (b.val + 1)

/-- The Stirling matrix of the second kind `S(n)`. -/
def stirlingMatrix2 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    (Nat.stirlingSecond (a.val + 1) (b.val + 1) : ℚ)

/-- The Vandermonde matrix `V(n)` with `V_{i,j} = j^{i-1}`
(1-based). -/
def vandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 1 : ℕ) : ℚ) ^ a.val

/-- **Lemma 1**, explicit formula: for `j ≥ i ≥ 1`,
`U_{i,j} = Λ(α, i, j)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1. -/
theorem_wanted uEntry_eq_lambda (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hij : i ≤ j) :
    uEntry α i j = lambda α i j

/-- **Lemma 1**, triangularity: `U_α` is upper
triangular: `U_{i,j} = 0` for `j < i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1. -/
theorem_wanted uEntry_eq_zero_of_lt (α : ℕ → ℚ) (i j : ℕ)
    (h : j < i) :
    uEntry α i j = 0

/-- **Lemma 2**: the `j`-th column sum of `R_α` is
`∑_{i=1}^j R_{i,j} = α_{j-1}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 2. -/
theorem_wanted sum_rEntry_col (α : ℕ → ℚ) (j : ℕ)
    (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Icc 1 j, rEntry α i j = α (j - 1)

/-- **Theorem 3**: the two decompositions
`S_α(n) = S(n) U_α(n)` and `S_α(n) = V(n) R_α(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 3. -/
theorem_wanted stirlingLikeMatrix_decomp (α : ℕ → ℚ)
    (n : ℕ) :
    stirlingLikeMatrix α n = stirlingMatrix2 n * uMatrix α n ∧
      stirlingLikeMatrix α n = vandermondeMatrix n * rMatrix α n

/-- **Theorem 4**: `det S_α(n) = ∏_{i=0}^{n-1} Ω(α, i+1)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 4. -/
theorem_wanted stirlingLikeMatrix_det (α : ℕ → ℚ) (n : ℕ) :
    (stirlingLikeMatrix α n).det =
      ∏ i ∈ Finset.range n, omega α (i + 1)

/-- **Proposition 5**: for `i, j ≥ 1`,
`∑_{k=1}^{min(i,j)} S(i,k) Λ(α,k,j) =
∑_{k=1}^j k^{i-1} (-1)^{j-k}/(j-k)! Ψ_α(k)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 5. -/
theorem_wanted sum_stirlingSecond_lambda (α : ℕ → ℚ)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.Icc 1 (min i j),
        (Nat.stirlingSecond i k : ℚ) * lambda α k j =
      ∑ k ∈ Finset.Icc 1 j, (k : ℚ) ^ (i - 1) *
        ((-1 : ℚ) ^ (j - k) / (j - k).factorial) * psi α k

-- Corollary 6 of the paper (the classical formula
-- `S(i,j) = (1/j!) ∑_{k=1}^j C(j,k) (-1)^{j-k} k^i`) is
-- already proved in MathlibExt as
-- `MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum`
-- and is therefore not restated here.


/-- **Lemma 7**: `R̃_α(n) = R_α(n)⁻¹` provided
`∏_{j=1}^n Ω(α, j) ≠ 0`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 7. -/
theorem_wanted rTildeMatrix_eq_inv (α : ℕ → ℚ) (n : ℕ)
    (h : ∏ j ∈ Finset.Icc 1 n, omega α j ≠ 0) :
    rTildeMatrix α n = (rMatrix α n)⁻¹

/-- **Proposition 8**: under the nonvanishing condition,
`∑_{k₁=1}^i ∑_{k₂=k₁}^j S(i,k₁) (j-1)↓_{k₂-1}
Λ(α,k₁,k₂) = j^{i-1} Ω(α,j)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 8. -/
theorem_wanted sum_stirlingSecond_descFactorial_lambda
    (α : ℕ → ℚ) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : ∏ k ∈ Finset.Icc 1 (max i j), omega α k ≠ 0) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc k₁ j,
        (Nat.stirlingSecond i k₁ : ℚ) *
          (Nat.descFactorial (j - 1) (k₂ - 1) : ℚ) *
          lambda α k₁ k₂ =
      (j : ℚ) ^ (i - 1) * omega α j

/-- **Proposition 9**: for `i, j ≥ 1`,
`∑_{k₁=1}^i ∑_{k₂=1}^j s(i,k₁) k₂^{k₁-1}
(-1)^{j-k₂}/(j-k₂)! Ψ_α(k₂)` equals `Λ(α,i,j)` if
`i ≤ j` and `0` if `i > j`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 9. -/
theorem_wanted sum_signed_psi_eq (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) * (k₂ : ℚ) ^ (k₁ - 1) *
          ((-1 : ℚ) ^ (j - k₂) / (j - k₂).factorial) * psi α k₂ =
      if i ≤ j then lambda α i j else 0

/-- **Corollary 10**: `∑_{k₁=1}^i ∑_{k₂=1}^j
(-1)^{j-k₂} s(i,k₁) k₂^{k₁-1} / ((j-k₂)! (k₂-1)!) =
δ_{i,j}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Corollary 10. -/
theorem_wanted sum_signed_eq_delta (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (-1 : ℚ) ^ (j - k₂) * (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) *
          (k₂ : ℚ) ^ (k₁ - 1) /
          ((j - k₂).factorial * (k₂ - 1).factorial) =
      if i = j then 1 else 0

end MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted
