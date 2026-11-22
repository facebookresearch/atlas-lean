/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A generalization of the Pascal and Stirling matrices

Statements from A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal
and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.

For a sequence `α = (α_j)_{j ≥ 1}` (here `α : ℕ → R` with `α 0` unused) the paper's matrices
`S_α(n)`, `𝖲_α(n)` and `𝖴_α(n)` are given by recurrences on their entries; the entry functions
below use 0-based indices, so entry `(i, j)` here is the paper's `(i + 1, j + 1)`. Statements were
checked with exact rational arithmetic before stating.
-/

open scoped Matrix

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [CommRing R]

/-- Entries of the paper's matrix `S_α(n)` (0-based): first column `α_1`, rest of the first row
`0`, and `Ŝ_{i,j} = Ŝ_{i-1,j-1} + α_j Ŝ_{i-1,j}` for `i, j ≥ 2` (1-based).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4,
equation (a-1). -/
def alphaStirlingEntry (α : ℕ → R) : ℕ → ℕ → R
  | _, 0 => α 1
  | 0, _ + 1 => 0
  | i + 1, j + 1 => alphaStirlingEntry α i j + α (j + 2) * alphaStirlingEntry α i (j + 1)

/-- Entries of the paper's shifted matrix `𝖲_α(n)` (0-based): first row and first column `α_1`,
and `𝖲_{i,j} = 𝖲_{i,j-1} + α_j 𝖲_{i-1,j}` for `i, j ≥ 2` (1-based).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def shiftedAlphaStirlingEntry (α : ℕ → R) : ℕ → ℕ → R
  | _, 0 => α 1
  | 0, _ + 1 => α 1
  | i + 1, j + 1 =>
      shiftedAlphaStirlingEntry α (i + 1) j + α (j + 2) * shiftedAlphaStirlingEntry α i (j + 1)

/-- Entries of the paper's matrix `𝖴_α(n)` (0-based): first row `1`, rest of the first column
`0`, and `𝖴_{i,j} = 𝖴_{i,j-1} + α_{i-1} 𝖴_{i-1,j-1} + (α_j - α_{i-1}) 𝖴_{i-1,j}` for
`i, j ≥ 2` (1-based).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2,
equation (u-1-2). -/
def alphaUpperEntry (α : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | _ + 1, 0 => 0
  | i + 1, j + 1 =>
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1)

/-- The recurrence of `S_α`: `Ŝ_{i+1,j+1} = Ŝ_{i,j} + α_{j+2} Ŝ_{i,j+1}` (0-based entries).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (a-1). -/
theorem alphaStirlingEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaStirlingEntry α (i + 1) (j + 1) =
      alphaStirlingEntry α i j + α (j + 2) * alphaStirlingEntry α i (j + 1) := rfl

/-- The first column of `S_α` is constant `α_1`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (a-1). -/
theorem alphaStirlingEntry_zero_right (α : ℕ → R) (i : ℕ) : alphaStirlingEntry α i 0 = α 1 := by
  cases i <;> rfl

/-- The recurrence of `𝖲_α`: `𝖲_{i+1,j+1} = 𝖲_{i+1,j} + α_{j+2} 𝖲_{i,j+1}` (0-based entries).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
theorem shiftedAlphaStirlingEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    shiftedAlphaStirlingEntry α (i + 1) (j + 1) =
      shiftedAlphaStirlingEntry α (i + 1) j + α (j + 2) * shiftedAlphaStirlingEntry α i (j + 1) := by
  rw [shiftedAlphaStirlingEntry]

/-- The first row of `𝖲_α` is constant `α_1`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
theorem shiftedAlphaStirlingEntry_zero_left (α : ℕ → R) (j : ℕ) :
    shiftedAlphaStirlingEntry α 0 j = α 1 := by
  cases j <;> rw [shiftedAlphaStirlingEntry]

/-- The recurrence (u-1-2) of `𝖴_α` (0-based entries).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (u-1-2). -/
theorem alphaUpperEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaUpperEntry α (i + 1) (j + 1) =
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1) := by
  rw [alphaUpperEntry]

/-- Small values of `𝖴_α`: `𝖴_{2,2} = α_2` and `𝖴_{2,3} = α_2 + α_3` (1-based), as in the
paper's display of `𝖴_α(4)`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
theorem alphaUpperEntry_one_one_one_two (α : ℕ → R) :
    alphaUpperEntry α 1 1 = α 2 ∧ alphaUpperEntry α 1 2 = α 2 + α 3 := by
  constructor
  · simp only [alphaUpperEntry]; ring
  · simp only [alphaUpperEntry]; ring

/-- The `n × n` matrix `S_α(n)`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def alphaStirlingMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => alphaStirlingEntry α a b

/-- The `n × n` shifted matrix `𝖲_α(n)`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def shiftedAlphaStirlingMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => shiftedAlphaStirlingEntry α a b

/-- The `n × n` matrix `𝖴_α(n)`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
def alphaUpperMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => alphaUpperEntry α a b

/-- Lemma 1, entry formula: for `j ≥ i ≥ 1` (1-based), `𝖴_{i,j} = h_{i-1}(α_i, …, α_j)`, the
complete homogeneous symmetric polynomial `MvPolynomial.hsymm`; in 0-based indices `i ≤ j`,
`𝖴_{i,j} = h_i(α_{i+1}, …, α_{j+1})`. In particular `𝖴_{i,i} = α_{i+1}^i`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
public theorem_wanted alphaUpperEntry_eq_hsymm (α : ℕ → R) {i j : ℕ} (hij : i ≤ j) :
    alphaUpperEntry α i j =
      MvPolynomial.eval (fun t : Fin (j - i + 1) => α (i + 1 + t))
        (MvPolynomial.hsymm (Fin (j - i + 1)) R i)

/-- Lemma 1, determinant: `det 𝖴_α(n) = ∏_{i=1}^n α_i^{i-1}`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
public theorem_wanted det_alphaUpperMatrix (α : ℕ → R) (n : ℕ) :
    (alphaUpperMatrix α n).det = ∏ i : Fin n, α (i + 1) ^ (i : ℕ)

/-- Theorem 2, LU decomposition: `𝖲_α(n) = S_α(n) · 𝖴_α(n)`. Stated for every sequence `α`: the
paper assumes `α_1 = 1`, but both sides scale by `α_1` and `𝖴_α` does not depend on `α_1`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 2
(`jis-2026-26.5.4-thm-2`). -/
public theorem_wanted shiftedAlphaStirlingMatrix_eq_mul (α : ℕ → R) (n : ℕ) :
    shiftedAlphaStirlingMatrix α n = alphaStirlingMatrix α n * alphaUpperMatrix α n

/-- Theorem 2, determinant: if `α_1 = 1` then `det 𝖲_α(n) = ∏_{j=1}^n α_j^{j-1}`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 2
(`jis-2026-26.5.4-thm-2`). -/
public theorem_wanted det_shiftedAlphaStirlingMatrix (α : ℕ → R) (hα : α 1 = 1) (n : ℕ) :
    (shiftedAlphaStirlingMatrix α n).det = ∏ j : Fin n, α (j + 1) ^ (j : ℕ)

/-- The paper's `𝖫_{d^{(m)}}(n)`: the `n × n` real matrix carrying the `m`-th diagonal
`d^{(m)}_b = C(m + b, b)` of Pascal's triangle on its `m`-th subdiagonal (0-based entry
`(b + m, b)`), zero elsewhere.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
def pascalDiagonalMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => if (a : ℕ) = b + m then ((m + b).choose b : ℝ) else 0

/-- `𝖫_{d^{(0)}}(n) = I_n`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
theorem pascalDiagonalMatrix_zero (n : ℕ) : pascalDiagonalMatrix 0 n = 1 := by
  ext a b
  simp [pascalDiagonalMatrix, Matrix.one_apply, Fin.val_inj]

/-- The paper's sequence `α^{(k)} = (α^{(k)}_i)_{i ≥ 1}` (1-based, value `0` at index `0`):
`α^{(k)}_1 = 1`, `α^{(k)}_i = 0` for `2 ≤ i ≤ k`, and
`α^{(k)}_i = C(i-2, k-1) α^{(k)}_{i-k}` for `i > k`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
def pascalExpFirstColumn (k i : ℕ) : ℕ :=
  if i = 1 then 1
  else if _h : 0 < k ∧ k < i then (i - 2).choose (k - 1) * pascalExpFirstColumn k (i - k)
  else 0
termination_by i
decreasing_by omega

/-- `α^{(k)}_1 = 1`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_one (k : ℕ) : pascalExpFirstColumn k 1 = 1 := by
  rw [pascalExpFirstColumn]
  simp

/-- `α^{(k)}_i = 0` for `2 ≤ i ≤ k`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_of_le {k i : ℕ} (h2 : 2 ≤ i) (hik : i ≤ k) :
    pascalExpFirstColumn k i = 0 := by
  rw [pascalExpFirstColumn]
  split_ifs <;> omega

/-- `α^{(k)}_i = C(i-2, k-1) α^{(k)}_{i-k}` for `1 ≤ k < i`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_of_lt {k i : ℕ} (hk : 1 ≤ k) (hki : k < i) :
    pascalExpFirstColumn k i = (i - 2).choose (k - 1) * pascalExpFirstColumn k (i - k) := by
  rw [pascalExpFirstColumn]
  split_ifs <;> first | rfl | omega

/-- Theorem 3: for `k ≥ 1`,
`exp(𝖫_{d^{(k)}}(n)) = T_{α^{(k)}, β}(n) ⊙ ∑_{i ≥ 0} 𝖫_{d^{(ki)}}(n)`, where `T_{α^{(k)}, β}(n)`
is the lower triangular Toeplitz matrix with first column `α^{(k)}` and first row
`β = (1, 0, 0, …)` (0-based entry `(a, b)` equal to `α^{(k)}_{a-b+1}` for `b ≤ a`) and `⊙` is the
Hadamard product. The infinite sum is written over `i < n`; the omitted terms are zero matrices
since `k i ≥ n` there.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3
(`jis-2026-26.5.4-thm-3`). -/
public theorem_wanted exp_pascalDiagonalMatrix (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    NormedSpace.exp (pascalDiagonalMatrix k n) =
      (Matrix.of fun a b : Fin n =>
          if (b : ℕ) ≤ a then (pascalExpFirstColumn k ((a : ℕ) - b + 1) : ℝ) else 0) ⊙
        ∑ i ∈ Finset.range n, pascalDiagonalMatrix (k * i) n

/-- The leading `n × n` section of the paper's lower triangular matrix `M(f)` of a formal power
series `f`: 0-based entry `(a, b)` is `a!/b! · [t^{a-b}] f` for `b ≤ a` and `0` otherwise.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
noncomputable def powerSeriesFactorialMatrix {K : Type*} [Field K] (f : PowerSeries K) (n : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if (b : ℕ) ≤ a then
      ((a : ℕ).factorial : K) / ((b : ℕ).factorial : K) * PowerSeries.coeff ((a : ℕ) - b) f
    else 0

/-- The diagonal entries of `M(f)` are the constant coefficient of `f`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
theorem powerSeriesFactorialMatrix_apply_self {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (n : ℕ) (a : Fin n) :
    powerSeriesFactorialMatrix f n a a = PowerSeries.coeff 0 f := by
  have h : ((a : ℕ).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp [powerSeriesFactorialMatrix, h]

/-- Lemma 5: `M(f) M(g) = M(fg)` for formal power series over a field of characteristic zero,
stated for every leading `n × n` section (equivalent for these lower triangular matrices).

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 5
(`jis-2026-26.5.4-lem-5`). -/
public theorem_wanted powerSeriesFactorialMatrix_mul {K : Type*} [Field K] [CharZero K]
    (f g : PowerSeries K) (n : ℕ) :
    powerSeriesFactorialMatrix f n * powerSeriesFactorialMatrix g n =
      powerSeriesFactorialMatrix (f * g) n

/-- Theorem 7: let `k ≥ 1`, let `β_1 = ⋯ = β_{k-1} = 0`, `β_k = 1` and
`β_m = ∑_{j=1}^k c_j β_{m-j}` for `m > k`. Then the determinant `D_{n,k}` of the `n × n` upper
Hessenberg-Toeplitz matrix `H_n(-1; c_1, …, c_k)` (entry `c_{j-i+1}` for `0 ≤ j - i ≤ k - 1`,
`-1` for `j - i = -1`, `0` otherwise) equals `β_{n+k}`. Sequences are 1-based (`c 0`, `β 0`
unused); stated over any commutative ring, without the paper's `c_k ≠ 0`, and also for `n = 0`.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 7
(`jis-2026-26.5.4-thm-7`). -/
public theorem_wanted det_hessenbergToeplitz_eq_recurrence (k : ℕ) (hk : 1 ≤ k) (c β : ℕ → R)
    (hβ : ∀ i, 1 ≤ i → i < k → β i = 0) (hβk : β k = 1)
    (hrec : ∀ m, k < m → β m = ∑ j ∈ Finset.Icc 1 k, c j * β (m - j)) (n : ℕ) :
    (Matrix.of fun a b : Fin n =>
        if (a : ℕ) ≤ b ∧ (b : ℕ) - a < k then c ((b : ℕ) - a + 1)
        else if (a : ℕ) = b + 1 then -1 else 0).det = β (n + k)

end

end MetaMathlibExt
