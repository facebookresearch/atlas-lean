/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.LinearAlgebra.Matrix.LowerToeplitz
public import MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors

/-!
# Total positivity of Bell-type Riordan arrays

Statement from Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total
Positivity of Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A Bell-type Riordan array `(g(x), x g(x))` over `ℝ`, with entries
`d(n, k) = [x^n] g(x) (x g(x))^k` and `g(0) ≠ 0`, whose `A`-sequence `(a_j)` (characterized by
`d(n+1, k+1) = ∑_j a_j d(n, k+j)`) is a Pólya frequency sequence (its lower Toeplitz matrix
`[a_{n-k}]` has all minors non-negative) is totally positive (all minors of `[d(n, k)]` are
non-negative). The sum over `j` stops at `j ≤ n`, since `d(n, m) = 0` for `m > n`.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Proposition 5. -/
public theorem_wanted bellRiordan_hasNonnegativeMinors_of_aSequence (g : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0) (a : ℕ → ℝ)
    (ha : ∀ n k : ℕ, PowerSeries.coeff (n + 1) (g * (PowerSeries.X * g) ^ (k + 1)) =
      ∑ j ∈ Finset.range (n + 1),
        a j * PowerSeries.coeff n (g * (PowerSeries.X * g) ^ (k + j)))
    (hpf : Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz a)) :
    Matrix.HasNonnegativeMinors
      (Matrix.of fun n k : ℕ => PowerSeries.coeff n (g * (PowerSeries.X * g) ^ k))

/-- `R` is the Riordan array with `A`-sequence `a` and `Z`-sequence `z`: `r_{0,0} = 1`,
`r_{0,k} = 0` for `k ≥ 1`, `r_{n+1,0} = ∑_j z_j r_{n,j}` and
`r_{n+1,k+1} = ∑_j a_j r_{n,k+j}`. The sums stop at `j ≤ n`, since the recurrence makes
`r_{n,m} = 0` for `m > n`.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1, equation (1). -/
def IsRiordanArrayAZ (a z : ℕ → ℝ) (R : ℕ → ℕ → ℝ) : Prop :=
  R 0 0 = 1 ∧ (∀ k, R 0 (k + 1) = 0) ∧
    (∀ n, R (n + 1) 0 = ∑ j ∈ Finset.range (n + 1), z j * R n j) ∧
    ∀ n k, R (n + 1) (k + 1) = ∑ j ∈ Finset.range (n + 1), a j * R n (k + j)

/-- The first entries of a Riordan array: `r_{1,0} = z_0` and `r_{1,1} = a_0`.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1, equation (1). -/
theorem IsRiordanArrayAZ.one_zero_and_one_one {a z : ℕ → ℝ} {R : ℕ → ℕ → ℝ}
    (h : IsRiordanArrayAZ a z R) : R 1 0 = z 0 ∧ R 1 1 = a 0 := by
  obtain ⟨h00, -, hz, ha⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hz 0]; simp [h00]
  · rw [ha 0 0]; simp [h00]

/-- The coefficient matrix `J(Z(x), A(x))` of a Riordan array: column `0` is `z_0, z_1, …`, and
the remaining columns form the lower Toeplitz matrix of `a`, so row `n` reads
`z_n, a_n, a_{n-1}, …, a_0, 0, …`.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1. -/
def riordanCoeffMatrix (z a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun n k => if k = 0 then z n else if k ≤ n + 1 then a (n + 1 - k) else 0

/-- Entries of `J(Z(x), A(x))`: `J_{n,0} = z_n` and `J_{n,1} = a_n`.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1. -/
theorem riordanCoeffMatrix_zero_one (z a : ℕ → ℝ) (n : ℕ) :
    riordanCoeffMatrix z a n 0 = z n ∧ riordanCoeffMatrix z a n 1 = a n := by
  simp [riordanCoeffMatrix]

/-- Proposition 1 (quoted from Chen, Liang and Wang): a Riordan array `R` with `A`- and
`Z`-sequences `a`, `z` is totally positive if its coefficient matrix `J(Z(x), A(x))` is.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Proposition 1 (`jis-2025-25.7.5-prop-1`). -/
public theorem_wanted riordanArray_hasNonnegativeMinors_of_coeffMatrix {a z : ℕ → ℝ}
    {R : ℕ → ℕ → ℝ} (hR : IsRiordanArrayAZ a z R)
    (hJ : Matrix.HasNonnegativeMinors (riordanCoeffMatrix z a)) :
    Matrix.HasNonnegativeMinors (Matrix.of R)

/-- Theorem 2: let `P, Q` be formal power series with `P(0) ≠ 0`, `a, b, r, s, t ≥ 0`, and let
`R = R(P, Q; a, b, r, s, t)` be the Riordan array with
`A(x) = (P² + sxP + tx²) / (P - rx)` and
`Z(x) = ((P² + sxP + tx²) Q + (aP + bx)(P - xQ)) / (P² - rxP)` (stated with denominators
cleared). If `J(Q(x), P(x))` is totally positive, `s² ≥ 4t` and `as + a√(s² - 4t) ≥ 2b`, then
`R` is totally positive. The paper leaves `P(0) ≠ 0` implicit (it makes `A`, `Z` well defined).

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Theorem 2 (`jis-2025-25.7.5-thm-2`). -/
public theorem_wanted riordanArray_hasNonnegativeMinors_of_params (P Q A Z : PowerSeries ℝ)
    (hP : PowerSeries.constantCoeff P ≠ 0) {a b r s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : A * (P - PowerSeries.C r * PowerSeries.X) =
      P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2)
    (hZ : Z * (P ^ 2 - PowerSeries.C r * PowerSeries.X * P) =
      (P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2) * Q +
        (PowerSeries.C a * P + PowerSeries.C b * PowerSeries.X) * (P - PowerSeries.X * Q))
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => PowerSeries.coeff n A) (fun n => PowerSeries.coeff n Z) R)
    (hJ : Matrix.HasNonnegativeMinors
      (riordanCoeffMatrix (fun n => PowerSeries.coeff n Q) (fun n => PowerSeries.coeff n P)))
    (hst : 4 * t ≤ s ^ 2) (hab : 2 * b ≤ a * s + a * Real.sqrt (s ^ 2 - 4 * t)) :
    Matrix.HasNonnegativeMinors (Matrix.of R)

/-- Corollary 6: let `P` be a Pólya frequency formal power series (its coefficient sequence is
PF: the lower Toeplitz matrix has non-negative minors), `r, s, t ≥ 0` with `s² ≥ 4t`, and let
`R = R(P; r, s, t)` be the Bell-type Riordan array (`z_i = a_{i+1}`) with
`A(x) = (P² + sxP + tx²) / (P - rx)` (denominator cleared). Then `R` is totally positive. `P(0) ≠ 0` is added, as in Theorem 2: for
`P = 0` the cleared equation for `A` is vacuous (`A = -1` gives `R n n = (-1)^n`).

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Corollary 6 (`jis-2025-25.7.5-cor-6`). -/
public theorem_wanted bellRiordanArray_hasNonnegativeMinors_of_pf (P A : PowerSeries ℝ)
    (hP : PowerSeries.constantCoeff P ≠ 0) {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hpf : Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz fun n => PowerSeries.coeff n P))
    (hA : A * (P - PowerSeries.C r * PowerSeries.X) =
      P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2)
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => PowerSeries.coeff n A)
      (fun n => PowerSeries.coeff (n + 1) A) R)
    (hst : 4 * t ≤ s ^ 2) :
    Matrix.HasNonnegativeMinors (Matrix.of R)

end

end MetaMathlibExt
