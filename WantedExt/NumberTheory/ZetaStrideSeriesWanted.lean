/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- The alternating stride sum `S_{q,t}(n) = ∑_{j=1}^{⌊(n+q-1)/q⌋} (-1)^{j+1} / (n+q-qj)^t`,
written with `i = j - 1` as `∑_{i < ⌊(n+q-1)/q⌋} (-1)^i / (n - qi)^t`: the alternating sum
of `m^{-t}` over `m = n, n - q, n - 2q, …, m ≥ 1`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public noncomputable def strideAlternatingSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ i / ((n - q * i : ℕ) : ℝ) ^ t

/-- The signed stride sum `∑_{j=1}^{⌊(n+q-1)/q⌋} (-1)^{(q+1)(j+1)} / (n+q-qj)^t`, written
with `i = j - 1` as `∑_{i < ⌊(n+q-1)/q⌋} (-1)^{(q+1) i} / (n - qi)^t`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public noncomputable def strideSignedSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ ((q + 1) * i) / ((n - q * i : ℕ) : ℝ) ^ t

private theorem div_eq_one_of_le {q n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    (n + q - 1) / q = 1 :=
  Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem div_add_eq {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (n + q + q - 1) / q = (n + q - 1) / q + 1 := by
  rw [show n + q + q - 1 = n + q - 1 + q by omega, Nat.add_div_right _ hq]

/-- For `1 ≤ n ≤ q` the alternating stride sum has the single term `n^{-t}`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideAlternatingSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideAlternatingSum, div_eq_one_of_le hn hnq]

/-- For `1 ≤ n ≤ q` the signed stride sum has the single term `n^{-t}`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideSignedSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideSignedSum, div_eq_one_of_le hn hnq]

/-- Recurrence `S_{q,t}(n + q) = (n + q)^{-t} - S_{q,t}(n)` for `n ≥ 1`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideAlternatingSum q t (n + q) = 1 / ((n + q : ℕ) : ℝ) ^ t - strideAlternatingSum q t n := by
  rw [strideAlternatingSum, div_add_eq hq hn, Finset.sum_range_succ', strideAlternatingSum,
    sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + q - q * (i + 1) = n - q * i by rw [Nat.mul_succ]; omega, pow_succ]
    ring

/-- Recurrence `T_{q,t}(n + q) = (n + q)^{-t} + (-1)^{q+1} T_{q,t}(n)` for `n ≥ 1`, where
`T_{q,t}` is the signed stride sum.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideSignedSum q t (n + q) =
      1 / ((n + q : ℕ) : ℝ) ^ t + (-1 : ℝ) ^ (q + 1) * strideSignedSum q t n := by
  rw [strideSignedSum, div_add_eq hq hn, Finset.sum_range_succ', strideSignedSum,
    Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + q - q * (i + 1) = n - q * i by rw [Nat.mul_succ]; omega, mul_add, mul_one,
      pow_add]
    ring

/-- Series representation of `ζ(t+1)`: for `q, t ≥ 1`,
`ζ(t+1) = ∑_{n ≥ 1} (2n+q)/(n(n+q)) S_{q,t}(n)`. The series is only conditionally
convergent (`S_{q,t}(n)` does not tend to `0`), so it is stated as the limit of its
partial sums. The second equality of (9) and the general identity (8) use the quantity
`A^{(t)}`, which the record does not define, and are not formalized.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public theorem_wanted tendsto_strideAlternatingSum_riemannZeta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1)))

/-- Digamma identity: for `q, t ≥ 1` and `-1 ≤ a < 1`,
`(1/2q) ∑_{n≥1} (-1)^{n+1} n^{-t} [ψ((n+a+1+q)/2q) - ψ((n+a+1)/2q)]
 + (1/2q) ∑_{n≥1} (-1)^{n+1} n^{-t} [ψ((n-a-1+2q)/2q) - ψ((n-a-1+q)/2q)]
 = ∑_{n≥1} (-1)^{n+1} (2n+q)/((n+a+1)(n-a-1+q)) T_{q,t}(n)`, with `T_{q,t}` the signed
stride sum. The right side is conditionally convergent and stated as a limit of partial
sums; the two digamma series converge absolutely.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (24). -/
public theorem_wanted tendsto_strideSignedSum_digamma (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (a : ℝ) (ha : -1 ≤ a) (ha' : a < 1) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) /
          (((n : ℝ) + 1 + a + 1) * ((n : ℝ) + 1 - a - 1 + q)) *
            strideSignedSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 + a + 1 + q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 + a + 1) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 - a - 1 + 2 * q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 - a - 1 + q) / (2 * q)))) / (2 * q)))

/-- Series representation of the Dirichlet eta function: for `q, t ≥ 1`,
`η(t+1) = ∑_{n≥1} (-1)^{n+1} (2n+q)/(n(n+q)) T_{q,t}(n)` (limit of partial sums), with
`η(s) = ∑_{n≥1} (-1)^{n+1} n^{-s}`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public theorem_wanted tendsto_strideSignedSum_dirichletEta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideSignedSum q t (n + 1))
      atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (t + 1)))

/-- Digamma identity over odd indices: for `q, t ≥ 1` and `-1 ≤ a < 1`,
`(1/2q) ∑_{n≥1} (2n-1)^{-t} [ψ((2n+a+q)/2q) - ψ((2n+a)/2q)]
 + (1/2q) ∑_{n≥1} (2n-1)^{-t} [ψ((2n-a-2+2q)/2q) - ψ((2n-a-2+q)/2q)]
 = ∑_{n≥1} (1/2) (2n+q)/((n+a+1)(n-a-1+q)) (S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n))`.
The two right-hand series are summed termwise and stated as one limit of partial sums.

Deviation: the paper prints the factor `2` where this statement has `1/2`; as printed the
right side is four times the left (`q = t = 1`, `a = -1`: `4λ(2) ≈ 4.935` against
`λ(2) = π²/8 ≈ 1.234`). With `1/2` the identity checks numerically for several `(a, q, t)`,
and at `a = -1` it is the `λ` form below, half the sum of the paper's series (9) for
`ζ(t+1)` and (25) for `η(t+1)`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3,
equation (27) (`integers-2024-A45-thm-3`). -/
public theorem_wanted tendsto_strideSums_digamma_odd (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (a : ℝ) (ha : -1 ≤ a) (ha' : a < 1) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) /
          (2 * (((n : ℝ) + 1 + a + 1) * ((n : ℝ) + 1 - a - 1 + q))) *
            (strideAlternatingSum q t (n + 1) + (-1 : ℝ) ^ n * strideSignedSum q t (n + 1)) :
          ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, 1 / (2 * ((n : ℂ) + 1) - 1) ^ t *
          (Complex.digamma ((2 * ((n : ℂ) + 1) + a + q) / (2 * q)) -
            Complex.digamma ((2 * ((n : ℂ) + 1) + a) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, 1 / (2 * ((n : ℂ) + 1) - 1) ^ t *
          (Complex.digamma ((2 * ((n : ℂ) + 1) - a - 2 + 2 * q) / (2 * q)) -
            Complex.digamma ((2 * ((n : ℂ) + 1) - a - 2 + q) / (2 * q)))) / (2 * q)))

/-- Series representation of the Dirichlet lambda function: for `q, t ≥ 1`,
`λ(t+1) = ∑_{n≥1} (1/2) (2n+q)/(n(n+q)) (S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n))` (limit of
partial sums), with `λ(s) = ∑_{n≥0} (2n+1)^{-s}`; this is half the sum of the series (9) for
`ζ(t+1)` and (25) for `η(t+1)`.

Deviation: the paper prints the factor `2` where this statement has `1/2`; as printed the
right side is `4λ(t+1)` (`q = t = 1`: about `4.935` against `λ(2) = π²/8 ≈ 1.234`).

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3,
equation (28) (`integers-2024-A45-thm-3`). -/
public theorem_wanted tendsto_strideSums_dirichletLambda (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 1 + q))) *
          (strideAlternatingSum q t (n + 1) + (-1 : ℝ) ^ n * strideSignedSum q t (n + 1)))
      atTop (𝓝 (∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ (t + 1)))

/-- Series representation of `ζ(p+t+1)`: for `q, t ≥ 1` and even `p ≥ 0`,
`ζ(p+t+1) = ∑_{n≥1} (n^{p+1} + (n+q)^{p+1})/(n(n+q))^{p+1} S_{q,t}(n)` (limit of partial
sums). The second equality of (32) uses the undefined `A^{(t)}` and is not formalized.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 4,
equation (32). -/
public theorem_wanted tendsto_strideAlternatingSum_riemannZeta_add (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) (hp : Even p) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) *
            strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((p : ℂ) + t + 1)))

/-- Series representation of `η(p+t+1)`: for `q, t ≥ 1` and even `p ≥ 0`,
`η(p+t+1) = ∑_{n≥1} (-1)^{n+1} (n^{p+1} + (n+q)^{p+1})/(n(n+q))^{p+1} T_{q,t}(n)` (limit of
partial sums).

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 5,
equation (40). -/
public theorem_wanted tendsto_strideSignedSum_dirichletEta_add (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) (hp : Even p) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) * strideSignedSum q t (n + 1))
      atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (p + t + 1)))

/-- Digamma identity at `a = -1/2`: for `q, t ≥ 1`,
`(1/2q) ∑_{n≥1} n^{-t} [ψ((n+1/2+q)/2q) - ψ((n+1/2)/2q)]
 + (1/2q) ∑_{n≥1} n^{-t} [ψ((n-1/2+2q)/2q) - ψ((n-1/2+q)/2q)]
 = ∑_{n≥1} (2n+q)/((n+1/2)(n-1/2+q)) S_{q,t}(n)` (right side as a limit of partial sums).

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (20). -/
public theorem_wanted tendsto_strideAlternatingSum_digamma_half (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 + 1 / 2) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2 * q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 - 1 / 2 + q) / (2 * q)))) / (2 * q)))

/-- For `t ≥ 1`, `∑_{n≥1} 1/(n^t (2n-1)) = 2^t log 2 - ∑_{j=1}^{t-1} 2^{t-1-j} ζ(j+1)`.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (22). -/
public theorem_wanted tsum_inv_pow_mul_two_mul_sub_one (t : ℕ) (ht : 0 < t) :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ t * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      2 ^ t * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 (t - 1), (2 : ℂ) ^ (t - 1 - j) * riemannZeta ((j : ℂ) + 1)

end

end MetaMathlibExt
