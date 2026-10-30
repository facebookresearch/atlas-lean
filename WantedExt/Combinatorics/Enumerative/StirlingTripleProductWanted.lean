/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Triple products of Stirling numbers and of symmetric polynomials (statements)

Statement-only targets from René Gy, *On Certain Products of Three Stirling Numbers*,
INTEGERS 26 (2026), Article A108. `Nat.stirlingFirst` is the unsigned Stirling number of the
first kind `[n, k]` and `Nat.stirlingSecond` the Stirling number of the second kind `{n, k}`.
For a sequence `x : ℕ → ℝ` indexed from `1`, `e_k(x_m)` and `h_k(x_m)` are the elementary and
complete homogeneous symmetric polynomials of degree `k` evaluated at `(x_1, …, x_m)`, written
with `MvPolynomial.esymm` and `MvPolynomial.hsymm` over `Fin m`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 2.1: for positive integers `n ≥ p` and `j`,
`{p+j, j}{n+j, p+j}/{n+j, j} ≥ C(n, p) ≥ [p+j, j][n+j, p+j]/[n+j, j]`.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Theorem 2.1 (`integers-2026-A108-thm-2-1`). -/
public theorem_wanted stirling_triple_ratio_bounds_choose {n p j : ℕ} (hp : 0 < p) (hj : 0 < j)
    (hpn : p ≤ n) :
    ((n.choose p : ℕ) : ℚ) ≤
        (Nat.stirlingSecond (p + j) j : ℚ) * Nat.stirlingSecond (n + j) (p + j) /
          Nat.stirlingSecond (n + j) j ∧
      (Nat.stirlingFirst (p + j) j : ℚ) * Nat.stirlingFirst (n + j) (p + j) /
          Nat.stirlingFirst (n + j) j ≤ (n.choose p : ℚ)

/-- Lemma 2.1: for integers `0 < k ≤ n`, `n {n, n-k} > (n - 2k) {n+1, n+1-k}`.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Lemma 2.1 (`integers-2026-A108-lem-2-1`). -/
public theorem_wanted mul_stirlingSecond_sub_gt {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ((n : ℤ) - 2 * k) * Nat.stirlingSecond (n + 1) (n + 1 - k) <
      (n : ℤ) * Nat.stirlingSecond n (n - k)

/-- Theorem 3.1, log-concave case: let `n, p, j` be positive integers, two of which equal `1`,
and `x_k` (`k ≥ 1`) a log-concave sequence of positive reals. Then
`e_n(x_{n+p+j}) e_p(x_{p+j}) / (e_n(x_{n+p+j-1}) e_p(x_{p+j-1})) ≥
e_{n+p}(x_{n+p+j}) / e_{n+p}(x_{n+p+j-1})` and
`h_n(x_{p+j+1}) h_p(x_{j+1}) / (h_n(x_{p+j}) h_p(x_j)) ≤ h_{n+p}(x_{j+1}) / h_{n+p}(x_j)`.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Theorem 3.1 (`integers-2026-A108-thm-3-1`). -/
public theorem_wanted symm_triple_ratio_of_logConcave (x : ℕ → ℝ)
    (hpos : ∀ k, 1 ≤ k → 0 < x k) (hlc : ∀ k, 2 ≤ k → x (k - 1) * x (k + 1) ≤ x k ^ 2)
    {n p j : ℕ} (hn : 0 < n) (hp : 0 < p) (hj : 0 < j)
    (h11 : (n = 1 ∧ p = 1) ∨ (n = 1 ∧ j = 1) ∨ (p = 1 ∧ j = 1)) :
    MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ (n + p)) ≤
      MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j)) ℝ n) /
          MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ n) *
        (MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j)) ℝ p) /
          MvPolynomial.eval (fun i : Fin (p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j - 1)) ℝ p)) ∧
    MvPolynomial.eval (fun i : Fin (p + j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j + 1)) ℝ n) /
        MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j)) ℝ n) *
      (MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ p) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ p)) ≤
      MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ (n + p))

/-- Theorem 3.1, log-convex case: under the hypotheses of `symm_triple_ratio_of_logConcave`
with `x` log-convex instead of log-concave, both inequalities are reversed.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Theorem 3.1 (`integers-2026-A108-thm-3-1`). -/
public theorem_wanted symm_triple_ratio_of_logConvex (x : ℕ → ℝ)
    (hpos : ∀ k, 1 ≤ k → 0 < x k) (hlc : ∀ k, 2 ≤ k → x k ^ 2 ≤ x (k - 1) * x (k + 1))
    {n p j : ℕ} (hn : 0 < n) (hp : 0 < p) (hj : 0 < j)
    (h11 : (n = 1 ∧ p = 1) ∨ (n = 1 ∧ j = 1) ∨ (p = 1 ∧ j = 1)) :
    MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j)) ℝ n) /
          MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ n) *
        (MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j)) ℝ p) /
          MvPolynomial.eval (fun i : Fin (p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j - 1)) ℝ p)) ≤
      MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ (n + p)) ∧
    MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ (n + p)) ≤
      MvPolynomial.eval (fun i : Fin (p + j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j + 1)) ℝ n) /
        MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j)) ℝ n) *
      (MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ p) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ p))

end

end MetaMathlibExt
