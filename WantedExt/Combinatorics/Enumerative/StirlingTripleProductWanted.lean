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

/-- **Triple products of Stirling numbers bracket the binomial coefficient.** Let $n$, $p$ and
$j$ be positive integers with $p \le n$. Write $S(m, i)$ for the Stirling number of the second
kind (the number of partitions of an $m$-element set into $i$ nonempty blocks) and $c(m, i)$ for
the unsigned Stirling number of the first kind (the number of permutations of $m$ elements with
exactly $i$ cycles). Then, as rational numbers,
$\frac{c(p + j, j)\, c(n + j, p + j)}{c(n + j, j)} \le \binom{n}{p} \le
\frac{S(p + j, j)\, S(n + j, p + j)}{S(n + j, j)}$.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Theorem 2.1 (`integers-2026-A108-thm-2-1`). -/
public theorem_wanted stirling_triple_ratio_bounds_choose {n p j : ℕ} (hp : 0 < p) (hj : 0 < j)
    (hpn : p ≤ n) :
    ((n.choose p : ℕ) : ℚ) ≤
        (Nat.stirlingSecond (p + j) j : ℚ) * Nat.stirlingSecond (n + j) (p + j) /
          Nat.stirlingSecond (n + j) j ∧
      (Nat.stirlingFirst (p + j) j : ℚ) * Nat.stirlingFirst (n + j) (p + j) /
          Nat.stirlingFirst (n + j) j ≤ (n.choose p : ℚ)

/-- **Gy's inequality for Stirling numbers of the second kind.** Let $n$ and $k$ be natural
numbers with $0 < k \le n$, and write $S(m, i)$ for the Stirling number of the second kind, the
number of partitions of an $m$-element set into $i$ nonempty blocks. Then
$(n - 2k)\,S(n + 1, n + 1 - k) < n\,S(n, n - k)$, where the left side is computed in the
integers, so that $n - 2k$ may be negative.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Lemma 2.1 (`integers-2026-A108-lem-2-1`). -/
public theorem_wanted mul_stirlingSecond_sub_gt {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ((n : ℤ) - 2 * k) * Nat.stirlingSecond (n + 1) (n + 1 - k) <
      (n : ℤ) * Nat.stirlingSecond n (n - k)

/-- **Gy's triple-ratio inequalities for log-concave sequences.** Let $n$, $p$ and $j$ be
positive integers, at least two of which equal $1$, and let $x_1, x_2, \dots$ be positive reals
with $x_{k-1} x_{k+1} \le x_k^2$ for all $k \ge 2$. For $m \ge 0$ write $e_i(m)$ and $h_i(m)$ for
the elementary and the complete homogeneous symmetric polynomials of degree $i$ evaluated at
$(x_1, \dots, x_m)$, and put $N = n + p + j$. Then
$$\frac{e_{n+p}(N)}{e_{n+p}(N-1)} \le \frac{e_n(N)}{e_n(N-1)} \cdot \frac{e_p(p+j)}{e_p(p+j-1)}$$
and
$$\frac{h_n(p+j+1)}{h_n(p+j)} \cdot \frac{h_p(j+1)}{h_p(j)} \le \frac{h_{n+p}(j+1)}{h_{n+p}(j)}.$$

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

/-- **Gy's triple-ratio inequalities for log-convex sequences.** Let $n$, $p$ and $j$ be
positive integers, at least two of which equal $1$, and let $x_1, x_2, \dots$ be positive reals
with $x_k^2 \le x_{k-1} x_{k+1}$ for all $k \ge 2$. For $m \ge 0$ write $e_i(m)$ and $h_i(m)$ for
the elementary and the complete homogeneous symmetric polynomials of degree $i$ evaluated at
$(x_1, \dots, x_m)$, and put $N = n + p + j$. Then
$$\frac{e_n(N)}{e_n(N-1)} \cdot \frac{e_p(p+j)}{e_p(p+j-1)} \le \frac{e_{n+p}(N)}{e_{n+p}(N-1)}$$
and
$$\frac{h_{n+p}(j+1)}{h_{n+p}(j)} \le \frac{h_n(p+j+1)}{h_n(p+j)} \cdot \frac{h_p(j+1)}{h_p(j)}.$$

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
