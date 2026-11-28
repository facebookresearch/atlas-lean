/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangular
public import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangularIsGenFrobeniusNumberConsMulOfGcd

/-!
Statements from Subwattanachai on the generalized Frobenius number of three consecutive triangular
numbers `t_n = n(n+1)/2`. The generalized Frobenius number `g(A; s)` is the largest integer with at
most `s` representations as a nonnegative integer combination of `A`; it is encoded by the
predicate `MetaMathlibExt.IsGenFrobeniusNumber A s g` from
`MathlibExt.NumberTheory.GeneralizedFrobeniusNumber`, which determines `g` uniquely. Every
generator vector below is positive, so the `ℕ∞`-valued representation count is finite there.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Frobenius numbers of three consecutive triangular numbers.** For a natural number
$j$ write $t_j = j(j+1)/2$. Let $n$ and $s$ be natural numbers, let $r = \lfloor\sqrt{s}\rfloor$,
let $\delta_s = 1$ if $s \ge r^2 + r$ and $\delta_s = 0$ otherwise, and put
$q_s = 2r + 2 + \delta_s$ and $c_s = s - r^2 - \delta_s r$. Suppose that
$n > 6\lfloor\sqrt{s+1}\rfloor - 6$ if $n$ is even and $n > 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$
if $n$ is odd. Then the generalized Frobenius number $g$ of $(t_n, t_{n+1}, t_{n+2})$ at $s$ exists
and satisfies $4(g + 1) = (n+1)(n+2)(q_s n + 6c_s)$ if $n$ is even and
$4(g + 1) = (n+1)(n+2)(q_s n + 6c_s - 3\delta_s)$ if $n$ is odd.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Theorem 1 (`integers-2026-A63-thm-1`). -/
public theorem_wanted isGenFrobeniusNumber_triangularTriple (n s : ℕ)
    (hn : triangularFrobeniusBound n s < n) :
    let r : ℤ := Nat.sqrt s
    let δ : ℤ := if r * r + r ≤ s then 1 else 0
    let q : ℤ := 2 * r + 2 + δ
    let c : ℤ := s - r * r - δ * r
    ∃ g : ℤ, IsGenFrobeniusNumber (triangularTriple n) s g ∧
      4 * (g + 1) = (n + 1) * (n + 2) * (q * n + 6 * c - if Even n then 0 else 3 * δ)

/-- **Komatsu's conjecture on generalized Frobenius numbers of triangular triples.** For a natural
number $r$ write $t_r = r(r+1)/2$. Let $n$ and $s$ be natural numbers, let
$N_{s+1} = 6\lfloor\sqrt{s+2}\rfloor - 6$ if $n$ is even and
$N_{s+1} = 6\lfloor(\sqrt{4s+9} - 1)/2\rfloor - 3$ if $n$ is odd, and suppose $n > N_{s+1}$. Let
$g_s$ and $g_{s+1}$ be the generalized Frobenius numbers of $(t_n, t_{n+1}, t_{n+2})$ at $s$ and at
$s + 1$, and put $P = (n+1)(n+2)$. Then: (i) if $s + 1$ is neither $k^2$ nor $k(k+1)$ for any
integer $k \ge 1$, then $4(g_{s+1} - g_s) = 6P$; (ii) if $n$ is even and $s + 1 = k^2$ or
$s + 1 = k(k+1)$ for an integer $k \ge 1$, then $4(g_{s+1} - g_s) = (n - 6k + 6)P$; (iii) if $n$ is
odd and $k \ge 1$ is an integer, then $4(g_{s+1} - g_s) = (n - 6k + 9)P$ when $s + 1 = k^2$, and
$4(g_{s+1} - g_s) = (n - 6k + 3)P$ when $s + 1 = k(k+1)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Theorem 2 (`integers-2026-A63-thm-2`). -/
public theorem_wanted isGenFrobeniusNumber_triangularTriple_succ_sub (n s : ℕ)
    (hn : triangularFrobeniusBound n (s + 1) < n) (g g' : ℤ)
    (hg : IsGenFrobeniusNumber (triangularTriple n) s g)
    (hg' : IsGenFrobeniusNumber (triangularTriple n) (s + 1) g') :
    ((∀ k : ℕ, 1 ≤ k → s + 1 ≠ k * k ∧ s + 1 ≠ k * (k + 1)) →
        4 * (g' - g) = 6 * ((n + 1) * (n + 2))) ∧
      (Even n → ∀ k : ℕ, 1 ≤ k → (s + 1 = k * k ∨ s + 1 = k * (k + 1)) →
        4 * (g' - g) = ((n : ℤ) - 6 * k + 6) * ((n + 1) * (n + 2))) ∧
      (¬ Even n → ∀ k : ℕ, 1 ≤ k →
        (s + 1 = k * k → 4 * (g' - g) = ((n : ℤ) - 6 * k + 9) * ((n + 1) * (n + 2))) ∧
        (s + 1 = k * (k + 1) → 4 * (g' - g) = ((n : ℤ) - 6 * k + 3) * ((n + 1) * (n + 2))))

/-- **Generalized Frobenius numbers of triangular triples in parametrized form.** For a natural
number $r$ write $t_r = r(r+1)/2$. Let $n$, $k$, $i$ be natural numbers with $i \le 2k + 1$ and
put $s = k(k+1) + i$. Suppose that $s \le 2$ or that $s$ is neither $m^2$ nor $m(m+1)$ for any
integer $m \ge 1$. Let $N_s = 6\lfloor\sqrt{s+1}\rfloor - 6$ if $n$ is even and
$N_s = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ if $n$ is odd, and suppose $n \ge 2$ and $n > N_s$.
For even $n$ let $(x_s, y_s) = (i, 2(k - i))$ if $i \le k$ and
$(x_s, y_s) = (i - k - 1, 4k - 2i + 3)$ if $i > k$; for odd $n$ let $(x_s, y_s) = (2i, k - i)$ if
$i \le k$ and $(x_s, y_s) = (2(i - k) - 1, 2k - i + 1)$ if $i > k$. Then the generalized Frobenius
number $g$ of $(t_n, t_{n+1}, t_{n+2})$ at $s$ exists and satisfies
$4(g + 1) = (n+1)(n+2)\bigl((2x_s + y_s + 3)n + 6x_s\bigr)$ if $n$ is even and
$4(g + 1) = (n+1)(n+2)\bigl((x_s + 2y_s + 3)n + 3(x_s - 1)\bigr)$ if $n$ is odd.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Theorem 3 (`integers-2026-A63-thm-3`). -/
public theorem_wanted isGenFrobeniusNumber_triangularTriple_of_xy (n k i : ℕ)
    (hi : i ≤ 2 * k + 1)
    (hs : k * (k + 1) + i ≤ 2 ∨
      ∀ m : ℕ, 1 ≤ m → k * (k + 1) + i ≠ m * m ∧ k * (k + 1) + i ≠ m * (m + 1))
    (hn2 : 2 ≤ n) (hn : triangularFrobeniusBound n (k * (k + 1) + i) < n) :
    let x : ℤ := triangularFrobeniusX n k i
    let y : ℤ := triangularFrobeniusY n k i
    ∃ g : ℤ, IsGenFrobeniusNumber (triangularTriple n) (k * (k + 1) + i) g ∧
      4 * (g + 1) = (n + 1) * (n + 2) *
        (if Even n then (2 * x + y + 3) * n + 6 * x else (x + 2 * y + 3) * n + 3 * (x - 1))

end

end MetaMathlibExt
