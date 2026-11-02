/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Sqrt
public import MathlibExt.NumberTheory.GeneralizedFrobeniusNumber

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

/-- **Three consecutive triangular numbers.** For a natural number $n$, the triangular triple of
$n$ is $(t_n, t_{n+1}, t_{n+2})$, where $t_m = m(m+1)/2$ is the $m$-th triangular number.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
def triangularTriple (n : ℕ) : Fin 3 → ℕ :=
  ![n * (n + 1) / 2, (n + 1) * (n + 2) / 2, (n + 2) * (n + 3) / 2]

/-- **Triangular triple at $n = 1$.** The three consecutive triangular numbers
$(t_1, t_2, t_3)$, where $t_m = m(m+1)/2$, are $(1, 3, 6)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
theorem triangularTriple_one : triangularTriple 1 = ![1, 3, 6] := by
  decide

/-- **Triangular Frobenius threshold.** For natural numbers $n$ and $s$, the threshold $N_s$ is
the integer $N_s^{\mathrm{even}} = 6\lfloor\sqrt{s+1}\rfloor - 6$ when $n$ is even and
$N_s^{\mathrm{odd}} = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ when $n$ is odd.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
def triangularFrobeniusBound (n s : ℕ) : ℤ :=
  if Even n then 6 * (Nat.sqrt (s + 1) : ℤ) - 6 else 6 * ((Nat.sqrt (4 * s + 5) - 1) / 2 : ℕ) - 3

/-- **Triangular Frobenius threshold at $s = 0$.** At $s = 0$ the triangular Frobenius threshold
$N_s$ equals $0$ for $n = 0$ (the even case, $N_0^{\mathrm{even}} = 6\lfloor\sqrt{1}\rfloor - 6$)
and $-3$ for $n = 1$ (the odd case, $N_0^{\mathrm{odd}} = 6\lfloor(\sqrt{5} - 1)/2\rfloor - 3$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
theorem triangularFrobeniusBound_zero :
    triangularFrobeniusBound 0 0 = 0 ∧ triangularFrobeniusBound 1 0 = -3 := by
  decide +kernel

/-- **The parameter $x_s$ of the triangular Frobenius formula.** For natural numbers $n$, $k$
and $i$, let $x$ be $i$ if $i \le k$ and $i - k - 1$ if $i > k$ when $n$ is even, and $2i$ if
$i \le k$ and $2(i - k) - 1$ if $i > k$ when $n$ is odd. For $s = k(k+1) + i$ with
$0 \le i \le 2k+1$ this is the integer $x_s$ (written $x_s^{\mathrm{even}}$ or
$x_s^{\mathrm{odd}}$ by the parity of $n$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusX (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then i else i - k - 1) else (if i ≤ k then 2 * i else 2 * (i - k) - 1)

/-- **The parameter $y_s$ of the triangular Frobenius formula.** For natural numbers $n$, $k$
and $i$, let $y$ be $2(k - i)$ if $i \le k$ and $4k + 3 - 2i$ if $i > k$ when $n$ is even, and
$k - i$ if $i \le k$ and $2k + 1 - i$ if $i > k$ when $n$ is odd, where a difference that would
be negative is replaced by $0$ (this happens only for $i > 2k + 1$). For $s = k(k+1) + i$ with
$0 \le i \le 2k+1$ this is the integer $y_s$ (written $y_s^{\mathrm{even}}$ or
$y_s^{\mathrm{odd}}$ by the parity of $n$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusY (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then 2 * (k - i) else 4 * k + 3 - 2 * i)
  else (if i ≤ k then k - i else 2 * k + 1 - i)

/-- **Triangular Frobenius parameters at $s = 5$.** Take $k = 1$ and $i = 3$, so that
$s = k(k+1) + i = 5$. Then $(x_s, y_s) = (1, 1)$ for $n = 0$ (the even case) and
$(x_s, y_s) = (3, 0)$ for $n = 1$ (the odd case).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1 and Table 2. -/
theorem triangularFrobeniusXY_five :
    (triangularFrobeniusX 0 1 3, triangularFrobeniusY 0 1 3) = (1, 1) ∧
      (triangularFrobeniusX 1 1 3, triangularFrobeniusY 1 1 3) = (3, 0) := by
  decide

/-- **Beck–Kifer reduction by a common factor of all generators but the first.** Let $K \ge 2$,
let $a_1$ and $\ell$ be positive integers, and let $a'_2, \dots, a'_K$ be positive integers with
$\gcd(a'_2, \dots, a'_K) = 1$ such that $\gcd(a_1, \ell a'_2, \dots, \ell a'_K) = 1$. Let $s$ be a
natural number. If $g'$ is the generalized Frobenius number $g(a_1, a'_2, \dots, a'_K; s)$, then
$\ell g' + a_1(\ell - 1)$ is the generalized Frobenius number
$g(a_1, \ell a'_2, \dots, \ell a'_K; s)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 1 (`integers-2026-A63-lem-1`), quoted from Beck
and Kifer, Lemma 4. -/
public theorem_wanted isGenFrobeniusNumber_cons_mul_of_gcd (k : ℕ) (a₁ ℓ : ℕ)
    (a' : Fin (k + 1) → ℕ) (ha₁ : 0 < a₁) (ha' : ∀ i, 0 < a' i) (hℓ : 0 < ℓ)
    (hgcd' : Finset.univ.gcd a' = 1)
    (hgcd : Finset.univ.gcd (Fin.cons a₁ (fun i => ℓ * a' i) : Fin (k + 2) → ℕ) = 1)
    (s : ℕ) (g' : ℤ) (hg' : IsGenFrobeniusNumber (Fin.cons a₁ a' : Fin (k + 2) → ℕ) s g') :
    IsGenFrobeniusNumber (Fin.cons a₁ (fun i => ℓ * a' i) : Fin (k + 2) → ℕ) s
      (ℓ * g' + a₁ * ((ℓ : ℤ) - 1))

/-- **Splitting off the first generator of the reduced triangular triple.** For a natural number
$r$ write $t_r = r(r+1)/2$, and for an integer $m$ and natural numbers $a_1, \dots, a_k$ let
$d(m; a_1, \dots, a_k)$ be the number of representations of $m$ by $(a_1, \dots, a_k)$. Let
$n \ge 1$, $d_1 = \gcd(t_{n+1}, t_{n+2})$, $a = t_{n+1}/d_1$ and $b = t_{n+2}/d_1$. Then for every
natural number $m$,

$$d(m; t_n, a, b) = \sum_{j=0}^{\lfloor m/t_n \rfloor} d(m - j t_n; a, b).$$

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 2 (`integers-2026-A63-lem-2`). -/
public theorem_wanted frobeniusRepCount_triangular_reduced_eq_sum (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] m =
      ∑ j ∈ Finset.range (m / t n + 1),
        frobeniusRepCount ![t (n + 1) / d₁, t (n + 2) / d₁] ((m : ℤ) - j * t n)

/-- **Representation counts between consecutive two-generator Frobenius numbers.** Let $a$ and $b$
be coprime positive integers. For a natural number $r$ let $g(a, b; r)$ be the generalized
Frobenius number of $(a, b)$ at $r$, and for an integer $m$ let $d(m; a, b)$ be the number of
representations of $m$ by $(a, b)$. Let $i$ and $s$ be natural numbers, let $c$ be a positive
integer divisible by $a$ or by $b$, and let $j$ be an integer. Then $d(g(a, b; s) + jc; a, b) = i$
if and only if $g(a, b; s) + jc \le g(a, b; i)$ and, in case $i \ge 1$, also
$g(a, b; i - 1) < g(a, b; s) + jc$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 3 (`integers-2026-A63-lem-3`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
public theorem_wanted frobeniusRepCount_pair_eq_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (G : ℕ → ℤ) (hG : ∀ r, IsGenFrobeniusNumber ![a, b] r (G r))
    (i s c : ℕ) (hc : 0 < c) (hdvd : a ∣ c ∨ b ∣ c) (j : ℤ) :
    frobeniusRepCount ![a, b] (G s + j * c) = i ↔
      (i = 0 ∨ G (i - 1) < G s + j * c) ∧ G s + j * c ≤ G i

/-- **Representation counts above a shifted two-generator Frobenius number.** Let $a < b$ be
coprime positive integers, let $s$ and $k$ be natural numbers, let $g$ be the generalized Frobenius
number $g(a, b; s)$, and for an integer $m$ let $d(m; a, b)$ be the number of representations of
$m$ by $(a, b)$. If $m$ is an integer with $m > g + ka$, then for every natural number $j$,
$d(m - ja; a, b) \ge d(g + (k - j)a; a, b)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 4 (`integers-2026-A63-lem-4`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
public theorem_wanted frobeniusRepCount_pair_sub_ge (a b : ℕ) (ha : 0 < a) (hab' : a < b)
    (hab : Nat.Coprime a b) (s k : ℕ) (g : ℤ) (hg : IsGenFrobeniusNumber ![a, b] s g) (m : ℤ)
    (hm : g + k * a < m) (j : ℕ) :
    frobeniusRepCount ![a, b] (g + ((k : ℤ) - j) * a) ≤ frobeniusRepCount ![a, b] (m - j * a)

/-- **Representation count of the reduced triangular triple at a shifted Frobenius number.** For a
natural number $r$ write $t_r = r(r+1)/2$. Let $n$, $k$, $i$ be natural numbers with $i \le 2k + 1$
and put $s = k(k+1) + i$. Let $N_s = 6\lfloor\sqrt{s+1}\rfloor - 6$ if $n$ is even and
$N_s = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ if $n$ is odd, and suppose $n > N_s$. For even $n$
let $(x_s, y_s) = (i, 2(k - i))$ if $i \le k$ and $(x_s, y_s) = (i - k - 1, 4k - 2i + 3)$ if
$i > k$; for odd $n$ let $(x_s, y_s) = (2i, k - i)$ if $i \le k$ and
$(x_s, y_s) = (2(i - k) - 1, 2k - i + 1)$ if $i > k$. Put $d_1 = \gcd(t_{n+1}, t_{n+2})$,
$a = t_{n+1}/d_1$ and $b = t_{n+2}/d_1$. If $g$ is the generalized Frobenius number
$g(a, b; x_s)$, then the number of representations of $g + y_s t_n$ by $(t_n, a, b)$ is $s$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 5 (`integers-2026-A63-lem-5`). -/
public theorem_wanted frobeniusRepCount_triangular_reduced_at_pair_frobenius (n k i : ℕ)
    (hi : i ≤ 2 * k + 1) (hn : triangularFrobeniusBound n (k * (k + 1) + i) < n) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    ∀ g₂ : ℤ, IsGenFrobeniusNumber ![t (n + 1) / d₁, t (n + 2) / d₁]
        (triangularFrobeniusX n k i) g₂ →
      frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁]
          (g₂ + triangularFrobeniusY n k i * t n) = k * (k + 1) + i

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

/-- **Generalized Frobenius numbers of the reduced triangular triple.** For a natural number $r$
write $t_r = r(r+1)/2$. Let $n$, $k$, $i$ be natural numbers with $i \le 2k + 1$ and put
$s = k(k+1) + i$. Let $N_s = 6\lfloor\sqrt{s+1}\rfloor - 6$ if $n$ is even and
$N_s = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ if $n$ is odd, and suppose $n > N_s$. For even $n$
let $(x_s, y_s) = (i, 2(k - i))$ if $i \le k$ and $(x_s, y_s) = (i - k - 1, 4k - 2i + 3)$ if
$i > k$; for odd $n$ let $(x_s, y_s) = (2i, k - i)$ if $i \le k$ and
$(x_s, y_s) = (2(i - k) - 1, 2k - i + 1)$ if $i > k$. Put $d_1 = \gcd(t_{n+1}, t_{n+2})$,
$a = t_{n+1}/d_1$ and $b = t_{n+2}/d_1$. Then $(x_s + 1)ab - a - b$ is the generalized Frobenius
number $g(a, b; x_s)$, and $(x_s + 1)ab - b - a + y_s t_n$ is the generalized Frobenius number
$g(t_n, a, b; s)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Theorem 4 (`integers-2026-A63-thm-4`). -/
public theorem_wanted isGenFrobeniusNumber_triangular_reduced (n k i : ℕ) (hi : i ≤ 2 * k + 1)
    (hn : triangularFrobeniusBound n (k * (k + 1) + i) < n) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    let a : ℤ := (t (n + 1) / d₁ : ℕ)
    let b : ℤ := (t (n + 2) / d₁ : ℕ)
    let x : ℤ := triangularFrobeniusX n k i
    IsGenFrobeniusNumber ![t (n + 1) / d₁, t (n + 2) / d₁] (triangularFrobeniusX n k i)
        ((x + 1) * a * b - a - b) ∧
      IsGenFrobeniusNumber ![t n, t (n + 1) / d₁, t (n + 2) / d₁] (k * (k + 1) + i)
        ((x + 1) * a * b - b - a + triangularFrobeniusY n k i * t n)

/-- **Explicit generalized Frobenius numbers of triangular triples at levels 11 to 20.** For a
natural number $r$ write $t_r = r(r+1)/2$. For a natural number $n$, a natural number $s$ and an
integer $L$, say that $s$ has value $L$ when the generalized Frobenius number $g$ of
$(t_n, t_{n+1}, t_{n+2})$ at $s$ exists and satisfies $4(g + 1) = (n+1)(n+2)L$. Then for every
natural number $n$: $11$ has value $8n + 12$ if $n = 12$ or $n \ge 14$; $12$ has value $9n$ for
even $n \ge 14$ and $9n - 3$ for odd $n \ge 17$; $13$ has value $9n + 6$ for even $n \ge 12$ and
$9n + 3$ for odd $n \ge 15$; $14$ has value $9n + 12$ for even $n \ge 12$ and $9n + 9$ for odd
$n \ge 15$; $15$ has value $9n + 18$ for even $n \ge 18$ and $9n + 15$ for odd $n \ge 15$; $16$
has value $10n$ if $n = 17$ or $n \ge 19$; $17$ has value $10n + 6$ if $n = 15$ or $n \ge 17$; $18$
has value $10n + 12$ if $n = 17$ or $n \ge 19$; $19$ has value $10n + 18$ if $n = 20$ or
$n \ge 22$; $20$ has value $11n$ for even $n \ge 18$ and $11n - 3$ for odd $n \ge 21$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Corollary 1 (`integers-2026-A63-cor-1`). -/
public theorem_wanted isGenFrobeniusNumber_triangularTriple_eleven_to_twenty (n : ℕ) :
    let F : ℕ → ℤ → Prop := fun s L =>
      ∃ g : ℤ, IsGenFrobeniusNumber (triangularTriple n) s g ∧ 4 * (g + 1) = (n + 1) * (n + 2) * L
    ((n = 12 ∨ 14 ≤ n) → F 11 (8 * n + 12)) ∧
      (Even n → 14 ≤ n → F 12 (9 * n)) ∧ (¬ Even n → 17 ≤ n → F 12 (9 * n - 3)) ∧
      (Even n → 12 ≤ n → F 13 (9 * n + 6)) ∧ (¬ Even n → 15 ≤ n → F 13 (9 * n + 3)) ∧
      (Even n → 12 ≤ n → F 14 (9 * n + 12)) ∧ (¬ Even n → 15 ≤ n → F 14 (9 * n + 9)) ∧
      (Even n → 18 ≤ n → F 15 (9 * n + 18)) ∧ (¬ Even n → 15 ≤ n → F 15 (9 * n + 15)) ∧
      ((n = 17 ∨ 19 ≤ n) → F 16 (10 * n)) ∧
      ((n = 15 ∨ 17 ≤ n) → F 17 (10 * n + 6)) ∧
      ((n = 17 ∨ 19 ≤ n) → F 18 (10 * n + 12)) ∧
      ((n = 20 ∨ 22 ≤ n) → F 19 (10 * n + 18)) ∧
      (Even n → 18 ≤ n → F 20 (11 * n)) ∧ (¬ Even n → 21 ≤ n → F 20 (11 * n - 3))

end

end MetaMathlibExt
