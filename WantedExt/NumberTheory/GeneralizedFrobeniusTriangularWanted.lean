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

/-- The three consecutive triangular numbers `(t_n, t_{n+1}, t_{n+2})`, `t_n = n(n+1)/2`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
def triangularTriple (n : ℕ) : Fin 3 → ℕ :=
  ![n * (n + 1) / 2, (n + 1) * (n + 2) / 2, (n + 2) * (n + 3) / 2]

/-- `triangularTriple 1 = (1, 3, 6)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
theorem triangularTriple_one : triangularTriple 1 = ![1, 3, 6] := by
  decide

/-- The bounds `N_s^{even} = 6⌊√(s+1)⌋ - 6` (for even `n`) and
`N_s^{odd} = 6⌊(√(4s+5) - 1)/2⌋ - 3` (for odd `n`), as integers.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
def triangularFrobeniusBound (n s : ℕ) : ℤ :=
  if Even n then 6 * (Nat.sqrt (s + 1) : ℤ) - 6 else 6 * ((Nat.sqrt (4 * s + 5) - 1) / 2 : ℕ) - 3

/-- `N_0^{even} = 0` and `N_0^{odd} = -3`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
theorem triangularFrobeniusBound_zero :
    triangularFrobeniusBound 0 0 = 0 ∧ triangularFrobeniusBound 1 0 = -3 := by
  decide +kernel

/-- The integers `x_s` of the paper's Definition 1 for `s = k(k+1) + i`, `0 ≤ i ≤ 2k+1`:
for even `n`, `x_s^{even} = i` (`i ≤ k`) or `i - k - 1` (`i > k`); for odd `n`, `x_s^{odd} = 2i`
(`i ≤ k`) or `2(i - k) - 1` (`i > k`).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusX (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then i else i - k - 1) else (if i ≤ k then 2 * i else 2 * (i - k) - 1)

/-- The integers `y_s` of the paper's Definition 1 for `s = k(k+1) + i`, `0 ≤ i ≤ 2k+1`:
for even `n`, `y_s^{even} = 2(k - i)` (`i ≤ k`) or `4k - 2i + 3` (`i > k`); for odd `n`,
`y_s^{odd} = k - i` (`i ≤ k`) or `2k - i + 1` (`i > k`).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusY (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then 2 * (k - i) else 4 * k + 3 - 2 * i)
  else (if i ≤ k then k - i else 2 * k + 1 - i)

/-- Table 2 entries at `s = 5 = 1·2 + 3`: `(x_5^{even}, y_5^{even}) = (1, 1)` and
`(x_5^{odd}, y_5^{odd}) = (3, 0)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1 and Table 2. -/
theorem triangularFrobeniusXY_five :
    (triangularFrobeniusX 0 1 3, triangularFrobeniusY 0 1 3) = (1, 1) ∧
      (triangularFrobeniusX 1 1 3, triangularFrobeniusY 1 1 3) = (3, 0) := by
  decide

/-- Beck and Kifer's reduction: for `A = (a₁, ℓa'₂, …, ℓa'_K)` of `K ≥ 2` positive integers with
`gcd(A) = 1` and `gcd(a'₂, …, a'_K) = 1` (so `ℓ = gcd(a₂, …, a_K)`), and `s ≥ 0`,
`g(A; s) = ℓ g(a₁, a'₂, …, a'_K; s) + a₁(ℓ - 1)`. The tail `(a'₂, …, a'_K)` is
`a' : Fin (k + 1) → ℕ`, so the paper's arity is `K = k + 2` (Lean `k = 0` is two generators).

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

/-- Splitting off the first generator: with `d₁ = gcd(t_{n+1}, t_{n+2})`, for `m ≥ 0`,
`d(m; t_n, t_{n+1}/d₁, t_{n+2}/d₁) = ∑_{j=0}^{⌊m/t_n⌋} d(m - j t_n; t_{n+1}/d₁, t_{n+2}/d₁)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 2 (`integers-2026-A63-lem-2`). -/
public theorem_wanted frobeniusRepCount_triangular_reduced_eq_sum (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] m =
      ∑ j ∈ Finset.range (m / t n + 1),
        frobeniusRepCount ![t (n + 1) / d₁, t (n + 2) / d₁] ((m : ℤ) - j * t n)

/-- For coprime positive `a, b`, `i, s ≥ 0`, a positive `c` divisible by `a` or by `b`, and
`j ∈ ℤ`: `d(g(a, b; s) + jc; a, b) = i` if and only if
`g(a, b; i - 1) < g(a, b; s) + jc ≤ g(a, b; i)`, with `g(a, b; -1) = -∞`. Here `G r` is
`g(a, b; r)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 3 (`integers-2026-A63-lem-3`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
public theorem_wanted frobeniusRepCount_pair_eq_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (G : ℕ → ℤ) (hG : ∀ r, IsGenFrobeniusNumber ![a, b] r (G r))
    (i s c : ℕ) (hc : 0 < c) (hdvd : a ∣ c ∨ b ∣ c) (j : ℤ) :
    frobeniusRepCount ![a, b] (G s + j * c) = i ↔
      (i = 0 ∨ G (i - 1) < G s + j * c) ∧ G s + j * c ≤ G i

/-- For coprime positive `a < b`, `s, k ≥ 0` and an integer `m > g(a, b; s) + ka`, every
`j ≥ 0` has `d(m - ja; a, b) ≥ d(g(a, b; s) + (k - j)a; a, b)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 4 (`integers-2026-A63-lem-4`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
public theorem_wanted frobeniusRepCount_pair_sub_ge (a b : ℕ) (ha : 0 < a) (hab' : a < b)
    (hab : Nat.Coprime a b) (s k : ℕ) (g : ℤ) (hg : IsGenFrobeniusNumber ![a, b] s g) (m : ℤ)
    (hm : g + k * a < m) (j : ℕ) :
    frobeniusRepCount ![a, b] (g + ((k : ℤ) - j) * a) ≤ frobeniusRepCount ![a, b] (m - j * a)

/-- For `s = k(k+1) + i` with `0 ≤ i ≤ 2k+1` and `n > N_s` (`N_s^{even}` or `N_s^{odd}` by the
parity of `n`): with `d₁ = gcd(t_{n+1}, t_{n+2})`,
`d(g(t_{n+1}/d₁, t_{n+2}/d₁; x_s) + y_s t_n; t_n, t_{n+1}/d₁, t_{n+2}/d₁) = s`.

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

/-- Main formula: for all `s ≥ 0`, with `r = ⌊√s⌋`, `δ_s = 1` if `s ≥ r² + r` and `0` otherwise,
`q_s = 2r + 2 + δ_s`, `c_s = s - r² - δ_s r`: (i) for even `n > 6⌊√(s+1)⌋ - 6`,
`g(t_n, t_{n+1}, t_{n+2}; s) = (n+1)(n+2)(q_s n + 6c_s)/4 - 1`; (ii) for odd
`n > 6⌊(√(4s+5) - 1)/2⌋ - 3`, `g(t_n, t_{n+1}, t_{n+2}; s) = (n+1)(n+2)(q_s n + 6c_s - 3δ_s)/4 - 1`.
Stated as `4(g + 1) = …`.

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

/-- Komatsu's conjecture, made precise: for `s, n ≥ 0` with `n > N_{s+1}` (by parity), writing
`g_s = g(t_n, t_{n+1}, t_{n+2}; s)` and `P = (n+1)(n+2)`: (i) if `s + 1` is neither `k²` nor
`k(k+1)` for any `k ≥ 1`, then `g_{s+1} - g_s = 6P/4`; (ii) for even `n` and `s + 1 ∈ {k², k(k+1)}`,
`g_{s+1} - g_s = (n - 6k + 6)P/4`; (iii) for odd `n`, `g_{s+1} - g_s = (n - 6k + 9)P/4` if
`s + 1 = k²` and `(n - 6k + 3)P/4` if `s + 1 = k(k+1)`. Stated as `4(g_{s+1} - g_s) = …`.

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

/-- Reformulation via Definition 1: if `s ∈ {0, 1, 2}` or `s` is neither `k²` nor `k(k+1)` for any
`k ≥ 1`, then for `n ≥ 2` with `n > N_s` (by parity), writing `s = k(k+1) + i`,
`0 ≤ i ≤ 2k+1`: `g(t_n, t_{n+1}, t_{n+2}; s) = (n+1)(n+2)((2x_s + y_s + 3)n + 6x_s)/4 - 1` for even
`n` and `(n+1)(n+2)((x_s + 2y_s + 3)n + 3(x_s - 1))/4 - 1` for odd `n`. Stated as `4(g + 1) = …`.

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

/-- For `s = k(k+1) + i` with `0 ≤ i ≤ 2k+1` and `n > N_s` (by parity), with
`d₁ = gcd(t_{n+1}, t_{n+2})`, `a = t_{n+1}/d₁`, `b = t_{n+2}/d₁`:
`g(t_n, a, b; s) = g(a, b; x_s) + y_s t_n = (x_s + 1)ab - b - a + y_s t_n`.

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

/-- Explicit values for `s = 11, …, 20`, each as `4(g + 1) = (n+1)(n+2) L`:
`s = 11`: `L = 8n + 12` (`n = 12` or `n ≥ 14`); `s = 12`: `9n` (even `n ≥ 14`), `9n - 3`
(odd `n ≥ 17`); `s = 13`: `9n + 6` (even `n ≥ 12`), `9n + 3` (odd `n ≥ 15`); `s = 14`: `9n + 12`
(even `n ≥ 12`), `9n + 9` (odd `n ≥ 15`); `s = 15`: `9n + 18` (even `n ≥ 18`), `9n + 15`
(odd `n ≥ 15`); `s = 16`: `10n` (`n = 17` or `n ≥ 19`); `s = 17`: `10n + 6` (`n = 15` or
`n ≥ 17`); `s = 18`: `10n + 12` (`n = 17` or `n ≥ 19`); `s = 19`: `10n + 18` (`n = 20` or
`n ≥ 22`); `s = 20`: `11n` (even `n ≥ 18`), `11n - 3` (odd `n ≥ 21`).

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
