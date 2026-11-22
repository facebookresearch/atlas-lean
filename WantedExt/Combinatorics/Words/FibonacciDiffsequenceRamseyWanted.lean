/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import MathlibExt.NumberTheory.LucasSequence
public import WantedExt.Combinatorics.AccessibleSetsWanted

/-!
# Ramsey-type theorems for Fibonacci numbers (statements)

Statement-only targets from William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci
Numbers and Other Sequences*, INTEGERS 25 (2025), Article A29.

Diffsequences, `r`-accessibility (`IsRAccessible`), `D`-progressions (`IsDAP`) and
`r`-largeness (`IsRLarge`, the paper's `r`-regularity of `AP_D`) are reused from
`WantedExt.Combinatorics.AccessibleSetsWanted`, as are the sets `positiveFibonacciSet` (`F`) and
`evenFibonacciSet` (`F_E`). `doa(D) ≤ r - 1` is stated as "not `s`-accessible for every `s ≥ r`",
and `Δ(D, k; r) = ∞` as the existence of an `r`-coloring of `ℤ⁺` with no monochromatic `k`-term
`D`-diffsequence (the form the proofs construct; equivalent to the finite version by
compactness).

The infinite Fibonacci word `F∞ = 010010100…` is MathlibExt's `fibInf` (zero-based, `false`
for the letter `0`); the paper indexes words from `1`, so the paper's `F∞(n)` is `fibInf (n - 1)`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **Halves of even Fibonacci numbers.** Let $F_m$ be the $m$-th Fibonacci number, with $F_0 = 0$
and $F_1 = 1$. The set of halves of the positive even Fibonacci numbers is
$G = \{F_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$; its elements are written
$g_n = F_{3n}/2$ for $n \ge 1$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
def halfEvenFibonacciSet : Set ℕ :=
  Set.range fun n => Nat.fib (3 * (n + 1)) / 2

/-- **$4$ is half of an even Fibonacci number.** Let $F_m$ be the $m$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$. The number $4$ belongs to the set
$G = \{F_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$ of halves of the positive even Fibonacci
numbers; indeed $4 = F_6/2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
theorem four_mem_halfEvenFibonacciSet : 4 ∈ halfEvenFibonacciSet :=
  ⟨1, by decide⟩

/-- **The Thue–Morse morphism $\mu$.** The morphism $\mu$ on binary words sends the letter $0$ to
the word $10$ and the letter $1$ to the word $01$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def thueMorseMorphism : Bool → List Bool
  | false => [true, false]
  | true => [false, true]

/-- **The morphism $\nu$.** The morphism $\nu$ is given on the letters $0$ and $1$ by
$\nu(0) = 1$ and $\nu(1) = 00$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def fibonacciNuMorphism : Bool → List Bool
  | false => [true]
  | true => [false, false]

/-- **Wesley's word $S$.** Let $\mu$ be the morphism of binary words with $0 \mapsto 10$ and
$1 \mapsto 01$, and let $f_0 = 0$, $f_1 = 01$, $f_2 = 010$, $\dots$ be the finite Fibonacci words.
The word $S$ is the infinite binary word, indexed from $0$, whose letter at index $n$ is the
letter at index $n$ of $\mu(f_{n+2})$.

Since each $f_k$ is a prefix of $f_{k+1}$, $S = \mu(F_\infty) = 1001101001\dots$, where
$F_\infty = 010010100\dots$ is the infinite Fibonacci word.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordS (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap thueMorseMorphism).getD n false

/-- **Wesley's word $T$.** Let $\nu$ be the morphism of binary words with $0 \mapsto 1$ and
$1 \mapsto 00$, and let $f_0 = 0$, $f_1 = 01$, $f_2 = 010$, $\dots$ be the finite Fibonacci words.
The word $T$ is the infinite binary word, indexed from $0$, whose letter at index $n$ is the
letter at index $n$ of $\nu(f_{n+2})$.

Since each $f_k$ is a prefix of $f_{k+1}$, $T = \nu(F_\infty) = 1001100100\dots$, where
$F_\infty = 010010100\dots$ is the infinite Fibonacci word.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordT (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap fibonacciNuMorphism).getD n false

/-- **The first ten letters of Wesley's words $S$ and $T$.** Indexing letters from $0$, the
letters of $S$ at indices $0, 1, \dots, 9$ are $1, 0, 0, 1, 1, 0, 1, 0, 0, 1$ and the letters of
$T$ at indices $0, 1, \dots, 9$ are $1, 0, 0, 1, 1, 0, 0, 1, 0, 0$; that is, $S$ begins with
$1001101001$ and $T$ begins with $1001100100$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
theorem wesleyWords_first_ten :
    (List.range 10).map wesleyWordS =
        [true, false, false, true, true, false, true, false, false, true] ∧
      (List.range 10).map wesleyWordT =
        [true, false, false, true, true, false, false, true, false, false] := by
  decide

/-- **Wesley's constants $c_{n,\varepsilon}$.** For a natural number $n$ and an integer
$\varepsilon$, the real number $c_{n,\varepsilon}$ is defined by the residue of $n$ modulo $4$:
if $n \equiv 0 \pmod 4$, then $c_{n,\varepsilon} = (4 + (2\sqrt5 - 5)\varepsilon)/10$;
if $n \equiv 1 \pmod 4$, then $c_{n,\varepsilon} = (11 - 4\sqrt5)/5$ when $\varepsilon = -4$ and
$c_{n,\varepsilon} = (4 + (4\sqrt5 - 5)\varepsilon)/20$ otherwise;
if $n \equiv 2 \pmod 4$, then $c_{n,\varepsilon} = (6 + (2\sqrt5 - 5)\varepsilon)/10$;
if $n \equiv 3 \pmod 4$, then $c_{n,\varepsilon} = (9 - 4\sqrt5)/5$ when $\varepsilon = -4$ and
$c_{n,\varepsilon} = (8 + (2\sqrt5 - 5)\varepsilon)/10$ otherwise.

Lemma 5 uses these constants only for $\varepsilon \in \{-4, 0, 4\}$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
noncomputable def wesleyFractionalConstant (n : ℕ) (ε : ℤ) : ℝ :=
  if n % 4 = 0 then (4 + (2 * √5 - 5) * ε) / 10
  else if n % 4 = 1 then (if ε = -4 then (11 - 4 * √5) / 5 else (4 + (4 * √5 - 5) * ε) / 20)
  else if n % 4 = 2 then (6 + (2 * √5 - 5) * ε) / 10
  else (if ε = -4 then (9 - 4 * √5) / 5 else (8 + (2 * √5 - 5) * ε) / 10)

/-- **Wesley's constant $c_{n,0}$ for $n \equiv 0 \pmod 4$.** For every natural number $n$ with
$n \equiv 0 \pmod 4$, Wesley's constant satisfies $c_{n,0} = 2/5$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
theorem wesleyFractionalConstant_zero_of_mod_four_eq_zero {n : ℕ} (hn : n % 4 = 0) :
    wesleyFractionalConstant n 0 = 2 / 5 := by
  norm_num [wesleyFractionalConstant, hn]

/-! ## Statements -/

/-- **The Fibonacci numbers have degree of accessibility at most $3$.** The positive Fibonacci set
$\{1, 2, 3, 5, 8, \dots\}$ is not $r$-accessible for any natural number $r \ge 4$. Moreover, some
coloring of the positive integers with four colors admits no monochromatic $4$-term
diffsequence with differences in the positive Fibonacci set: there are no positive integers
$x_0, x_1, x_2, x_3$ of one color such that $x_{i+1} - x_i$ is a positive Fibonacci number for
$i = 0, 1, 2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Theorem 1 (`integers-2025-A29-thm-1`). -/
public theorem_wanted fibonacciSet_degreeOfAccessibility_le_three :
    (∀ r, 4 ≤ r → ¬ IsRAccessible r positiveFibonacciSet) ∧
    ∃ c : ℕ+ → Fin 4, ¬ ∃ x : Fin 4 → ℕ+,
      IsMonochromatic c x ∧ IsDDiffSequence positiveFibonacciSet (fun i => ((x i : ℕ) : ℤ))

/-- **Arithmetic progressions with Fibonacci gaps are not $2$-regular.** There is a coloring of the
positive integers with two colors that admits no monochromatic $5$-term arithmetic progression
with gap in the positive Fibonacci set $\{1, 2, 3, 5, 8, \dots\}$, that is, no positive integers
$x_0, \dots, x_4$ of one color with $x_i = a + i d$ for all $i < 5$, for a positive integer $a$ and
a positive Fibonacci number $d$. Moreover, the positive Fibonacci set is $1$-large, and it is not
$r$-large for any natural number $r \ge 2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Theorem 2 (`integers-2025-A29-thm-2`). -/
public theorem_wanted fibonacci_gap_progressions_not_two_regular :
    (∃ c : ℕ+ → Fin 2, ¬ ∃ x : Fin 5 → ℕ+,
      IsMonochromatic c x ∧ IsDAP positiveFibonacciSet 5 x) ∧
    IsRLarge 1 positiveFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRLarge r positiveFibonacciSet

/-- **Fibonacci numbers divided by the golden ratio.** Let $F_n$ be the $n$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$, and let $\varphi = (1 + \sqrt{5})/2$ be the golden ratio. For every
natural number $n \ge 2$,
$$\frac{F_n}{\varphi} - F_{n-1} = (-1)^{n+1} \varphi^{-n}.$$

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 1 (`integers-2025-A29-cor-1`). -/
public theorem_wanted fib_div_goldenRatio_sub_fib (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℝ) / Real.goldenRatio - Nat.fib (n - 1) =
      (-1) ^ (n + 1) * Real.goldenRatio ^ (-(n : ℤ))

/-- **Beatty-sequence descriptions of the words $F_\infty$, $S$ and $T$.** Let
$\varphi = (1 + \sqrt{5})/2$ be the golden ratio and $F_\infty = 010010100\cdots$ the infinite
Fibonacci word. Let $S = \mu(F_\infty)$ be its image under the morphism $\mu$ with $\mu(0) = 10$
and $\mu(1) = 01$, and $T = \nu(F_\infty)$ its image under the morphism $\nu$ with $\nu(0) = 1$
and $\nu(1) = 00$. For a word $W$ and an integer $n \ge 1$, write $W(n)$ for the $n$-th letter of
$W$, counting from $1$. Then:
(i) for every integer $n \ge 1$, $F_\infty(n) = 0$ if and only if $n = \lfloor m\varphi \rfloor$
for some integer $m$;
(ii) for every integer $n$, positive or not, if $n \ne \lfloor m\varphi \rfloor$ for every
integer $m$, then $n + 1 = \lfloor m'\varphi \rfloor$ and $n - 1 = \lfloor m''\varphi \rfloor$ for
some integers $m'$ and $m''$;
(iii) for every integer $n \ge 1$, $S(n) = 0$ if and only if either $n$ is even and
$n/2 = \lfloor m\varphi \rfloor$ for some integer $m$, or $n$ is odd and
$(n+1)/2 \ne \lfloor m\varphi \rfloor$ for every integer $m$;
(iv) for every integer $n \ge 1$, $T(n) = 1$ if and only if $n = 2\lfloor m\varphi \rfloor - m$
for some integer $m$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 2 (`integers-2025-A29-lem-2`). -/
public theorem_wanted fibonacciWord_beatty_properties :
    (∀ n : ℕ, 1 ≤ n → (fibInf (n - 1) = false ↔ ∃ m : ℤ, (n : ℤ) = ⌊m * Real.goldenRatio⌋)) ∧
    (∀ n : ℤ, (∀ m : ℤ, n ≠ ⌊m * Real.goldenRatio⌋) →
      (∃ m' : ℤ, n + 1 = ⌊m' * Real.goldenRatio⌋) ∧ ∃ m'' : ℤ, n - 1 = ⌊m'' * Real.goldenRatio⌋) ∧
    (∀ n : ℕ, 1 ≤ n → (wesleyWordS (n - 1) = false ↔
      (Even n ∧ ∃ m : ℤ, ((n / 2 : ℕ) : ℤ) = ⌊m * Real.goldenRatio⌋) ∨
        (Odd n ∧ ∀ m : ℤ, (((n + 1) / 2 : ℕ) : ℤ) ≠ ⌊m * Real.goldenRatio⌋))) ∧
    ∀ n : ℕ, 1 ≤ n → (wesleyWordT (n - 1) = true ↔
      ∃ m : ℤ, (n : ℤ) = 2 * ⌊m * Real.goldenRatio⌋ - m)

/-- **Halved even Fibonacci numbers and $4$-accessibility of the Fibonacci numbers.** Write $f_n$
for the $n$-th Fibonacci number ($f_0 = 0$, $f_1 = 1$). Let $F = \{1, 2, 3, 5, 8, \dots\}$ be the
set of positive Fibonacci numbers and $G = \{f_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$ the set
of halves of the even Fibonacci numbers. If $G$ is not $2$-accessible, then $F$ is not
$4$-accessible.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 3 (`integers-2025-A29-lem-3`). -/
public theorem_wanted not_accessible_four_of_halfEvenFibonacci
    (h : ¬ IsRAccessible 2 halfEvenFibonacciSet) :
    ¬ IsRAccessible 4 positiveFibonacciSet

/-- **Differences of fractional parts of multiples of the golden ratio.** Let $F_m$ be the $m$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the golden
ratio, and write $\{y\} = y - \lfloor y \rfloor$ for the fractional part. Let $i \ge 1$ be a
natural number, put $g_i = F_{3i}/2$ (an integer, since $F_{3i}$ is even), and let
$x_1, x_2, m_1, m_2$ be integers. Then:
(i) if $g_i$ is even, $2(x_2 - x_1) = g_i$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} \le (\varphi^{-3i+1} - \varphi)/4 < -0.38$;
(ii) if $g_i$ is odd, $2(x_2 - x_1) = g_i + 1$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 + 1 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (3\varphi - 6)/4 < -0.28$;
(iii) if $g_i$ is odd, $i > 1$, $2(x_2 - x_1) = g_i - 1$, $x_1 + 1 = \lfloor m_1\varphi \rfloor$
and $x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (-5\varphi + 6)/4 < -0.52$.

The paper states (i) with a strict inequality, but equality occurs: $i = 2$, $m_1 = 1$, $m_2 = 2$,
$x_1 = 1$, $x_2 = 3$ give $\{2\varphi\} - \{\varphi\} = (\varphi^{-5} - \varphi)/4$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 4 (`integers-2025-A29-lem-4`). -/
public theorem_wanted fract_goldenRatio_differences (i : ℕ) (hi : 1 ≤ i) (x₁ x₂ m₁ m₂ : ℤ) :
    (Even (Nat.fib (3 * i) / 2) → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) →
      x₁ = ⌊m₁ * Real.goldenRatio⌋ → x₂ = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) ≤
        (Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - Real.goldenRatio) / 4 ∧
      (Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - Real.goldenRatio) / 4 < -0.38) ∧
    (Odd (Nat.fib (3 * i) / 2) → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) + 1 →
      x₁ = ⌊m₁ * Real.goldenRatio⌋ → x₂ + 1 = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) <
        (3 * Real.goldenRatio - 6) / 4 ∧ (3 * Real.goldenRatio - 6) / 4 < -0.28) ∧
    (Odd (Nat.fib (3 * i) / 2) → 1 < i → 2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) - 1 →
      x₁ + 1 = ⌊m₁ * Real.goldenRatio⌋ → x₂ = ⌊m₂ * Real.goldenRatio⌋ →
      Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) <
        (-5 * Real.goldenRatio + 6) / 4 ∧ (-5 * Real.goldenRatio + 6) / 4 < -0.52)

/-- **Fractional parts of shifted Fibonacci numbers divided by $\sqrt{5}$.** Let $F_n$ be the
$n$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the
golden ratio, so that $2\varphi - 1 = \sqrt{5}$, and write $\{y\} = y - \lfloor y \rfloor$ for the
fractional part. Let $n \ge 13$ be a natural number and $\varepsilon \in \{-4, 0, 4\}$, let
$c_{n,\varepsilon}$ be Wesley's constant, which depends on $n \bmod 4$ and $\varepsilon$, and put
$y = (F_n + \varepsilon)/(2\varphi - 1)$. Then
(i) $\{y\} = -2(-\varphi)^{-n}/5 + c_{n,\varepsilon}$, and
(ii) $\lfloor y \rfloor$ is even if and only if $\varepsilon = 0$ and
$n \equiv 0, 1, 2, 3, 5, 10 \pmod{12}$, or $\varepsilon = 4$ and
$n \equiv 0, 2, 3, 9, 10 \pmod{12}$, or $\varepsilon = -4$ and
$n \equiv 0, 1, 2, 5, 7, 10, 11 \pmod{12}$.

The paper prints $+2(-\varphi)^{-n}/5$ in (i). The sign $-$ is the one its proof derives
(Equation (1)); the printed sign fails for every $n \ge 13$, since this term is nonzero.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (`integers-2025-A29-lem-5`). -/
public theorem_wanted fract_fib_add_div_sqrt_five (n : ℕ) (hn : 13 ≤ n) (ε : ℤ)
    (hε : ε = -4 ∨ ε = 0 ∨ ε = 4) :
    Int.fract (((Nat.fib n : ℝ) + ε) / (2 * Real.goldenRatio - 1)) =
        -(2 * (-Real.goldenRatio) ^ (-(n : ℤ)) / 5) + wesleyFractionalConstant n ε ∧
    (Even ⌊((Nat.fib n : ℝ) + ε) / (2 * Real.goldenRatio - 1)⌋ ↔
      (ε = 0 ∧ n % 12 ∈ ({0, 1, 2, 3, 5, 10} : Finset ℕ)) ∨
      (ε = 4 ∧ n % 12 ∈ ({0, 2, 3, 9, 10} : Finset ℕ)) ∨
      (ε = -4 ∧ n % 12 ∈ ({0, 1, 2, 5, 7, 10, 11} : Finset ℕ)))

/-- **The Lucas numbers are not $4$-accessible.** Let $L = \{2, 1, 3, 4, 7, \dots\}$ be the set of
Lucas numbers $L_0 = 2$, $L_1 = 1$, $L_{n+2} = L_{n+1} + L_n$. There is a coloring of the positive
integers with the colors $0, 1, 2, 3$ for which no sequence $x_0, x_1, x_2$ of positive integers is
both monochromatic and an $L$-diffsequence; and $L$ is not $r$-accessible for any $r \ge 4$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 6 (`integers-2025-A29-lem-6`). -/
public theorem_wanted lucasSet_not_four_accessible :
    (∃ c : ℕ+ → Fin 4, ¬ ∃ x : Fin 3 → ℕ+,
      IsMonochromatic c x ∧ IsDDiffSequence (Set.range lucasNumber) (fun i => ((x i : ℕ) : ℤ))) ∧
    ∀ r, 4 ≤ r → ¬ IsRAccessible r (Set.range lucasNumber)

/-- **The even Fibonacci numbers have degree of accessibility $1$.** The even Fibonacci set
$\{2, 8, 34, \dots\}$ is $1$-accessible, and it is not $r$-accessible for any natural number
$r \ge 2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 2 (`integers-2025-A29-cor-2`). -/
public theorem_wanted evenFibonacciSet_degreeOfAccessibility_eq_one :
    IsRAccessible 1 evenFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRAccessible r evenFibonacciSet

end

end MetaMathlibExt
