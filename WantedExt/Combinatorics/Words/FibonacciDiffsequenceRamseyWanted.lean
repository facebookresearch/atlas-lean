/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.EvenFibonacciAccessibility
public import MathlibExt.Combinatorics.HalfEvenFibonacciSet
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import MathlibExt.NumberTheory.FibonacciDivGoldenRatio
public import MathlibExt.NumberTheory.FractGoldenRatioDifferences
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.WesleyFractionalConstant
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

end

end MetaMathlibExt
