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

/-- The set `G = {1, 4, 17, 72, …} = {f / 2 : f ∈ F} ∩ ℤ` of halves of even Fibonacci numbers,
`g_n = f_{3n} / 2` for `n ≥ 1`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
def halfEvenFibonacciSet : Set ℕ :=
  Set.range fun n => Nat.fib (3 * (n + 1)) / 2

/-- `g₂ = f₆ / 2 = 4 ∈ G`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
theorem four_mem_halfEvenFibonacciSet : 4 ∈ halfEvenFibonacciSet :=
  ⟨1, by decide⟩

/-- The Thue–Morse morphism `μ : 0 ↦ 10, 1 ↦ 01` on letters (`false` is `0`).

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def thueMorseMorphism : Bool → List Bool
  | false => [true, false]
  | true => [false, true]

/-- The morphism `ν : 0 ↦ 1, 1 ↦ 00` on letters (`false` is `0`).

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def fibonacciNuMorphism : Bool → List Bool
  | false => [true]
  | true => [false, false]

/-- The word `S = μ(F∞) = 1001101001…`, zero-based: letter `n` is read from the image of a
prefix of `F∞` long enough to contain it.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordS (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap thueMorseMorphism).getD n false

/-- The word `T = ν(F∞) = 1001100100…`, zero-based.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordT (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap fibonacciNuMorphism).getD n false

/-- The first ten letters: `S = 1001101001…` and `T = 1001100100…`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
theorem wesleyWords_first_ten :
    (List.range 10).map wesleyWordS =
        [true, false, false, true, true, false, true, false, false, true] ∧
      (List.range 10).map wesleyWordT =
        [true, false, false, true, true, false, false, true, false, false] := by
  decide

/-- The constant `c_{n,ε}` of Lemma 5, by the residue of `n` modulo `4` and `ε ∈ {-4, 0, 4}`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
noncomputable def wesleyFractionalConstant (n : ℕ) (ε : ℤ) : ℝ :=
  if n % 4 = 0 then (4 + (2 * √5 - 5) * ε) / 10
  else if n % 4 = 1 then (if ε = -4 then (11 - 4 * √5) / 5 else (4 + (4 * √5 - 5) * ε) / 20)
  else if n % 4 = 2 then (6 + (2 * √5 - 5) * ε) / 10
  else (if ε = -4 then (9 - 4 * √5) / 5 else (8 + (2 * √5 - 5) * ε) / 10)

/-- `c_{n,0} = 2/5` for `n ≡ 0 (mod 4)`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
theorem wesleyFractionalConstant_zero_of_mod_four_eq_zero {n : ℕ} (hn : n % 4 = 0) :
    wesleyFractionalConstant n 0 = 2 / 5 := by
  norm_num [wesleyFractionalConstant, hn]

/-! ## Statements -/

/-- Degree of accessibility of the Fibonacci numbers is at most three: `F` is not
`r`-accessible for any `r ≥ 4`; in particular some `4`-coloring of `ℤ⁺` has no monochromatic
`4`-term `F`-diffsequence.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Theorem 1 (`integers-2025-A29-thm-1`). -/
public theorem_wanted fibonacciSet_degreeOfAccessibility_le_three :
    (∀ r, 4 ≤ r → ¬ IsRAccessible r positiveFibonacciSet) ∧
    ∃ c : ℕ+ → Fin 4, ¬ ∃ x : Fin 4 → ℕ+,
      IsMonochromatic c x ∧ IsDDiffSequence positiveFibonacciSet (fun i => ((x i : ℕ) : ℤ))

/-- The family of arithmetic progressions with common difference in `F` is not `2`-regular:
some `2`-coloring of `ℤ⁺` has no monochromatic `5`-term progression with difference in `F`;
hence `dor(AP_F) = 1`: `F` is `1`-large and not `r`-large for `r ≥ 2` (`IsRLarge`, the
paper's `r`-regularity of `AP_F`).

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Theorem 2 (`integers-2025-A29-thm-2`). -/
public theorem_wanted fibonacci_gap_progressions_not_two_regular :
    (∃ c : ℕ+ → Fin 2, ¬ ∃ x : Fin 5 → ℕ+,
      IsMonochromatic c x ∧ IsDAP positiveFibonacciSet 5 x) ∧
    IsRLarge 1 positiveFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRLarge r positiveFibonacciSet

/-- For `n ≥ 2`, `f_n / φ - f_{n-1} = (-1)^{n+1} φ^{-n}`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 1 (`integers-2025-A29-cor-1`). -/
public theorem_wanted fib_div_goldenRatio_sub_fib (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℝ) / Real.goldenRatio - Nat.fib (n - 1) =
      (-1) ^ (n + 1) * Real.goldenRatio ^ (-(n : ℤ))

/-- Properties of `F∞`, `S` and `T` (positions `n ≥ 1` as in the paper, so letter `n` is index
`n - 1`): (i) `F∞(n) = 0` iff `n = ⌊mφ⌋` for some integer `m`; (ii) if `n ≠ ⌊mφ⌋` for every
`m`, then `n + 1` and `n - 1` are of that form; (iii) `S(n) = 0` iff `n` is even with
`n/2 = ⌊mφ⌋` for some `m`, or `n` is odd with `(n+1)/2 ≠ ⌊mφ⌋` for every `m` (the paper's
other two cases are `S(n) = 1`); (iv) `T(n) = 1` iff `n = 2⌊mφ⌋ - m` for some integer `m`.

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

/-- If `G` is not `2`-accessible (`Δ(G, k; 2) = ∞` for some `k`), then `F` is not
`4`-accessible.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 3 (`integers-2025-A29-lem-3`). -/
public theorem_wanted not_accessible_four_of_halfEvenFibonacci
    (h : ¬ IsRAccessible 2 halfEvenFibonacciSet) :
    ¬ IsRAccessible 4 positiveFibonacciSet

/-- Fractional-part bounds, with `g_i = f_{3i} / 2` (`i ≥ 1`) and integers `x₁, x₂, m₁, m₂`:
(i) if `g_i` is even, `x₂ - x₁ = g_i / 2`, `x₁ = ⌊m₁φ⌋`, `x₂ = ⌊m₂φ⌋`, then
`{m₂φ} - {m₁φ} ≤ (φ^{-3i+1} - φ)/4 < -0.38`; (ii) if `g_i` is odd, `x₂ - x₁ = (g_i + 1)/2`,
`x₁ = ⌊m₁φ⌋`, `x₂ + 1 = ⌊m₂φ⌋`, then `{m₂φ} - {m₁φ} < (3φ - 6)/4 < -0.28`; (iii) if `g_i` is
odd, `i > 1`, `x₂ - x₁ = (g_i - 1)/2`, `x₁ + 1 = ⌊m₁φ⌋`, `x₂ = ⌊m₂φ⌋`, then
`{m₂φ} - {m₁φ} < (-5φ + 6)/4 < -0.52`. Halved gaps are written as `2(x₂ - x₁) = …`.
CORRECTED READING of (i): `≤` for the printed `<`. The proof derives the equality
`{m₂φ} - {m₁φ} = (φ^{-3i+1} - φ)/4`; e.g. `m₁ = 1`, `m₂ = 2` (`x₁ = 1`, `x₂ = 3`, `i = 2`)
gives `{2φ} - {φ} = (φ^{-5} - φ)/4`.

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

/-- For `ε ∈ {-4, 0, 4}` and `n ≥ 13`: (i) `{(f_n + ε)/(2φ - 1)} = -2(-φ)^{-n}/5 + c_{n,ε}`;
(ii) `⌊(f_n + ε)/(2φ - 1)⌋` is even iff `ε = 0` and `n ≡ 0, 1, 2, 3, 5, 10 (mod 12)`, or
`ε = 4` and `n ≡ 0, 2, 3, 9, 10 (mod 12)`, or `ε = -4` and `n ≡ 0, 1, 2, 5, 7, 10, 11 (mod 12)`.
CORRECTED READING of (i): the sign of `2(-φ)^{-n}/5` is `-`, as in the proof's
Equation (1) (`{(f_n + ε)/(2φ - 1)} = -2(-φ)^{-n}/5 + {r/5 + ε/√5}`); the printed `+` fails for
every `n ≥ 13` and `ε` (checked to 50 digits for `13 ≤ n < 120`), since the term is nonzero.

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

/-- `Δ(L, 3; 4) = ∞` for the Lucas numbers `L = {2, 1, 3, 4, 7, …}` (some `4`-coloring of `ℤ⁺`
has no monochromatic `3`-term `L`-diffsequence); in particular `L` is not
`r`-accessible for any `r ≥ 4`, i.e. `doa(L) ≤ 3`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 6 (`integers-2025-A29-lem-6`). -/
public theorem_wanted lucasSet_not_four_accessible :
    (∃ c : ℕ+ → Fin 4, ¬ ∃ x : Fin 3 → ℕ+,
      IsMonochromatic c x ∧ IsDDiffSequence (Set.range lucasNumber) (fun i => ((x i : ℕ) : ℤ))) ∧
    ∀ r, 4 ≤ r → ¬ IsRAccessible r (Set.range lucasNumber)

/-- The even Fibonacci numbers have degree of accessibility `1`: `F_E` is `1`-accessible and
not `r`-accessible for any `r ≥ 2`.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 2 (`integers-2025-A29-cor-2`). -/
public theorem_wanted evenFibonacciSet_degreeOfAccessibility_eq_one :
    IsRAccessible 1 evenFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRAccessible r evenFibonacciSet

end

end MetaMathlibExt
