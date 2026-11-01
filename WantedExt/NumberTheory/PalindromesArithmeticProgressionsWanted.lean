/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Palindromes in arithmetic progressions (statements)

Statement-only targets from Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon
Napp Phunphayap and Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in
Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8 (TeX
source read).

Conventions. For `m ≥ 1` with base-`b` expansion `m = (a_k ⋯ a_0)_b`, the digit `a_i` is
`(Nat.digits b m).getD i 0` (Mathlib's little-endian digit list) and `k` is
`(Nat.digits b m).length - 1`. A positive `n` is a `b`-adic palindrome when
`(Nat.digits b n).Palindrome`. `A_b(m, q, r)` is `palindromeAPCount b m q r` and
`A_b(m) = A_b(m, 1, 0)`; `C_b(m)` is `palindromicHalfCopy b m`; `N_b(k, q, r, x, y)` is
`digitSumCongruenceCount b k q r x y`. Iverson brackets `[P]` are written `if P then 1 else 0`.
-/

namespace MetaMathlibExt

open Int

@[expose] public section

/-- Floor-function facts (iii) and (v) of Lemma 6: for real `x`, `⌊x⌋ + ⌊-x⌋` is `0` when `x`
is an integer and `-1` otherwise; and for real `x`, `y`, `⌊x + y⌋ = ⌊x⌋ + ⌊y⌋` when
`{x} + {y} < 1` and `⌊x⌋ + ⌊y⌋ + 1` otherwise, with `{x} = Int.fract x`. Parts (i), (ii),
(iv), (vi) of the lemma are existing Mathlib lemmas and are not restated.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Lemma 6
(`jis-2024-24.4.8-lem-6`). -/
public theorem_wanted floor_add_floor_neg_and_floor_add_eq :
    (∀ x : ℝ, (∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = 0) ∧
      (∀ x : ℝ, (¬ ∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = -1) ∧
      ∀ x y : ℝ, ⌊x + y⌋ =
        if fract x + fract y < 1 then ⌊x⌋ + ⌊y⌋ else ⌊x⌋ + ⌊y⌋ + 1

/-- `A_b(m, q, r)`: the number of `b`-adic palindromes `n` with `1 ≤ n ≤ m` and
`n ≡ r (mod q)`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public def palindromeAPCount (b m q r : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter fun n => (Nat.digits b n).Palindrome ∧ n ≡ r [MOD q]).card

/-- `C_b(m)`: the `b`-adic palindrome with the same number of digits as `m` whose upper half
digits are those of `m`, i.e. `∑_{j ≤ k} a_{max(j, k - j)} b ^ j`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1. -/
public def palindromicHalfCopy (b m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (Nat.digits b m).length,
    (Nat.digits b m).getD (max j ((Nat.digits b m).length - 1 - j)) 0 * b ^ j

/-- `N_b(k, q, r, x, y)`: the number of integer solutions of `x_1 + ⋯ + x_k ≡ r (mod q)` with
`x ≤ x_1 < y` and `0 ≤ x_i < b` for `2 ≤ i ≤ k` (meant for `k ≥ 1`); `x, y` are taken natural.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public def digitSumCongruenceCount (b k q : ℕ) (r : ℤ) (x y : ℕ) : ℕ :=
  ((Finset.Ico x y ×ˢ Fintype.piFinset fun _ : Fin (k - 1) => Finset.range b).filter
    fun p => ((p.1 + ∑ i, p.2 i : ℕ) : ℤ) ≡ r [ZMOD q]).card

/-- Small values: `A_10(100, 1, 0) = 18` (the palindromes `1, …, 9, 11, …, 99`) and
`A_2(9, 2, 1) = 5` (`1, 3, 5 = (101)_2, 7 = (111)_2, 9 = (1001)_2`).

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public theorem palindromeAPCount_small :
    palindromeAPCount 10 100 1 0 = 18 ∧ palindromeAPCount 2 9 2 1 = 5 := by
  decide +kernel

/-- The source's example: for `m = (134240)_5 = (12702)_8 = 5570`, `C_5(m) = (134431)_5 = 5616`
and `C_8(m) = (12721)_8 = 5585`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1 (example). -/
public theorem palindromicHalfCopy_example :
    palindromicHalfCopy 5 5570 = 5616 ∧ palindromicHalfCopy 8 5570 = 5585 := by
  decide +kernel

/-- Small value: `N_3(2, 2, 0, 0, 3) = 5` (pairs `(x_1, x_2) ∈ [0, 3)²` with even sum).

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public theorem digitSumCongruenceCount_small : digitSumCongruenceCount 3 2 2 0 0 3 = 5 := by
  decide +kernel

/-- Lemma 5: for integers `a, b, k, q ≥ 1` with `b ≡ 1 (mod q)` and any integer `r`,
(i) `N_b(k, q, r) = (b^k - 1)/q + [r ≡ 0 (mod q)]`;
(ii) `N_b(k, q, r, 1, b) = (b^k - b^{k-1})/q`;
(iii) `N_b(k, q, r, 0, a) = a(b^{k-1} - 1)/q + ⌊a/q⌋ + [r mod q < a mod q]`;
(iv) `N_b(k, q, r, 1, a) = (a - 1)(b^{k-1} - 1)/q + ⌊a/q⌋ + [r mod q < a mod q] - [r ≡ 0 (mod q)]`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Lemma 5. -/
public theorem_wanted digitSumCongruenceCount_of_modEq_one {a b k q : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hk : 1 ≤ k) (hq : 1 ≤ q) (hbq : b ≡ 1 [MOD q]) (r : ℤ) :
    (digitSumCongruenceCount b k q r 0 b : ℚ) =
        ((b : ℚ) ^ k - 1) / q + (if r ≡ 0 [ZMOD q] then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 b : ℚ) = ((b : ℚ) ^ k - (b : ℚ) ^ (k - 1)) / q ∧
      (digitSumCongruenceCount b k q r 0 a : ℚ) =
        (a : ℚ) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 a : ℚ) =
        ((a : ℚ) - 1) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) - (if r ≡ 0 [ZMOD q] then 1 else 0)

/-- Theorem 7: let `b ≥ 2`, `m, q ≥ 1` with `q ∣ b`, `m = (a_k ⋯ a_0)_b` and
`α = (b^{⌈k/2⌉} + b^{⌊k/2⌋} - 2)/(b - 1)`. Then
`A_b(m, q, 0) = (b/q - 1)α + ⌊(a_k - 1)/q⌋ b^{⌊k/2⌋} + [a_k ≡ 0 (mod q)](S + [m ≥ C_b(m)])`
and, for `r mod q > 0`,
`A_b(m, q, r) = bα/q + ⌈(a_k - (r mod q))/q⌉ b^{⌊k/2⌋} + [a_k ≡ r (mod q)](S + [m ≥ C_b(m)])`,
where `S = ∑_{1 ≤ i ≤ ⌊k/2⌋} a_{k-i} b^{⌊k/2⌋-i}`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 7. -/
public theorem_wanted palindromeAPCount_of_dvd_base {b m q : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hqb : q ∣ b) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m q 0 : ℚ) =
        ((b : ℚ) / q - 1) * α + (((a k - 1) / q : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
          (if a k ≡ 0 [MOD q] then 1 else 0) * (S + δ) ∧
      ∀ r : ℕ, 0 < r % q →
        (palindromeAPCount b m q r : ℚ) =
          (b : ℚ) * α / q + (⌈((a k : ℚ) - ((r % q : ℕ) : ℚ)) / q⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
            (if a k ≡ r [MOD q] then 1 else 0) * (S + δ)

/-- Corollary 8: for `b ≥ 2`, `m ≥ 1`, `m = (a_k ⋯ a_0)_b`,
`A_b(m) = b^{⌈k/2⌉} + ∑_{0 ≤ i ≤ ⌊k/2⌋} a_{k-i} b^{⌊k/2⌋-i} + [m ≥ C_b(m)] - 2`; and for even `b`,
with `α` as in Theorem 7,
`A_b(m, 2, 0) = (b/2 - 1)α + ⌊(a_k - 1)/2⌋ b^{⌊k/2⌋} + [a_k even](S + [m ≥ C_b(m)])` and
`A_b(m, 2, 1) = bα/2 + ⌈(a_k - 1)/2⌉ b^{⌊k/2⌋} + [a_k odd](S + [m ≥ C_b(m)])`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 8. -/
public theorem_wanted palindromeCount_closed_form {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m 1 0 : ℚ) =
        (b : ℚ) ^ ((k + 1) / 2) +
          ∑ i ∈ Finset.range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) + δ - 2 ∧
      (Even b →
        (palindromeAPCount b m 2 0 : ℚ) =
            ((b : ℚ) / 2 - 1) * α + (((a k - 1) / 2 : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Even (a k) then 1 else 0) * (S + δ) ∧
          (palindromeAPCount b m 2 1 : ℚ) =
            (b : ℚ) * α / 2 + (⌈((a k : ℚ) - 1) / 2⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Odd (a k) then 1 else 0) * (S + δ))

/-- Theorem 9: let `b ≥ 2`, `m, q ≥ 1`, `0 ≤ r < q`, `b ≡ 1 (mod q)`, `m = (a_k ⋯ a_0)_b`, and
for `j ≤ ⌊k/2⌋` let `r_j`, `s_j`, `m₁*`, `m₂*`, `m₃*`, `δ(m)` be as in the source (`rr`, `ss`,
`m₁`, `m₂`, `m₃`, `δ` below; `r/2` is used only for even `r`, written with natural division).
(i) For odd `q`, `A_b(m, q, r) = (b^{⌊(k+1)/2⌋} - 1)/q + ∑_{j ≤ ⌊k/2⌋} (⌊a_{k-j} b^{⌊k/2⌋-j}/q⌋ +
[r_j < s_j]) - [r = 0] + δ(m)`.
(ii) For even `q`, `A_b(m, q, r)` is `(b - 1)b^{(k-1)/2}/q` if `k, r` are odd;
`((b + 1)b^{(k-1)/2} - 2)/q + m₁* - [r = 0] + δ(m)` if `k` is odd and `r` even;
`⌊a_{k/2}/q⌋ + m₂* + [r_{k/2} < s_{k/2}] + δ(m)` if `k` is even and `r` odd; and
`2(b^{k/2} - 1)/q + ⌊a_{k/2}/q⌋ + m₃* - [r = 0] + [r_{k/2} < s_{k/2}] + δ(m)` if `k, r` are even.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 9. -/
public theorem_wanted palindromeAPCount_of_modEq_one {b m q r : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let rr : ℕ → ℤ := fun j =>
      if 2 * j = k then ((r : ℤ) - 2 * ∑ i ∈ Finset.range (k / 2), (a (k - i) : ℤ)) % q
      else if Even q then (((r / 2 : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % (q / 2 : ℕ)
      else ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % q
    let ss : ℕ → ℤ := fun j =>
      if Even q ∧ 2 * j ≠ k then ((a (k - j) % (q / 2) : ℕ) : ℤ) else ((a (k - j) % q : ℕ) : ℤ)
    let δ : ℚ :=
      (if palindromicHalfCopy b m ≤ m then 1 else 0) * (if rr (k / 2) = ss (k / 2) then 1 else 0)
    let m₁ : ℚ := ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      ((2 * (a (k - j) : ℚ) * (b : ℚ) ^ ((k - 1) / 2 - j) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    let m₂ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (a (k - j) : ℚ) * ((b : ℚ) - 1) * (b : ℚ) ^ (k / 2 - j - 1) / q
    let m₃ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (((a (k - j) : ℚ) * ((b : ℚ) + 1) * (b : ℚ) ^ (k / 2 - j - 1) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    (Odd q →
      (palindromeAPCount b m q r : ℚ) =
        ((b : ℚ) ^ ((k + 1) / 2) - 1) / q +
          ∑ j ∈ Finset.range (k / 2 + 1),
            ((((a (k - j) * b ^ (k / 2 - j)) / q : ℕ) : ℚ) + (if rr j < ss j then 1 else 0)) -
          (if r = 0 then 1 else 0) + δ) ∧
    (Even q →
      (palindromeAPCount b m q r : ℚ) =
        if Odd k ∧ Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else if Odd k then
          (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) - 2) / q + m₁ - (if r = 0 then 1 else 0) + δ
        else if Odd r then
          ((a (k / 2) / q : ℕ) : ℚ) + m₂ + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ
        else
          2 * ((b : ℚ) ^ (k / 2) - 1) / q + ((a (k / 2) / q : ℕ) : ℚ) + m₃ -
            (if r = 0 then 1 else 0) + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ)

/-- Corollary 11: for `b ≥ 2`, `k, q ≥ 1`, `0 ≤ r < q`:
(i) if `q ∣ b`, `A_b(b^k, q, r) = (b/q - [r = 0])(b^{⌈k/2⌉} + b^{⌊k/2⌋} - 2)/(b - 1)`;
(ii) if `b ≡ 1 (mod q)`, `A_b(b^k, q, r)` is `(b^{⌈k/2⌉} + b^{⌊k/2⌋} - 2)/q` for odd `q`,
`(b - 1)b^{⌊(k-1)/2⌋}/q` for even `q` and odd `r`, and
`((b + 1)b^{⌊(k-1)/2⌋} + 2b^{⌊k/2⌋} - 4)/q` for even `q` and even `r`.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 11. -/
public theorem_wanted palindromeAPCount_base_pow {b k q r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 1 ≤ q) (hr : r < q) :
    (q ∣ b →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        ((b : ℚ) / q - (if r = 0 then 1 else 0)) *
          (((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1))) ∧
    (b ≡ 1 [MOD q] →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        if Odd q then ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / q
        else if Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) + 2 * (b : ℚ) ^ (k / 2) - 4) / q)

/-- Corollary 12: for `b ≥ 2`, odd `q ≥ 1`, `0 ≤ r < q` and `b ≡ 1 (mod q)`, uniformly in `m ≥ 1`,
`A_b(m, q, r) = A_b(m)/q + O*(log m/(2 log b) + 2)`, i.e. the error is at most
`log m/(2 log b) + 2` in absolute value.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 12. -/
public theorem_wanted abs_palindromeAPCount_sub_le {b q r : ℕ} (hb : 2 ≤ b) (hq : Odd q)
    (hr : r < q) (hbq : b ≡ 1 [MOD q]) {m : ℕ} (hm : 1 ≤ m) :
    |(palindromeAPCount b m q r : ℝ) - (palindromeAPCount b m 1 0 : ℝ) / q| ≤
      Real.log m / (2 * Real.log b) + 2

end

end MetaMathlibExt
