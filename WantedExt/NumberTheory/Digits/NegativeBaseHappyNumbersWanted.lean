/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Function.Iterate

/-!
# Negative base happy numbers

Statements from Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The
Fibonacci Quarterly 62 (2024), no. 2, 125–129.

For `b ≤ -2` every integer `a` has a unique expansion `a = ∑_{i=0}^n a_i b^i` with digits
`0 ≤ a_i ≤ |b| - 1`, and `S_{2,b}(a) = ∑ a_i²`. An integer `a` is `b`-happy if `S_{2,b}^k(a) = 1`
for some `k ≥ 1`. `U_{2,b}` is the set of positive integers lying on a cycle of `S_{2,b}`, and a
finite set `T` is `(2, b)`-good if for each `u ∈ U_{2,b}` there are `n, k ≥ 1` with
`S_{2,b}^k(t + n) = u` for all `t ∈ T`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Fuelled digit-square sum in base `b`: peel the least digit `a % b ∈ [0, |b|)` and continue
with `(a - a % b) / b`, stopping at `0` or when the fuel runs out.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def negBaseSqDigitSumAux (b : ℤ) : ℕ → ℤ → ℤ
  | 0, _ => 0
  | fuel + 1, a =>
      if a = 0 then 0 else (a % b) ^ 2 + negBaseSqDigitSumAux b fuel ((a - a % b) / b)

/-- The function `S_{2,b}`: the sum of the squares of the base-`b` digits of `a`, for `b ≤ -2`.
The fuel `2|a| + 2` suffices: the quantity `2a` (for `a ≥ 0`), `2|a| + 1` (for `a < 0`) strictly
decreases at each digit step.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def negBaseSqDigitSum (b a : ℤ) : ℤ :=
  negBaseSqDigitSumAux b (2 * a.natAbs + 2) a

/-- `S_{2,b}(0) = 0`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem negBaseSqDigitSum_zero (b : ℤ) : negBaseSqDigitSum b 0 = 0 := by
  simp [negBaseSqDigitSum, negBaseSqDigitSumAux]

/-- A single nonzero digit `0 < d < |b|` has `S_{2,b}(d) = d²`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem negBaseSqDigitSum_of_digit {b d : ℤ} (hd0 : 0 < d) (hd : d < -b) :
    negBaseSqDigitSum b d = d ^ 2 := by
  have hmod : d % b = d := by
    rw [← Int.emod_neg]
    exact Int.emod_eq_of_lt hd0.le hd
  unfold negBaseSqDigitSum
  rw [show 2 * d.natAbs + 2 = (2 * d.natAbs + 1) + 1 from rfl, negBaseSqDigitSumAux]
  simp only [hd0.ne', ↓reduceIte, hmod, sub_self, Int.zero_ediv]
  cases 2 * d.natAbs + 1 <;> simp [negBaseSqDigitSumAux]

/-- Sample values: `-1 = 1·(-10) + 9` and `10 = 1·100 + 9·(-10)` give `S_{2,-10}(-1) =
S_{2,-10}(10) = 82`, and `5 = 16 - 12 + 1` gives `S_{2,-4}(5) = 11`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem negBaseSqDigitSum_samples :
    negBaseSqDigitSum (-10) (-1) = 82 ∧ negBaseSqDigitSum (-10) 10 = 82 ∧
      negBaseSqDigitSum (-4) 5 = 11 := by
  decide

/-- An integer `a` is `b`-happy if `S_{2,b}^k(a) = 1` for some `k ≥ 1`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def IsNegBaseHappy (b a : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum b)^[k] a = 1

/-- `1` is `b`-happy for every `b ≤ -2`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem isNegBaseHappy_one {b : ℤ} (hb : b ≤ -2) : IsNegBaseHappy b 1 :=
  ⟨1, one_pos, by
    simpa using negBaseSqDigitSum_of_digit (b := b) (d := 1) one_pos (by omega)⟩

/-- `U_{2,b}`: the positive integers `u` with `S_{2,b}^m(u) = u` for some `m ≥ 1`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def negBaseSqDigitCycles (b : ℤ) : Set ℤ :=
  {u | 0 < u ∧ ∃ m : ℕ, 0 < m ∧ (negBaseSqDigitSum b)^[m] u = u}

/-- `1 ∈ U_{2,b}` for every `b ≤ -2`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem one_mem_negBaseSqDigitCycles {b : ℤ} (hb : b ≤ -2) : (1 : ℤ) ∈ negBaseSqDigitCycles b :=
  ⟨one_pos, isNegBaseHappy_one hb⟩

/-- A finite set `T` is `(2, b)`-good if for each `u ∈ U_{2,b}` there exist `n, k ≥ 1` with
`S_{2,b}^k(t + n) = u` for every `t ∈ T`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def IsNegBaseGood (b : ℤ) (T : Finset ℤ) : Prop :=
  ∀ u ∈ negBaseSqDigitCycles b, ∃ n : ℤ, 0 < n ∧ ∃ k : ℕ, 0 < k ∧
    ∀ t ∈ T, (negBaseSqDigitSum b)^[k] (t + n) = u

/-- Grundman–Harris, part (1): there is an infinite arithmetic progression with difference `3` of
`-2`-happy numbers; indeed `a ∈ ℤ` is `-2`-happy iff `a ≡ 1 (mod 3)`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_neg_two_iff :
    (∃ n : ℤ, ∀ i : ℕ, IsNegBaseHappy (-2) (n + 3 * i)) ∧
      ∀ a : ℤ, IsNegBaseHappy (-2) a ↔ a ≡ 1 [ZMOD 3]

/-- Grundman–Harris, part (2): there is an infinite arithmetic progression with difference `2` of
`-3`-happy numbers; indeed `a ∈ ℤ` is `-3`-happy iff `a ≡ 1 (mod 2)`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_neg_three_iff :
    (∃ n : ℤ, ∀ i : ℕ, IsNegBaseHappy (-3) (n + 2 * i)) ∧
      ∀ a : ℤ, IsNegBaseHappy (-3) a ↔ a ≡ 1 [ZMOD 2]

/-- Grundman–Harris, part (3): for `b ∈ {-4, -6, -8, -10}` there are arbitrarily long finite runs
of consecutive `b`-happy numbers.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_consecutive_runs_small (b : ℤ)
    (hb : b = -4 ∨ b = -6 ∨ b = -8 ∨ b = -10) (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + i)

/-- Grundman–Harris, part (4): for odd `b ≤ -3` there are arbitrarily long finite arithmetic
progressions with difference `2` of `b`-happy numbers.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_two_consecutive_runs_odd (b : ℤ) (hb : b ≤ -3)
    (hodd : Odd b) (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + 2 * i)

/-- For even `b ≤ -4` there are arbitrarily long finite runs of consecutive `b`-happy numbers.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.2. -/
public theorem_wanted isNegBaseHappy_consecutive_runs_even (b : ℤ) (hb : b ≤ -4) (heven : Even b)
    (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + i)

/-- For `b ≤ -2`, a finite set `T` of positive integers and a composition `F` of a finite sequence
of the maps `S_{2,b}` and `I(t) = t + 1` (the list `ops`, `true` for `S_{2,b}`), if `F(T)` is
`(2, b)`-good then `T` is `(2, b)`-good.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Lemma 2.1. -/
public theorem_wanted isNegBaseGood_of_image_comp (b : ℤ) (hb : b ≤ -2) (T : Finset ℤ)
    (hT : ∀ t ∈ T, 0 < t) (ops : List Bool)
    (hgood : IsNegBaseGood b (T.image
      ((ops.map fun op => if op then negBaseSqDigitSum b else fun t => t + 1).foldr (· ∘ ·) id))) :
    IsNegBaseGood b T

/-- For `b ≤ -7` and each finite set `A` of positive integers there is `k ≥ 1` with
`S_{2,b}^k(a) < 2b²` for every `a ∈ A`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Lemma 2.2. -/
public theorem_wanted exists_iterate_negBaseSqDigitSum_lt (b : ℤ) (hb : b ≤ -7) (A : Finset ℤ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∃ k : ℕ, 0 < k ∧ ∀ a ∈ A, (negBaseSqDigitSum b)^[k] a < 2 * b ^ 2

/-- For even `b ≤ -12` and `0 < v < 2b²` there are `0 ≤ w < v` and `0 ≤ c ≤ |b| - 2` with
`S_{2,b}((|b| - 1) b + v - w - 1) - S_{2,b}((|b| - 1) b² + |b| - 1 - w) + 5 + 2c ≡ 0
(mod |b| + 1)`.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Lemma 3.1. -/
public theorem_wanted exists_negBaseSqDigitSum_congr (b : ℤ) (hb : b ≤ -12) (heven : Even b)
    (v : ℤ) (hv0 : 0 < v) (hv : v < 2 * b ^ 2) :
    ∃ w c : ℤ, 0 ≤ w ∧ w < v ∧ 0 ≤ c ∧ c ≤ |b| - 2 ∧
      negBaseSqDigitSum b ((|b| - 1) * b + v - w - 1) -
          negBaseSqDigitSum b ((|b| - 1) * b ^ 2 + |b| - 1 - w) + 5 + 2 * c ≡ 0 [ZMOD |b| + 1]

/-- For even `b ≤ -4`, every finite set of positive integers is `(2, b)`-good.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 3.2. -/
public theorem_wanted isNegBaseGood_of_even (b : ℤ) (hb : b ≤ -4) (heven : Even b) (T : Finset ℤ)
    (hT : ∀ t ∈ T, 0 < t) :
    IsNegBaseGood b T

end

end MetaMathlibExt
