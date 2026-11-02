/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Digits.Defs

/-!
# A classification of the decimal Kaprekar numbers (statement)

Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly 62
(2024), Article iwasaki06162024-ASrev2.

`D_n` is the set of `n`-digit strings of decimal digits (leading zeros allowed), i.e. the
numbers `α < 10^n` written with exactly `n` digits. The Kaprekar transformation sends
`α ∈ D_n` to `α_M - α_L`, where `α_M` and `α_L` arrange the `n` digits of `α` in descending and
ascending order; it depends only on the multiset of digits, and a nonzero `α` with
`f(α) = α` is a Kaprekar number. The value depends on `n`: `495` is a Kaprekar number in `D_3`,
but in `D_4` it is the string `0495` and is sent to `9540 - 0459 = 9081`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Kaprekar difference.** Let $l$ be a list of $k$ natural numbers and let
$a_0 \le a_1 \le \dots \le a_{k-1}$ be its entries in increasing order. The Kaprekar difference of
$l$ is $\alpha_M - \alpha_L$, where $\alpha_M = \sum_{i<k} a_i 10^i$ and
$\alpha_L = \sum_{i<k} a_{k-1-i} 10^i$. When the entries are decimal digits, $\alpha_M$ is the
number written with the digits of $l$ in descending order and $\alpha_L$ is the number written
with them in ascending order (leading zeros allowed).

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarDiff (l : List ℕ) : ℕ :=
  Nat.ofDigits 10 (List.insertionSort (· ≤ ·) l) - Nat.ofDigits 10 (List.insertionSort (· ≥ ·) l)

/-- **Kaprekar map.** For natural numbers $n$ and $\alpha$, take the decimal digits of $\alpha$
(without leading zeros, and no digits at all for $\alpha = 0$) and, if there are fewer than $n$
of them, pad them with leading zeros to a string of exactly $n$ digits. The Kaprekar map sends
$\alpha$ to the Kaprekar difference $\alpha_M - \alpha_L$ of this digit string: the number with
these digits in descending order minus the number with them in ascending order. For
$\alpha < 10^n$ this is the Kaprekar transformation on the set $D_n$ of $n$-digit strings; for
$\alpha \ge 10^n$ nothing is padded and all digits of $\alpha$ are used.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarMap (n α : ℕ) : ℕ :=
  kaprekarDiff (Nat.digits 10 α ++ List.replicate (n - (Nat.digits 10 α).length) 0)

/-- **6174 is fixed by the four-digit Kaprekar map.** The Kaprekar map with $n = 4$ sends $6174$
to itself: $7641 - 1467 = 6174$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_four_6174 : kaprekarMap 4 6174 = 6174 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- **495 is fixed by the three-digit Kaprekar map.** The Kaprekar map with $n = 3$ sends $495$ to
itself: $954 - 459 = 495$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_three_495 : kaprekarMap 3 495 = 495 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- **The four-digit Kaprekar map sends 495 to 9081.** With $n = 4$, the number $495$ is padded to
the digit string $0495$, and the Kaprekar map sends it to $9540 - 0459 = 9081$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public theorem kaprekarMap_four_495 : kaprekarMap 4 495 = 9081 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- **Classification of decimal Kaprekar numbers.** Let $n \ge 3$ and $0 < \alpha < 10^n$. Then
the Kaprekar map on $n$-digit strings fixes $\alpha$ if and only if $\alpha$ is the Kaprekar
difference of some string $s$ of exactly $n$ decimal digits of one of the following five forms,
where juxtaposition is concatenation, $(w)^k$ is the block $w$ repeated $k$ times, and in each
form the exponents are chosen independently with $x, x_1, x_2 \ge 1$ and $y, y_1, y_2 \ge 0$:
$(495)^x$; $6174\,(36)^y$; $(123456789)^x (36)^y$;
$(123456789)^{x_1} (36)^{x_2} (495)^{2x_2} (27)^{3x_2}$;
$(124578)^{x_1} (09)^{x_2} (123456789)^{y_1} (36)^{y_2}$.

The witness string must have length $n$: $495$ is the Kaprekar difference of $(495)^1$, but the
Kaprekar map on $4$-digit strings sends $495$ to $9081$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Theorem 3.1. -/
public theorem_wanted kaprekarMap_fixed_iff {n α : ℕ} (hn : 3 ≤ n) (hα : α < 10 ^ n)
    (hα0 : α ≠ 0) :
    kaprekarMap n α = α ↔
      ∃ s : List ℕ, s.length = n ∧ kaprekarDiff s = α ∧
        ((∃ x, 1 ≤ x ∧ s = (List.replicate x [4, 9, 5]).flatten) ∨
          (∃ y, s = [6, 1, 7, 4] ++ (List.replicate y [3, 6]).flatten) ∨
          (∃ x y, 1 ≤ x ∧ s = (List.replicate x [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
            (List.replicate y [3, 6]).flatten) ∨
          (∃ x₁ x₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate x₂ [3, 6]).flatten ++ (List.replicate (2 * x₂) [4, 9, 5]).flatten ++
              (List.replicate (3 * x₂) [2, 7]).flatten) ∨
          (∃ x₁ x₂ y₁ y₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 4, 5, 7, 8]).flatten ++
              (List.replicate x₂ [0, 9]).flatten ++
              (List.replicate y₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate y₂ [3, 6]).flatten))

end

end MetaMathlibExt
