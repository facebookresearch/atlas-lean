/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.InfiniteWord.Tribonacci
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

/-!
# Tribonacci analogues of Wythoff-array facts (statements)

Statement-only targets from Chen, Ge, Kalashnikov, Kim, Liang, Lubashev, Qian, Raghavan,
Taycher, Wang and Khovanova, *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*. Tribonacci numbers are `MetaMathlibExt.tribonacci`
(`T₀ = T₁ = 0`, `T₂ = 1`), the Tribonacci word is `InfiniteWord.tribonacciWord`
(0-indexed), and a Tribonacci representation is a digit list written least significant
digit first, digit `i` carrying weight `T_{i+3}` (so the last printed digit has weight `1`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- `w` is a Tribonacci representation of `n`: a `0/1` digit list, least significant digit
first, with no three consecutive ones, whose digit `i` has weight `T_{i+3}`. Leading zeros
(trailing entries of `w`) are allowed.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3 (Tribonacci representation). -/
public def IsTribonacciRepr (w : List ℕ) (n : ℕ) : Prop :=
  (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w ∧
    ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3) = n

/-- The empty digit list represents `0`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem isTribonacciRepr_nil : IsTribonacciRepr [] 0 := by
  simp [IsTribonacciRepr]

/-- The paper's example `(9)_T = 1010`, i.e. `9 = 7 + 2`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem isTribonacciRepr_nine : IsTribonacciRepr [0, 1, 0, 1] 9 := by
  unfold IsTribonacciRepr
  decide

/-- Duchêne and Rigo: the symbol of the Tribonacci word at (0-indexed) position `m` is
`a`, `b` or `c` according as the Tribonacci representation of `m` ends in `0`, `01` or `11`
(the paper's `n`-th symbol with `m = n - 1`; the representation of `0` is empty and ends
in `0`).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Theorem 1
(quoting Duchêne and Rigo 2008) (`jis-2025-25.5.4-thm-1`). -/
public theorem_wanted tribonacciWord_eq_of_isTribonacciRepr (m : ℕ) (w : List ℕ)
    (hw : IsTribonacciRepr w m) :
    InfiniteWord.tribonacciWord m =
      if w.getD 0 0 = 0 then .a else if w.getD 1 0 = 0 then .b else .c

/-- With `α` the real root and `β`, `γ = conj β` the non-real roots of
`x³ = x² + x + 1`, `|T_{n+1} - α T_n| < 2 α^{-n/2} / |β - γ|` for every `n`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Lemma 2
(`jis-2025-25.5.4-lem-2`). -/
public theorem_wanted abs_tribonacci_succ_sub_mul_lt (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1)
    (β : ℂ) (hβ : β ^ 3 = β ^ 2 + β + 1) (hβim : β.im ≠ 0) (n : ℕ) :
    |(tribonacci (n + 1) : ℝ) - α * tribonacci n|
      < 2 * α ^ (-(n : ℝ) / 2) / ‖β - (starRingEnd ℂ) β‖

/-- With `α` the real root of `x³ = x² + x + 1`, the value `T_{n+1} - α T_n` does not have
the same strict sign at three consecutive `n`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 3 (`jis-2025-25.5.4-prop-3`). -/
public theorem_wanted tribonacci_succ_sub_mul_sign_changes (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (n : ℕ) :
    ¬ (∀ i < 3, 0 < (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i)) ∧
      ¬ (∀ i < 3, (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i) < 0)

/-- The first column of the Trithoff array (OEIS A003265, the positive integers whose
Tribonacci representation ends in `1`, in increasing order) grows like
`α / (α - 1) = (α² + 1) / 2` times its index: its `r`-th term (index `r + 1`) divided by
`r + 1` tends to `α / (α - 1)`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 6 (`jis-2025-25.5.4-prop-6`). -/
public theorem_wanted tendsto_trithoff_first_column_div (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) :
    Filter.Tendsto
      (fun r : ℕ => (Nat.nth (fun n => 0 < n ∧ ∃ w, IsTribonacciRepr w n ∧ w.getD 0 0 = 1) r
        : ℝ) / (r + 1))
      Filter.atTop (nhds (α / (α - 1)))

/-- Every natural number is a sum of four Fibternary numbers (base-`3` digits in `{0, 1}`,
no two consecutive ones) and a sum of three Tribternary numbers (base-`3` digits in
`{0, 1}`, no three consecutive ones).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 21 (`jis-2025-25.5.4-prop-21`). -/
public theorem_wanted exists_fibternary_sum_four_and_tribternary_sum_three (n : ℕ) :
    (∃ a b c d : ℕ, (∀ x ∈ [a, b, c, d],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c + d) ∧
      ∃ a b c : ℕ, (∀ x ∈ [a, b, c],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c

/-- Every positive integer has a positive Fibternary multiple (base-`3` digits in `{0, 1}`,
no two consecutive ones).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 22 (`jis-2025-25.5.4-prop-22`). -/
public theorem_wanted exists_fibternary_multiple (n : ℕ) (hn : 0 < n) :
    ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 m

/-- Every positive integer has a positive Tribbinary multiple (binary digits with no three
consecutive ones) and a positive Tribternary multiple (base-`3` digits in `{0, 1}`, no three
consecutive ones).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Corollary 23 (`jis-2025-25.5.4-cor-23`). -/
public theorem_wanted exists_tribbinary_and_tribternary_multiple (n : ℕ) (hn : 0 < n) :
    (∃ m, 0 < m ∧ n ∣ m ∧ ¬ [1, 1, 1] <:+: Nat.digits 2 m) ∧
      ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 m

/-! ## Tribonacci successor, Trithoff rows and precolumns -/

/-- The value `[w]_T` of a digit list `w` in the Tribonacci base, least significant digit
first, digit `i` weighing `T_{i+3}`. Digits may exceed `1` and three consecutive ones are
allowed, so this also evaluates the paper's non-canonical and improper representations.
For a Tribonacci representation `w` of `n`, `tribonacciValue (0 :: w)` is the Tribonacci
successor `out(n)`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Sections 2.3, 5 and 6.1. -/
public def tribonacciValue (w : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3)

/-- The empty word has value `0`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem tribonacciValue_nil : tribonacciValue [] = 0 := by
  simp [tribonacciValue]

/-- The paper's non-canonical word `1110` evaluates to `13`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 5. -/
public theorem tribonacciValue_one_one_one_zero : tribonacciValue [0, 1, 1, 1] = 13 := by
  decide

/-- The paper's improper word `1030` evaluates to `13`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciValue_one_zero_three_zero : tribonacciValue [0, 3, 0, 1] = 13 := by
  decide

/-- Records of `out(n) - α n`. Let `R n` be a Tribonacci representation of `n`, so that
`out(n) = [R n 0]_T`, and let `P` (resp. `Q`) list the indices `i ≥ 1` with
`T_{i+1} - α T_i > 0` (resp. `< 0`) in increasing order, so that the paper's `P(t)` and
`Q(t)` are `Nat.nth P (t - 1)` and `Nat.nth Q (t - 1)` for `t ≥ 1`. A positive (negative)
record is a positive `n` whose difference `out(n) - α n` exceeds (is below) that of every
`m < n`. Part 1: every index `i + 3` used by a positive record lies in `P`, and every index
used by a negative record lies in `Q`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 1 and its negative analogue (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_indices (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1)
    (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n) (n : ℕ) (i : ℕ)
    (hi : (R n).getD i 0 = 1) :
    ((0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R m) : ℝ) - α * m <
        tribonacciValue (0 :: R n) - α * n) →
      0 < (tribonacci (i + 4) : ℝ) - α * tribonacci (i + 3)) ∧
    ((0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R n) : ℝ) - α * n <
        tribonacciValue (0 :: R m) - α * m) →
      (tribonacci (i + 4) : ℝ) - α * tribonacci (i + 3) < 0)

/-- Records of `out(n) - α n` (notation as in `tribonacciSucc_record_indices`). Part 2: for
every `k ≥ 2` the number `T_{P(2)} + ⋯ + T_{P(k)}` is a positive record, and
`T_{Q(2)} + ⋯ + T_{Q(k)}` is a negative record (`j = k - 1 ≥ 1` summands).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 2 and its negative analogue (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_of_partial_sum (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n)
    (j : ℕ) (hj : 1 ≤ j) :
    (let n := (∑ s ∈ Finset.range j,
        tribonacci (Nat.nth (fun i => 0 < (tribonacci (i + 1) : ℝ) - α * tribonacci i) (s + 1)));
      0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R m) : ℝ) - α * m <
        tribonacciValue (0 :: R n) - α * n) ∧
    (let n := (∑ s ∈ Finset.range j,
        tribonacci (Nat.nth (fun i => (tribonacci (i + 1) : ℝ) - α * tribonacci i < 0) (s + 1)));
      0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R n) : ℝ) - α * n <
        tribonacciValue (0 :: R m) - α * m)

/-- Records of `out(n) - α n` (notation as in `tribonacciSucc_record_indices`). Part 3: for
every `t > 1` all sufficiently late positive records use `T_{P(t)}` in their Tribonacci
representation, and all sufficiently late negative records use `T_{Q(t)}` (the record's
"(negative) ... contains `P(t)`" is read as `Q(t)` for negative records, following the
paper's "similar statements are true for negative differences": by part 1 a negative record
uses only indices in `Q`).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 3 (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_eventually_contains (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n)
    (t : ℕ) (ht : 1 < t) :
    (∃ N₀, ∀ N > N₀, (R (Nat.nth (fun n => 0 < n ∧ ∀ m < n,
        (tribonacciValue (0 :: R m) : ℝ) - α * m < tribonacciValue (0 :: R n) - α * n) N)).getD
      (Nat.nth (fun i => 0 < (tribonacci (i + 1) : ℝ) - α * tribonacci i) (t - 1) - 3) 0 = 1) ∧
    ∃ N₀, ∀ N > N₀, (R (Nat.nth (fun n => 0 < n ∧ ∀ m < n,
        (tribonacciValue (0 :: R n) : ℝ) - α * n < tribonacciValue (0 :: R m) - α * m) N)).getD
      (Nat.nth (fun i => (tribonacci (i + 1) : ℝ) - α * tribonacci i < 0) (t - 1) - 3) 0 = 1

/-- Row numbers of the Trithoff array: if `1 :: a` (least significant digit first, the
paper's `[a1]_T`) is the Tribonacci representation of a first-column entry `n`, then `n` is the
`(n - [a]_T)`-th element of the first column (A003265), and
`n - [a]_T = 1 + [a1]_U` with `U_i = T_i + T_{i+1}` (the paper's `U_i = T_{2,i-2}`, i.e.
`0, 1, 2, 3, 6, 11, …`; the paper's alternative formula `T_{i+1} - T_i` is shifted, and the
displayed values are used).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 7 (`jis-2025-25.5.4-lem-7`). -/
public theorem_wanted trithoff_row_number_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr (1 :: a) n) :
    Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (n - tribonacciValue a - 1) = n ∧
      n - tribonacciValue a = 1 + ∑ i ∈ Finset.range (a.length + 1),
        (1 :: a).getD i 0 * (tribonacci i + tribonacci (i + 1))

/-- The difference sequence of the Trithoff row through `[a]_T` contains `[11 · a]_T`, the
digit-wise product evaluated without carries (digit `i` is `a_i + a_{i-1}`). The row entries
from `[a]_T` rightwards are `[0^k a]_T`; the witness difference is taken among them.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 8 (`jis-2025-25.5.4-prop-8`). -/
public theorem_wanted exists_trithoff_row_difference_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr a n) :
    ∃ k : ℕ, (tribonacciValue (List.replicate (k + 1) 0 ++ a) : ℤ) -
        tribonacciValue (List.replicate k 0 ++ a) =
      tribonacciValue ((List.range (a.length + 1)).map fun i => a.getD i 0 + (0 :: a).getD i 0)

/-- Appending a `0` to a non-canonical representation (digits `0`/`1`, three consecutive
ones allowed) of `n` gives a non-canonical representation of `out(n)`: if `w` has `0/1`
digits and value `n`, and `v` is the Tribonacci representation of `n`, then
`[w0]_T = [v0]_T = out(n)`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 12 (`jis-2025-25.5.4-lem-12`). -/
public theorem_wanted tribonacciValue_cons_zero_of_noncanonical (w v : List ℕ) (n : ℕ)
    (hw : ∀ d ∈ w, d ≤ 1) (hwn : tribonacciValue w = n) (hv : IsTribonacciRepr v n) :
    tribonacciValue (0 :: w) = tribonacciValue (0 :: v)

/-- Precolumns of the Trithoff array. If a first-column entry `n` has Tribonacci
representation `abc1` (here `1 :: c :: b :: a`, least significant digit first), extend its
row `n, out(n), out²(n), …` to the left by the Tribonacci rule: the wall is
`out²(n) - out(n) - n = [abc]_T + 1`, the seed `out(n) - n - wall = [ab]_T + c`, and the
pre-seed `n - wall - seed = [a]_T + b`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 13 (`jis-2025-25.5.4-lem-13`). -/
public theorem_wanted trithoff_precolumns (a : List ℕ) (b c n : ℕ)
    (h : IsTribonacciRepr (1 :: c :: b :: a) n) :
    let g₂ : ℤ := tribonacciValue (0 :: 1 :: c :: b :: a)
    let g₃ : ℤ := tribonacciValue (0 :: 0 :: 1 :: c :: b :: a)
    let wall := g₃ - g₂ - n
    let seed := g₂ - n - wall
    wall = tribonacciValue (c :: b :: a) + 1 ∧ seed = tribonacciValue (b :: a) + c ∧
      (n : ℤ) - wall - seed = tribonacciValue a + b

/-- Precolumns in terms of the Tribonacci word (1-indexed positions `p` correspond to
`InfiniteWord.tribonacciWord (p - 1)`). With `R r` the Tribonacci representation of the
first-column entry of row `r + 1` and the wall, seed and pre-seed of that row computed as in
`trithoff_precolumns`: the wall runs increasingly through the positions of `a` and `b`; the
seed starts at `0`, is non-decreasing, and takes each positive value `m` twice if position
`m` holds `a` and once otherwise; the pre-seed starts at `0`, is non-decreasing, takes `0`
twice, and takes each positive `m` three times if position `m` holds `a` or `b` and twice if
it holds `c`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 14 (`jis-2025-25.5.4-thm-14`). -/
public theorem_wanted trithoff_wall_seed_preseed (R : ℕ → List ℕ)
    (hR : ∀ r, IsTribonacciRepr (R r) (Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r)) :
    let g₁ : ℕ → ℤ := fun r => Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r
    let g₂ : ℕ → ℤ := fun r => tribonacciValue (0 :: R r)
    let g₃ : ℕ → ℤ := fun r => tribonacciValue (0 :: 0 :: R r)
    let wall := fun r => g₃ r - g₂ r - g₁ r
    let seed := fun r => g₂ r - g₁ r - wall r
    let preseed := fun r => g₁ r - wall r - seed r
    (∀ r, wall r = 1 + Nat.nth (fun m => InfiniteWord.tribonacciWord m ≠ .c) r) ∧
    (seed 0 = 0 ∧ Monotone seed ∧ ∀ m : ℕ, {r | seed r = m}.ncard =
      if m ≠ 0 ∧ InfiniteWord.tribonacciWord (m - 1) = .a then 2 else 1) ∧
    (preseed 0 = 0 ∧ Monotone preseed ∧ ∀ m : ℕ, {r | preseed r = m}.ncard =
      if m ≠ 0 ∧ InfiniteWord.tribonacciWord (m - 1) ≠ .c then 3 else 2)

/-- Consecutive first-column entries of the Trithoff array differ by `2` or `3`, and the
difference between rows `i + 1` and `i + 2` is `3` exactly when `i + 1` is in A305373, which
the paper identifies as A003144 + A003145: the sum of the `k`-th positions (1-indexed) of the
letters `a` and `b` in the Tribonacci word.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 11 (`jis-2025-25.5.4-prop-11`). -/
public theorem_wanted trithoff_first_column_sub (i : ℕ) :
    (Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
        Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 2 ∨
      Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
          Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 3) ∧
    (Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
        Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 3 ↔
      ∃ k, i + 1 = (Nat.nth (fun m => InfiniteWord.tribonacciWord m = .a) k + 1) +
        (Nat.nth (fun m => InfiniteWord.tribonacciWord m = .b) k + 1))

/-! ## ExtraTribs -/

/-- An extraTrib: a two-sided integer sequence following the Tribonacci rule whose terms are
eventually positive.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 4. -/
public def IsExtraTrib (S : ℤ → ℤ) : Prop :=
  (∀ n, S (n + 3) = S (n + 2) + S (n + 1) + S n) ∧ ∃ N, ∀ n ≥ N, 0 < S n

/-- The zero sequence is not an extraTrib.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 4. -/
public theorem not_isExtraTrib_zero : ¬ IsExtraTrib (fun _ => 0) := by
  rintro ⟨-, N, hN⟩
  exact lt_irrefl 0 (hN N le_rfl)

/-- Every extraTrib `S` has a unique rational Tribonacci-like difference-inverse `Q`
(`Q (n + 1) - Q n = S n`), and some extraTrib is a difference-inverse of `S` exactly when `S`
is not of Type EEOO (parities repeating even, even, odd, odd).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 9 (`jis-2025-25.5.4-thm-9`). -/
public theorem_wanted extraTrib_difference_inverse (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃! Q : ℤ → ℚ, (∀ n, Q (n + 3) = Q (n + 2) + Q (n + 1) + Q n) ∧
      ∀ n, Q (n + 1) - Q n = S n) ∧
    ((∃ Q : ℤ → ℤ, IsExtraTrib Q ∧ ∀ n, Q (n + 1) - Q n = S n) ↔
      ¬ ∃ k : ℤ, ∀ n, (Even (S n) ↔ (n - k) % 4 < 2))

/-- Repeated inversion of an extraTrib stops: there is no infinite chain of extraTribs, each
the difference-inverse of the previous one.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 10 (`jis-2025-25.5.4-thm-10`). -/
public theorem_wanted extraTrib_not_infinitely_invertible (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    ¬ ∃ f : ℕ → ℤ → ℤ, f 0 = S ∧
      ∀ k, IsExtraTrib (f (k + 1)) ∧ ∀ n, f (k + 1) (n + 1) - f (k + 1) n = f k n

/-- If every term of an extraTrib is divisible by `n`, its row number in the Trithoff array
is `1` modulo `n`. The extraTrib's tail `S (k₀), S (k₀ + 1), …` is row `r + 1`, whose
first-column entry has Tribonacci representation `w`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 18 (`jis-2025-25.5.4-thm-18`). -/
public theorem_wanted extraTrib_row_number_modEq_one (S : ℤ → ℤ) (hS : IsExtraTrib S) (n : ℕ)
    (hn : ∀ k, (n : ℤ) ∣ S k) (r : ℕ) (w : List ℕ) (hw : IsTribonacciRepr w (Nat.nth (fun m => 0 < m
        ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r))
    (k₀ : ℤ) (hrow : ∀ j : ℕ, S (k₀ + j) = tribonacciValue (List.replicate j 0 ++ w)) :
    r + 1 ≡ 1 [MOD n]

/-- Extending an extraTrib to the left reaches a negative term, and no three consecutive
terms to the left of a negative term have the same strict sign.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 19 (`jis-2025-25.5.4-lem-19`). -/
public theorem_wanted extraTrib_left_extension (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃ k, S k < 0) ∧ ∀ k, S k < 0 → ∀ n, n + 2 < k →
      ¬ (0 < S n ∧ 0 < S (n + 1) ∧ 0 < S (n + 2)) ∧ ¬ (S n < 0 ∧ S (n + 1) < 0 ∧ S (n + 2) < 0)

/-- The reversal `n ↦ |S (-n)|` of an extraTrib is not an extraTrib.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 20 (`jis-2025-25.5.4-thm-20`). -/
public theorem_wanted not_isExtraTrib_reversal (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    ¬ IsExtraTrib (fun n => |S (-n)|)

/-! ## Canonization of improper representations

Words in this section are written most significant digit first, as in the paper; the
procedure pads a word with a `0` on the left before each step. -/

/-- Leftmost carrying: the first block `d a b c` with `a, b, c > 0` becomes
`(d + 1) (a - 1) (b - 1) (c - 1)`; `none` if there is no such block.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciLeftmostCarry : List ℕ → Option (List ℕ)
  | [] => none
  | d :: tl =>
    match tl with
    | a :: b :: c :: rest =>
      if 0 < a ∧ 0 < b ∧ 0 < c then some ((d + 1) :: (a - 1) :: (b - 1) :: (c - 1) :: rest)
      else (tribonacciLeftmostCarry tl).map (d :: ·)
    | _ => none

/-- Carrying `0111 ↦ 1000`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 5. -/
public theorem tribonacciLeftmostCarry_zero_one_one_one :
    tribonacciLeftmostCarry [0, 1, 1, 1] = some [1, 0, 0, 0] := by
  decide

/-- The weight of an improper word (padded with a `0` on the left): the sum of the digits to
the right of the last `0` preceding the improper boundary, the leftmost digit `≥ 2`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciImproperWeight (w : List ℕ) : ℕ :=
  let v := 0 :: w
  let p := v.findIdx (fun d => 2 ≤ d)
  ((v.take p).reverse.takeWhile (fun d => d ≠ 0)).sum + (v.drop p).sum

/-- The weight of `010113` is `1 + 1 + 3 = 5`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciImproperWeight_example : tribonacciImproperWeight [0, 1, 0, 1, 1,
    3] = 5 := by
  decide

/-- One step of the canonization procedure on the padded word `0 :: w`: Step 1 (leftmost
carrying) when possible; otherwise, with `p` the improper boundary, Step 2a
(`0abcd ↦ 1(a-2)bc(d+1)`) when the digit before it is `0` and Step 2b
(`01a0cd ↦ 10(a-2)0(c+1)(d+1)`) otherwise; `none` when the boundary is among the last three
digits.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciCanonizationStep (w : List ℕ) : Option (List ℕ) :=
  let v := 0 :: w
  match tribonacciLeftmostCarry v with
  | some u => some u
  | none =>
    let p := v.findIdx (fun d => 2 ≤ d)
    if p + 3 < v.length then
      if v.getD (p - 1) 0 = 0 then
        some (((v.set (p - 1) 1).set p (v.getD p 0 - 2)).set (p + 3) (v.getD (p + 3) 0 + 1))
      else
        some (((((v.set (p - 2) 1).set (p - 1) 0).set p (v.getD p 0 - 2)).set (p + 2)
          (v.getD (p + 2) 0 + 1)).set (p + 3) (v.getD (p + 3) 0 + 1))
    else none

/-- Run at most `n` canonization steps, stopping at a canonical word (digits `0`/`1`, no
three consecutive ones); `none` if a step is undefined.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciCanonizationRun : ℕ → List ℕ → Option (List ℕ)
  | 0, w => some w
  | n + 1, w =>
    if (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w then some w
    else (tribonacciCanonizationStep w).bind (tribonacciCanonizationRun n)

/-- `2000000` (twice `T_9 = 44`) canonizes in one Step 2a to `10001000` (`81 + 7`).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciCanonizationRun_example :
    tribonacciCanonizationRun 2 [2, 0, 0, 0, 0, 0, 0] = some [1, 0, 0, 0, 1, 0, 0, 0] := by
  decide

/-- Leftmost carrying on an improper word does not move the improper boundary to the left
and does not increase the weight (read for a result that is still improper; the carry acts
on the padded word `0 :: w`, of the same length as the result).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 15 (`jis-2025-25.5.4-lem-15`). -/
public theorem_wanted tribonacciLeftmostCarry_boundary_weight (w u : List ℕ)
    (hw : ∃ d ∈ w, 2 ≤ d) (hu : tribonacciLeftmostCarry (0 :: w) = some u)
    (hu' : ∃ d ∈ u, 2 ≤ d) :
    (0 :: w).findIdx (fun d => 2 ≤ d) ≤ u.findIdx (fun d => 2 ≤ d) ∧
      tribonacciImproperWeight u ≤ tribonacciImproperWeight w

/-- The canonization procedure applied to an improper word of weight `m` followed by at least
`3m` zeros terminates in a canonical word.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 16 (`jis-2025-25.5.4-thm-16`). -/
public theorem_wanted tribonacciCanonizationRun_terminates (w : List ℕ) (hw : ∃ d ∈ w, 2 ≤ d)
    (k : ℕ) (hk : 3 * tribonacciImproperWeight w ≤ k) :
    ∃ n v, tribonacciCanonizationRun n (w ++ List.replicate k 0) = some v ∧
      (∀ d ∈ v, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: v

/-- If the canonization procedure takes the improper word `w` to the canonical word `v`,
the same steps take `w0^k` to `v0^k`.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Corollary 17 (`jis-2025-25.5.4-cor-17`). -/
public theorem_wanted tribonacciCanonizationRun_append_zeros (w v : List ℕ) (n k : ℕ)
    (hw : ∃ d ∈ w, 2 ≤ d) (hv : tribonacciCanonizationRun n w = some v)
    (hcan : (∀ d ∈ v, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: v) :
    tribonacciCanonizationRun n (w ++ List.replicate k 0) = some (v ++ List.replicate k 0)

end

end MetaMathlibExt
