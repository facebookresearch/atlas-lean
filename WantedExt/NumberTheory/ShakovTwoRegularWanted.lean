/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A 2-regular sequence that counts the divisors of `n^2 + 1`

Statements from Anton Shakov, "A 2-Regular Sequence
That Counts The Divisors of `n^2 + 1`", *Journal of
Integer Sequences* 28 (2025), Article 25.6.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Shakov/shakov5.html>).

The sequence `s` is defined by the paper's `2`-regular
recursion (`shakovSeq` below; the value at `0` is a
dummy, the paper's domain is `n ≥ 1`). All statements
were verified numerically: the fibers of `s` match
`τ(m^2 + 1)` for `m ≤ 12`, the block-average formula
for `n ≤ 8`, the primality criterion for `n ≤ 12`,
and `s (a n) = Nat.fib (n - 1)` for `n ≤ 15` (the
paper's `F_n` is `Nat.fib (n - 1)`).

Lemmas 5 and 6 are stated for the integer pair tree
(`integerPairTree`, a
`TripSternTree`). Corollary 11 is not stated: with
the paper's convention `F_1 = 0`, `F_2 = 1` it is false
(see the source audit table).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Composite
public import MathlibExt.NumberTheory.TripSternTree

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

/-- Shakov's `2`-regular sequence: `s(1) = 0`,
`s(2) = s(3) = 1`, and
`s(4k) = 2 s(2k) - s(k)`,
`s(4k+1) = 2 s(2k) + s(2k+1)`,
`s(4k+2) = 2 s(2k+1) + s(2k)`,
`s(4k+3) = 2 s(2k+1) - s(k)`.
The value at `0` is a dummy. -/
def shakovSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | n + 4 =>
      if (n + 4) % 4 = 0 then
        2 * shakovSeq (2 * ((n + 4) / 4)) - shakovSeq ((n + 4) / 4)
      else if (n + 4) % 4 = 1 then
        2 * shakovSeq (2 * ((n + 4) / 4)) +
          shakovSeq (2 * ((n + 4) / 4) + 1)
      else if (n + 4) % 4 = 2 then
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) +
          shakovSeq (2 * ((n + 4) / 4))
      else
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) - shakovSeq ((n + 4) / 4)
  termination_by n => n
  decreasing_by all_goals omega

/-- The auxiliary sequence of Proposition 9: `a(1) = 1`
and `a(n)` is `2 a(n-1)`, `a(n-1) + 1`,
`2 a(n-1) + 1`, `a(n-1) - 1` according as
`n ≡ 0, 1, 2, 3 (mod 4)`. The value at `0` is a dummy. -/
def shakovA : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 4 = 0 then 2 * shakovA (n + 1)
      else if (n + 2) % 4 = 1 then shakovA (n + 1) + 1
      else if (n + 2) % 4 = 2 then 2 * shakovA (n + 1) + 1
      else shakovA (n + 1) - 1

/-- **Theorem 4**:
`∑_{m ≥ 0} τ(m^2 + 1) x^m = ∑_{n ≥ 1} x^{s(n)}`, stated
coefficientwise: for every `m`, the fiber
`{n ≥ 1 : s(n) = m}` is finite with exactly
`τ(m^2 + 1)` elements (in particular `s(n) ≥ 0`).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Theorem 4. -/
theorem_wanted fiber_card (m : ℕ) :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ shakovSeq n) ∧
      ∃ F : Finset ℕ,
        (∀ n : ℕ, n ∈ F ↔ 1 ≤ n ∧ shakovSeq n = (m : ℤ)) ∧
          F.card = (m ^ 2 + 1).divisors.card

/-- **Proposition 7**:
`(1 / 2^n) ∑_{2^n ≤ t < 2^(n+1)} s(t)
  = ((5 + √17)^n - (5 - √17)^n) / (2^(2n-1) √17)`.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 7. -/
theorem_wanted block_average (n : ℕ) :
    (1 / (2 : ℝ) ^ n) *
        (∑ t ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)),
          (shakovSeq t : ℝ)) =
      ((5 + Real.sqrt 17) ^ n - (5 - Real.sqrt 17) ^ n) /
        ((2 : ℝ) ^ (2 * n - 1) * Real.sqrt 17)

/-- **Proposition 8**: `n^2 + 1` is prime if and only
if `{m : s(m) = n} = {2^n, 2^(n+1) - 1}`.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 8. -/
theorem_wanted prime_iff_fiber (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (n ^ 2 + 1) ↔
      {m : ℕ | shakovSeq m = (n : ℤ)} = {2 ^ n, 2 ^ (n + 1) - 1}

/-- **Proposition 9**: with `a` as in `shakovA`,
`s(a(n)) = F_n`, the `n`-th Fibonacci number (the
paper's `F_n` is `Nat.fib (n - 1)`; `a(n)` is a
positive integer, written `Int.toNat` here).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 9. -/
theorem_wanted shakovSeq_shakovA (n : ℕ) (hn : 1 ≤ n) :
    shakovSeq (shakovA n).toNat = (Nat.fib (n - 1) : ℤ)

/-- **Corollary 10**: `F_n^2 + 1` is composite for
`n > 4` (in Mathlib indexing, `Nat.fib k ^ 2 + 1` is
composite for `k ≥ 4`).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Corollary 10. -/
theorem_wanted fib_sq_add_one_composite (k : ℕ) (hk : 4 ≤ k) :
    Nat.IsComposite (Nat.fib k ^ 2 + 1)


/-- The integer pair tree as a `TripSternTree (ℚ × ℚ)`: the
root is `(1, 0)` and each pair `(d, m)` has children
`L(d, m) = (d, m + d)` (a `false` edge) and
`R(d, m) = (((m + d)^2 + 1)/d, m + (m^2 + 1)/d)` (a `true`
edge). Nodes are computed over `ℚ` (the paper's maps involve
division); `integerPairTree.nodeAtPath w` reads the path `w`
from the root.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Journal of Integer
Sequences 28 (2025), Article 25.6.2, Section 3. -/
def integerPairTree : MetaMathlibExt.TripSternTree (ℚ × ℚ) where
  seed := (1, 0)
  leftTransition p := (p.1, p.2 + p.1)
  rightTransition p := (((p.2 + p.1) ^ 2 + 1) / p.1, p.2 + (p.2 ^ 2 + 1) / p.1)

/-- The four pairs on row `2` of the tree, left to right:
`(1, 2), (5, 3), (2, 3), (5, 2)`.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Journal of Integer
Sequences 28 (2025), Article 25.6.2, Section 3, Figure 1. -/
theorem integerPairTree_nodeAtPath_row_two :
    integerPairTree.nodeAtPath [false, false] = (1, 2) ∧
      integerPairTree.nodeAtPath [false, true] = (5, 3) ∧
      integerPairTree.nodeAtPath [true, false] = (2, 3) ∧
      integerPairTree.nodeAtPath [true, true] = (5, 2) := by
  norm_num [integerPairTree, MetaMathlibExt.TripSternTree.nodeAtPath]

/-- **Lemma 5**: every pair `(d, m)` on the integer pair
tree consists of integers with `d ≥ 1`, `m ≥ 0` and
`d ∣ m^2 + 1`.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Journal of Integer
Sequences 28 (2025), Article 25.6.2, Lemma 5 (`jis-2025-25.6.2-lem-5`). -/
theorem_wanted integerPairTree_nodeAtPath_dvd (w : List Bool) :
    ∃ d m : ℕ, integerPairTree.nodeAtPath w = ((d : ℚ), (m : ℚ)) ∧
      1 ≤ d ∧ d ∣ m ^ 2 + 1

/-- **Lemma 6**: if `d ≥ 1`, `m ≥ 0` and `d ∣ m^2 + 1`,
then `(d, m)` appears on the integer pair tree exactly once
(at exactly one path).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Journal of Integer
Sequences 28 (2025), Article 25.6.2, Lemma 6 (`jis-2025-25.6.2-lem-6`). -/
theorem_wanted existsUnique_integerPairTree_nodeAtPath (d m : ℕ)
    (hd : 1 ≤ d) (hdvd : d ∣ m ^ 2 + 1) :
    ∃! w : List Bool,
      integerPairTree.nodeAtPath w = ((d : ℚ), (m : ℚ))

end MathlibExt.NumberTheory.ShakovTwoRegularWanted
