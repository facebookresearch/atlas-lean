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
recursion (`shakovSeq`; the value at `0` is a
dummy, the paper's domain is `n ≥ 1`). The primality
criterion was verified numerically for `n ≤ 12`.

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
public import MathlibExt.NumberTheory.FibonacciSquareAddOne
public import MathlibExt.NumberTheory.ShakovBlockAverage
public import MathlibExt.NumberTheory.TripSternTree

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

/-- **Primality of $n^2 + 1$ from the fibers of Shakov's sequence.** Let $s$ be Shakov's
$2$-regular sequence. For every natural number $n \ge 1$, the number $n^2 + 1$ is prime if and
only if the set of natural numbers $m$ with $s(m) = n$ is exactly $\{2^n, 2^{n+1} - 1\}$.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 8. -/
theorem_wanted prime_iff_fiber (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (n ^ 2 + 1) ↔
      {m : ℕ | shakovSeq m = (n : ℤ)} = {2 ^ n, 2 ^ (n + 1) - 1}

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
