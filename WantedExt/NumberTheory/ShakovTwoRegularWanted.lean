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

Not stated (see the source audit table): Lemmas 5
and 6 and Corollary 11, which quantify over the
paper's integer pair tree and second component tree,
neither defined in the extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Composite

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

end MathlibExt.NumberTheory.ShakovTwoRegularWanted
