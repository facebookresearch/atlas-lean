/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Further extensions of Sury's identity

Statements from Gregory Dresden and Xiaoya Gao, "Further Extensions
of Sury's Identity", *Journal of Integer Sequences* 29 (2026),
Article 26.3.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dresden/dresden34.html>).

The generic sequences are taken over `ℚ`.  In Theorem 2 the paper
allows a negative offset `k`; the negative terms are the ones obtained
by running the recurrence backward, which uses `c₂ ≠ 0`.  We encode
that extension directly by requiring the recurrence at every integer
index.

For the Fibonacci and Lucas specializations, `j`-step means the
subsequence of terms with indices `j*n`, and offset `k` means indices
`j*n + k`.  Fibonacci values use Mathlib's signed `Int.fib`, cast to
`ℚ`; its negative-index convention is the standard one used in the
paper.  The Lucas extension below uses `L_{-m} = (-1)^m * L_m`.
Signed values are needed for the `n = 0` case of Theorem 3 and for
negative offsets in Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

/-- Mathlib's signed Fibonacci sequence `Int.fib`, viewed in `ℚ`. -/
abbrev fibAtInt (n : ℤ) : ℚ :=
  (Int.fib n : ℚ)

/-- The Lucas numbers extended to integer indices by
`L_{-m} = (-1)^m * L_m`, viewed in `ℚ`. -/
def lucasAtInt (n : ℤ) : ℚ :=
  if 0 ≤ n then
    (MetaMathlibExt.lucasNumber n.toNat : ℚ)
  else
    (-1 : ℚ) ^ ((-n).toNat) *
      (MetaMathlibExt.lucasNumber (-n).toNat : ℚ)

/-- **Theorem 1**: Sury's identity for a second-order recurrence with
`A 0 = 1`.  With `t = c₁ - A 1`, assumed nonzero as in the source,
the weighted initial segment determines `A (n+2) - A 1 * A (n+1)`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 1. -/
theorem_wanted second_order_recurrence_initial_one_sury_sum
    (A : ℕ → ℚ) (c₁ c₂ : ℚ)
    (hc₂ : c₂ ≠ 0) (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, A (n + 2) = c₁ * A (n + 1) + c₂ * A n)
    (ht : c₁ - A 1 ≠ 0) (n : ℕ) :
    A (n + 2) - A 1 * A (n + 1) =
      (A 2 - A 1 ^ 2) *
        ∑ i ∈ Finset.range (n + 1), (c₁ - A 1) ^ (n - i) * A i

/-- **Theorem 2**: the offset form for an integer-indexed second-order
recurrence.  The offset `k` may be negative; the recurrence is
required at all integer indices, matching the paper's backward
extension using `c₂ ≠ 0`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 2. -/
theorem_wanted second_order_recurrence_offset_sury_sum
    (X : ℤ → ℚ) (c₁ c₂ : ℚ)
    (hc₂ : c₂ ≠ 0)
    (hrec : ∀ n : ℤ, X (n + 2) = c₁ * X (n + 1) + c₂ * X n)
    (k : ℤ) (hXk : X k ≠ 0) (hXk_pred : X (k - 1) ≠ 0)
    (n : ℕ) :
    X 0 * X ((n : ℤ) + 2) - X 1 * X ((n : ℤ) + 1) =
      ((X 0 * X 2 - X 1 ^ 2) / X k) *
        ∑ i ∈ Finset.range (n + 1),
          (-c₂ * X (k - 1) / X k) ^ (n - i) * X ((i : ℤ) + k)

/-- **Theorem 3**: the `j`-step Fibonacci identity.  The term
`F_{j(n-1)}` uses Mathlib's signed Fibonacci extension when `n = 0`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 3. -/
theorem_wanted fib_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    lucasAtInt (j : ℤ) ^ (n + 1) *
          fibAtInt ((j : ℤ) * ((n : ℤ) - 1)) +
        (-1 : ℚ) ^ (j * (n + 1)) * fibAtInt (2 * (j : ℤ)) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * lucasAtInt (j : ℤ) ^ i *
          fibAtInt ((j : ℤ) * (i : ℤ))

/-- **Theorem 4**: the `j`-step Lucas identity over `ℚ`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 4. -/
theorem_wanted lucas_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    2 * (lucasAtInt (j : ℤ) / 2) ^ (n + 1) *
          (fibAtInt ((j : ℤ) * (n : ℤ)) / fibAtInt (j : ℤ)) +
        2 * (-1 : ℚ) ^ (j * n) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * (lucasAtInt (j : ℤ) / 2) ^ i *
          lucasAtInt ((j : ℤ) * (i : ℤ))

/-- **Theorem 5, Fibonacci offset formula**: for `j > |k| > 0`, the
`j`-step Fibonacci numbers with offset `k` sum to `F_{j(n+1)}`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula (53). -/
theorem_wanted fib_step_offset_sury_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) (hk : k ≠ 0) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / fibAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^
              (n - i) *
            fibAtInt ((j : ℤ) * (i : ℤ) + k)

/-- **Theorem 5, Lucas offset formula**: for `j > |k|`, the `j`-step
Lucas numbers with offset `k` sum to `F_{j(n+1)}`.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula (54). -/
theorem_wanted lucas_step_offset_sury_fib_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / lucasAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ k * lucasAtInt ((j : ℤ) - k) / lucasAtInt k) ^
              (n - i) *
            lucasAtInt ((j : ℤ) * (i : ℤ) + k)

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
