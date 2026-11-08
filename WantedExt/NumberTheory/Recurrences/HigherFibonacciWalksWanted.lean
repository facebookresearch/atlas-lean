/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Walks in tiled rectangles and higher-order Fibonacci convolutions

Statements from Jan Sedlák and Antonín Slavík, "Walks in Tiled
Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.3.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Slavik/slavik4.html>).

Sequences are integer-indexed and valued in `ℚ`.  For `m ≥ 1`, an
`m`-step Fibonacci recurrence means
`F n = F (n-1) + ⋯ + F (n-m)` for every integer `n`.  The standard
sequence also has `F 0 = ⋯ = F (m-2) = 0` and `F (m-1) = 1`.

The weighted sums `S` and `S₂` allow an integer upper limit; a
negative upper limit gives the empty sum.  This is the convention
needed at `n = 0` in Theorem 3.

Theorem 4 is stated for `n ≥ 2*m - 2`.  The printed theorem says
all `n ≥ 0`, but its derivation substitutes `n - 2*m + 2` into a
formula for `w` at a nonnegative index.  Under the empty-sum
convention the unrestricted displayed formula already fails at
`(m, n) = (2, 0)`: the self-convolution is `0`, while the formula
gives `9 / 16`.  The restricted range is therefore recorded
explicitly here and in the source-audit table.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Data.Rat.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- An integer-indexed rational sequence satisfies the `m`-step
Fibonacci recurrence at every integer index. -/
def IsHigherFibRecurrence (m : ℕ) (F : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, F n = ∑ i ∈ Finset.range m, F (n - (i : ℤ) - 1)

/-- The standard initial conditions for the order-`m` Fibonacci
sequence, together with the `m`-step recurrence. -/
def IsStandardHigherFib (m : ℕ) (F : ℤ → ℚ) : Prop :=
  IsHigherFibRecurrence m F ∧
    (∀ i : ℕ, i < m - 1 → F (i : ℤ) = 0) ∧
    F ((m : ℤ) - 1) = 1

/-- The weighted sum `S(m,N,l,q) = ∑_{k=0}^{N} q^k F_{k+l}`.
An upper limit `N < 0` gives the empty sum.  The order `m` is carried
explicitly to match the paper notation, although the sum itself only
uses `F`, `N`, `l`, and `q`. -/
def weightedHigherFibSum (F : ℤ → ℚ) (_m : ℕ) (N l : ℤ) (q : ℚ) : ℚ :=
  if N < 0 then
    0
  else
    ∑ k ∈ Finset.range (N.toNat + 1), q ^ (k : ℤ) * F ((k : ℤ) + l)

/-- The first-moment weighted sum
`S₂(m,N,l,q) = ∑_{k=0}^{N} k q^k F_{k+l}`. -/
def weightedHigherFibMomentSum (F : ℤ → ℚ) (_m : ℕ) (N l : ℤ)
    (q : ℚ) : ℚ :=
  if N < 0 then
    0
  else
    ∑ k ∈ Finset.range (N.toNat + 1),
      (k : ℚ) * q ^ (k : ℤ) * F ((k : ℤ) + l)

/-- The shifted self-convolution `wₙ⁽ᵐ⁾`, defined by
`∑_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}`. -/
def higherFibWalk (F : ℤ → ℚ) (m n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    F ((j : ℤ) + (m : ℤ) - 1) * F ((n : ℤ) - (j : ℤ) + (m : ℤ) - 1)

/-- Mathlib's signed Fibonacci sequence, viewed in `ℚ`. -/
abbrev fibQ (n : ℤ) : ℚ :=
  (Int.fib n : ℚ)

/-- The number of Fibonacci tiling walks encoded algebraically as
`vₙ = ∑_{j=0}^{n} F_{j+1} F_{n-j+1}`. -/
def fibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- The even-upward-step summands in `fibWalkCount`. -/
def evenFibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range (n + 1)).filter Even,
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- The odd-upward-step summands in `fibWalkCount`. -/
def oddFibWalkCount (n : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range (n + 1)).filter Odd,
    fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)

/-- **Theorem 1**: for the standard order-`m` Fibonacci sequence,
the shifted self-convolution `wₙ⁽ᵐ⁾` satisfies
`(m+1) wₙ₊₁ - 2m wₙ = (n+m+2)Fₙ₊ₘ - (n+m)Fₙ₊ₘ₋₁`.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 1. -/
theorem_wanted higherFibWalk_recurrence
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    ((m : ℚ) + 1) * higherFibWalk F m (n + 1) -
        2 * (m : ℚ) * higherFibWalk F m n =
      ((n : ℚ) + (m : ℚ) + 2) * F ((n : ℤ) + (m : ℤ)) -
        ((n : ℚ) + (m : ℚ)) * F ((n : ℤ) + (m : ℤ) - 1)

/-- **Theorem 2**: the closed form for the weighted sum `S(m,n,l,q)`
for every integer-indexed sequence satisfying the `m`-step
recurrence, provided `q^(m+1) - 2*q + 1 ≠ 0`.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 2. -/
theorem_wanted weightedHigherFibSum_eq
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsHigherFibRecurrence m F)
    (n : ℕ) (l : ℤ) (q : ℚ)
    (hq : q ^ (m + 1) - 2 * q + 1 ≠ 0) :
    weightedHigherFibSum F m (n : ℤ) l q =
      ((q - 1) *
        (q ^ (n + 1) * F ((n : ℤ) + l + 1) - F l +
          ∑ i ∈ Finset.Icc 1 (m - 1),
            ∑ j ∈ Finset.Icc 1 i,
              q ^ (i + 1 - j) *
                (q ^ (n + 1) * F ((n : ℤ) + l - (j : ℤ) + 1) -
                  F (l - (j : ℤ))))) /
        (q ^ (m + 1) - 2 * q + 1)

/-- **Theorem 3**: the explicit formula for `wₙ⁽ᵐ⁾` in terms of
`S` and `S₂` at `q = (m+1)/(2m)`.  At `n = 0` the weighted sums
have upper limit `-1` and are empty.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 3. -/
theorem_wanted higherFibWalk_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    higherFibWalk F m n =
      (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ n +
        ((2 * (m : ℚ)) ^ ((n : ℤ) - 1) / ((m : ℚ) + 1) ^ n) *
          (((m : ℚ) + 2) *
              weightedHigherFibSum F m ((n : ℤ) - 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) +
            weightedHigherFibMomentSum F m ((n : ℤ) - 1) (m : ℤ)
              (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            (m : ℚ) *
              weightedHigherFibSum F m ((n : ℤ) - 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            weightedHigherFibMomentSum F m ((n : ℤ) - 1)
              ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))))

/-- **Theorem 4 (restricted range)**: for `n ≥ 2*m - 2`, the
ordinary self-convolution `∑ᵢ Fᵢ Fₙ₋ᵢ` equals
`w_{n-2m+2}` and hence the displayed weighted-sum formula.
The restriction is the range obtained by the paper's substitution;
see the module header for the small-index counterexample to the
unrestricted display.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 4. -/
theorem_wanted higherFib_selfConvolution_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) (hn : 2 * m - 2 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        higherFibWalk F m (n - (2 * m - 2)) ∧
      (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ ((n : ℤ) - 2 * (m : ℤ) + 2) +
          ((2 * (m : ℚ)) ^ ((n : ℤ) - 2 * (m : ℤ) + 1) /
              ((m : ℚ) + 1) ^ ((n : ℤ) - 2 * (m : ℤ) + 2)) *
            (((m : ℚ) + 2) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  (m : ℤ) (((m : ℚ) + 1) / (2 * (m : ℚ))) +
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              (m : ℚ) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))))

/-- **Lemma 5, odd board length**: at board length `2*k - 1`, the
even-position and odd-position walk counts are equal.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem_wanted evenFibWalkCount_odd_length_eq_oddFibWalkCount
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = oddFibWalkCount (2 * k - 1)

/-- **Lemma 5, even board length**: at board length `2*k`, the
even-position walk count exceeds the odd-position count by
`F_{2k+2}`.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem_wanted evenFibWalkCount_even_length_eq_odd_add_fib
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
      oddFibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)

/-- **Theorem 6, odd board length**: both the even-position and
odd-position walk counts at board length `2*k - 1` are
`v_{2k-1} / 2`.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem_wanted fibWalkCounts_odd_length_eq_half
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2 ∧
      oddFibWalkCount (2 * k - 1) = fibWalkCount (2 * k - 1) / 2

/-- **Theorem 6, even board length**: at board length `2*k`, the
even-position count is `(v_{2k} + F_{2k+2}) / 2` and the
odd-position count is `(v_{2k} - F_{2k+2}) / 2`.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem_wanted fibWalkCounts_even_length_eq
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)) / 2 ∧
      oddFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) - fibQ (2 * (k : ℤ) + 2)) / 2

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
