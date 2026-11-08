/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey fractions with equal numerators

Statements from Rogelio Tomás García, "Farey
Fractions with Equal Numerators and the Rank of Unit
Fractions", *INTEGERS* 24 (2024), Article A63
(<https://math.colgate.edu/~integers/vol24.html>).

`fareyNumeratorCount n h` is the paper's `N_n(h)`:
the number of fractions of the Farey sequence `F_n`
with numerator `h`, i.e. denominators `h ≤ b ≤ n`
coprime to `h`. Lemma 1's endpoint conventions and
Theorem 1's formula were pinned by brute force over
small parameters (the count in `(1/k, 1/(k-1)]`
requires the strict lower endpoint as soon as
`n > k*h - 1`).

Not stated (see the source audit table): Theorem 2
and Corollaries 3-8 (their rank and counting
formulas could not be pinned from the flattened
extraction), Corollary 1 (false as extracted without
a floor), and Corollary 2 (expository text defining
the rank, not a statement).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

/-- The number of Farey fractions of order `n` with
numerator `h`: denominators `b` with `h ≤ b ≤ n` and
`Nat.Coprime h b`. -/
def fareyNumeratorCount (n h : ℕ) : ℕ :=
  ((Finset.Icc h n).filter (fun b => Nat.Coprime h b)).card

/-- **Lemma 1**: for positive integers `k > 1`, `n`
and `h`, the number of Farey fractions between `1/k`
and `1/(k-1)` in `F_n` with numerator `h` is `φ(h)`
when `n ≥ k*h - 1`; the number between `1/k` and
`2/(2k-1)` with numerator `h` is `φ(h)/2` for
`h > 2` (stated as `2 * count = φ(h)`).

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Lemma 1. -/
theorem_wanted farey_between_count (k n h : ℕ)
    (hk : 1 < k) (hh : 1 ≤ h) (hn : k * h - 1 ≤ n) :
    ((Finset.Icc 1 n).filter (fun b => Nat.Coprime h b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧
          (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1))).card =
        Nat.totient h ∧
      (2 < h →
        2 * ((Finset.Icc 1 n).filter (fun b =>
            Nat.Coprime h b ∧ (1 : ℚ) / k < (h : ℚ) / b ∧
              (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1))).card =
          Nat.totient h)

/-- **Theorem 1**: for `0 < h < n`,
`N_n(h) = φ(h) * (n / h) - ∑_{d ∣ h} μ(d) {n / d}
  - φ(h) + δ_{1h}`, where `μ` is the Möbius function,
`{x}` is the fractional part (written `(n % d) / d`)
and `δ_{1h}` is `1` if
`h = 1` and `0` otherwise.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Theorem 1. -/
theorem_wanted fareyNumeratorCount_formula (h n : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    (fareyNumeratorCount n h : ℚ) =
      (Nat.totient h : ℚ) * (n : ℚ) / h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            ((n % d : ℚ) / d) -
        (Nat.totient h : ℚ) + (if h = 1 then 1 else 0)

end MathlibExt.NumberTheory.FareyNumeratorWanted
