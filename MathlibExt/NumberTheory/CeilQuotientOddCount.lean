/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Odd ceiling and floor quotients

`ceilQuotientOddCount_succ_eq` expresses the odd ceiling count at `n + 1` in terms
of the odd floor count at `n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Floor sequence parity count.** For a natural number $n$, the floor sequence parity count
$\mathcal{F}_n$ is the number of integers $k$ with $1 \le k \le n$ for which
$\lfloor n/k \rfloor$ is odd (OEIS A059851).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓕_n`). -/
public def floorQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Odd (n / k))).card

/-- **The floor sequence parity count at $10$.** The number $\mathcal{F}_{10}$ of integers $k$
with $1 \le k \le 10$ for which $\lfloor 10/k \rfloor$ is odd equals $7$: the quotients
$\lfloor 10/k \rfloor$ for $k = 1, \dots, 10$ are $10, 5, 3, 2, 2, 1, 1, 1, 1, 1$, and seven of
them are odd.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 and Figure 1. -/
public theorem floorQuotientOddCount_ten : floorQuotientOddCount 10 = 7 := by
  decide

/-- **Ceiling parity count.** For a natural number $n$, the ceiling parity count $\mathcal{C}_n$
is the number of integers $k$ with $1 \le k \le n$ for which $\lceil n/k \rceil$ is odd
(OEIS A330926).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓒_n`). -/
public def ceilQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd ⌈(n : ℚ) / (k : ℚ)⌉)).card

/-- **The ceiling parity count at $9$.** The ceiling parity count $\mathcal{C}_9$, the number of
integers $k$ with $1 \le k \le 9$ for which $\lceil 9/k \rceil$ is odd, equals $5$.

The ceilings $\lceil 9/k \rceil$ for $k = 1, \dots, 9$ are $9, 5, 3, 3, 2, 2, 2, 2, 1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem ceilQuotientOddCount_nine : ceilQuotientOddCount 9 = 5 := by
  decide +kernel

open Finset in
/-- **Ceiling parity count from the floor parity count.** For a natural number $m$, let
$\mathcal{C}_m$ and $\mathcal{F}_m$ be the numbers of integers $k$ with $1 \le k \le m$ for which
$\lceil m/k \rceil$, respectively $\lfloor m/k \rfloor$, is odd. Then for every natural number
$n$, $\mathcal{C}_{n+1} = (n + 1) - \mathcal{F}_n$.

The source prints a second equality $\mathcal{C}_n = \sum_{d=2}^{n} \lfloor n/d \rfloor (-1)^d$,
which is not part of this statement: it fails at $n = 3$, where $\mathcal{C}_3 = 2$ but the sum
is $1 - 1 = 0$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 9 (`jis-2024-24.2.5-prop-9`). -/
public theorem ceilQuotientOddCount_succ_eq (n : ℕ) :
    (ceilQuotientOddCount (n + 1) : ℤ) = (n + 1 : ℤ) - floorQuotientOddCount n := by
  have hceil : ((Icc 1 (n + 1)).filter fun k : ℕ => Odd ⌈((n + 1 : ℕ) : ℚ) / k⌉) =
      (Icc 1 (n + 1)).filter fun k => ¬ Odd (n / k) := by
    apply filter_congr
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [Rat.ceil_natCast_div_natCast]
      change Odd ((n / (k + 1) + 1 : ℕ) : ℤ) ↔ _
      rw [Int.odd_coe_nat, Nat.odd_add_one]
  have hfloor : ((Icc 1 (n + 1)).filter fun k => Odd (n / k)) =
      (Icc 1 n).filter fun k => Odd (n / k) := by
    ext k
    by_cases hk : k ≤ n
    · simp [hk, hk.trans (Nat.le_succ n)]
    · simp [Nat.div_eq_of_lt (Nat.lt_of_not_ge hk)]
  have h := (Icc 1 (n + 1)).card_filter_add_card_filter_not (fun k => Odd (n / k))
  rw [hfloor, Nat.card_Icc] at h
  rw [ceilQuotientOddCount, floorQuotientOddCount, hceil]
  omega

end

end MetaMathlibExt
