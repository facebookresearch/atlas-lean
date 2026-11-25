/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Odd harmonic numbers

`oddHarmonic n = O_n = ∑_{m=1}^n 1/(2m-1)`, with `O_0 = 0`, and its relation
`O_n = H_{2n} - H_n / 2` to the harmonic numbers.
-/

@[expose] public section

namespace MetaMathlibExt

open Finset

/-- **Odd harmonic numbers.** For a natural number $n$, the $n$-th odd harmonic number is the
rational number $O_n = \sum_{m=1}^{n} \frac{1}{2m-1}$, the sum of the reciprocals of the first
$n$ odd positive integers; in particular $O_0 = 0$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Section 1 (definition of `O_n`). -/
def oddHarmonic (n : ℕ) : ℚ :=
  ∑ m ∈ range n, 1 / (2 * (m : ℚ) + 1)

/-- **The zeroth odd harmonic number.** The odd harmonic number $O_0$ equals $0$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Section 1. -/
@[simp]
theorem oddHarmonic_zero : oddHarmonic 0 = 0 := by
  simp [oddHarmonic]

/-- **Recurrence for the odd harmonic numbers.** For every natural number $n$, the odd harmonic
numbers satisfy $O_{n+1} = O_n + \frac{1}{2n+1}$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Section 1 (used in the Remark after Corollary 1). -/
theorem oddHarmonic_succ (n : ℕ) :
    oddHarmonic (n + 1) = oddHarmonic n + 1 / (2 * (n : ℚ) + 1) := by
  simp [oddHarmonic, sum_range_succ]

/-- **Odd harmonic numbers in terms of harmonic numbers.** For every natural number $n$, the odd
harmonic number $O_n$ and the harmonic numbers $H_k = \sum_{j=1}^{k} \frac{1}{j}$ satisfy
$O_n = H_{2n} - \frac{H_n}{2}$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Section 1 (definition of `O_n`). -/
theorem oddHarmonic_eq_harmonic (n : ℕ) : oddHarmonic n = harmonic (2 * n) - harmonic n / 2 := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
    rw [oddHarmonic_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega, harmonic_succ (2 * n + 1),
      harmonic_succ (2 * n), harmonic_succ n]
    have h1 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
    have h3 : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end MetaMathlibExt
