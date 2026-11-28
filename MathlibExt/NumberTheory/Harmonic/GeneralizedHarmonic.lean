/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Generalized harmonic numbers

For real $s$ and natural $n$, the generalized harmonic number is the finite sum
$H_n^{(s)} = \sum_{k=1}^n 1/k^s$, with $H_0^{(s)} = 0$. This module supplies the successor
recurrence and the equivalent sum over $0 \le k < n$ with denominator $(k+1)^s$.

## References

* Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an Identity
  for Their Sums*, INTEGERS 26 (2026), Article A124, pp. 1–7, Section 1 (definition of $H_n^{(s)}$).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized harmonic numbers.** For a real number $s$ and a natural number $n$, the
generalized harmonic number of order $s$ is $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$, where $k^s$ is the
real power.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
noncomputable def generalizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) ^ s)⁻¹

/-- **The zeroth generalized harmonic number.** For every real $s$, the generalized harmonic
number $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ vanishes at $n = 0$: $H_0^{(s)} = 0$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
@[simp]
theorem generalizedHarmonic_zero (s : ℝ) : generalizedHarmonic s 0 = 0 := by
  simp [generalizedHarmonic]

/-- **Recurrence for generalized harmonic numbers.** For every real $s$ and every natural number
$n$, the generalized harmonic numbers $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ satisfy
$H_{n+1}^{(s)} = H_n^{(s)} + 1/(n+1)^s$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
theorem generalizedHarmonic_succ (s : ℝ) (n : ℕ) :
    generalizedHarmonic s (n + 1) = generalizedHarmonic s n + (((n + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  simp [generalizedHarmonic, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- **Range-sum formula for generalized harmonic numbers.** For every real $s$ and natural
number $n$, the generalized harmonic number satisfies
$H_n^{(s)} = \sum_{k=0}^{n-1} 1/(k+1)^s$, with the empty sum at $n = 0$. -/
theorem generalizedHarmonic_eq_sum_range (s : ℝ) (n : ℕ) :
    generalizedHarmonic s n = ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [generalizedHarmonic_succ, ih, Finset.sum_range_succ]

end

end MetaMathlibExt
