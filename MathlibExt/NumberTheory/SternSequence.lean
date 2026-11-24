/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Stern's diatomic sequence.** The Stern sequence is the function
$s : \mathbb{N} \to \mathbb{N}$ defined by $s(0) = 0$, $s(1) = 1$, and, for every $n \ge 1$,
$s(2n) = s(n)$ and $s(2n + 1) = s(n) + s(n + 1)$.

Source: Stern sequence (`jis_term_8e87f9eebae5b6160acdc06a`, "Stern diatomic sequence",
OEIS A002487); JIS Lansing, lines 92-103; JIS Dennison, lines 80-85. -/
def sternSequence : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then sternSequence ((n + 2) / 2)
    else sternSequence ((n + 2) / 2) + sternSequence ((n + 2) / 2 + 1)
termination_by n => n
decreasing_by all_goals omega

/-- **Stern sequence at zero.** The Stern sequence $s$ satisfies $s(0) = 0$.

Source: Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487; JIS Lansing,
lines 92-103. -/
theorem stern_zero : sternSequence 0 = 0 := by
  simp only [sternSequence]

/-- **Stern sequence at one.** The Stern sequence $s$ satisfies $s(1) = 1$.

Source: Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487; JIS Lansing,
lines 92-103. -/
theorem stern_one : sternSequence 1 = 1 := by
  simp only [sternSequence]

/-- **Even-index recurrence for the Stern sequence.** For every natural number $n \ge 1$, the
Stern sequence $s$ satisfies $s(2n) = s(n)$.

Source: Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487; JIS Lansing,
lines 92-103; JIS Dennison, lines 80-85. -/
theorem stern_even (n : Nat) (hn : 1 ≤ n) : sternSequence (2 * n) = sternSequence n := by
  have h2 : 2 * n = ((2 * n - 2) + 2) := by omega
  rw [h2]
  have hmod : (((2 * n - 2) + 2) % 2) = 0 := by omega
  have hdiv : (((2 * n - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_left hmod, hdiv]

/-- **Odd-index recurrence for the Stern sequence.** For every natural number $n \ge 1$, the
Stern sequence $s$ satisfies $s(2n + 1) = s(n) + s(n + 1)$.

Source: Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487; JIS Lansing,
lines 92-103; JIS Dennison, lines 80-85. -/
theorem stern_odd (n : Nat) (hn : 1 ≤ n) :
    sternSequence (2 * n + 1) = sternSequence n + sternSequence (n + 1) := by
  have h2 : 2 * n + 1 = (((2 * n + 1) - 2) + 2) := by omega
  rw [h2]
  have hne : (((2 * n + 1) - 2) + 2) % 2 ≠ 0 := by omega
  have hdiv : ((((2 * n + 1) - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_right hne, hdiv]

end

end MetaMathlibExt
