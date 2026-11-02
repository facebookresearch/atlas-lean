/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Bounds.Basic

/-!
# Odd greedy choice

The one-step choice in the odd greedy (Egyptian) expansion of a positive
rational: the least positive odd denominator whose unit fraction does not
exceed the remainder. Shared by the odd greedy expansion termination
conjecture (`OpenConjectures.NumberTheory.OddGreedyExpansionTermination`)
and the Louwsma--Martino first-denominator characterization
(`WantedExt.NumberTheory.OddGreedyExpansionWanted`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Odd greedy choice.** For a rational number $r$ and a natural number $d$, $d$ is the odd
greedy choice at $r$ when $r > 0$, $d$ is positive and odd, $1/d \le r$, and $d \le e$ for every
positive odd natural number $e$ with $1/e \le r$. Equivalently, $1/d$ is the largest unit
fraction with odd denominator that does not exceed $r$. -/
def IsOddGreedyChoice (r : ℚ) (d : ℕ) : Prop :=
  0 < r ∧ 0 < d ∧ Odd d ∧ (1 : ℚ) / (d : ℚ) ≤ r ∧
    ∀ e : ℕ, 0 < e → Odd e → (1 : ℚ) / (e : ℚ) ≤ r → d ≤ e

/-- **The odd greedy choice needs a positive remainder.** If $d$ is the odd greedy choice at a
rational number $r$, then $r > 0$. -/
theorem IsOddGreedyChoice.pos_r {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : 0 < r :=
  h.1

/-- **The odd greedy choice is positive.** If $d$ is the odd greedy choice at a rational number
$r$, then $d > 0$. -/
theorem IsOddGreedyChoice.pos_d {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : 0 < d :=
  h.2.1

/-- **The odd greedy choice is odd.** If $d$ is the odd greedy choice at a rational number $r$,
then $d$ is odd. -/
theorem IsOddGreedyChoice.odd {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : Odd d :=
  h.2.2.1

/-- **The odd greedy unit fraction does not exceed the remainder.** If $d$ is the odd greedy
choice at a rational number $r$, then $1/d \le r$. -/
theorem IsOddGreedyChoice.inv_le {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : (1 : ℚ) / (d : ℚ) ≤ r :=
  h.2.2.2.1

/-- **The odd greedy choice is minimal.** If $d$ is the odd greedy choice at a rational number
$r$, then $d \le e$ for every positive odd natural number $e$ with $1/e \le r$. -/
theorem IsOddGreedyChoice.min {r : ℚ} {d e : ℕ}
    (h : IsOddGreedyChoice r d) (he : 0 < e) (hodd : Odd e)
    (hle : (1 : ℚ) / (e : ℚ) ≤ r) : d ≤ e :=
  h.2.2.2.2 e he hodd hle

/-- **Uniqueness of the odd greedy choice.** If $d$ and $d'$ are both odd greedy choices at the
same rational number $r$, then $d = d'$. -/
theorem IsOddGreedyChoice.unique {r : ℚ} {d d' : ℕ}
    (h : IsOddGreedyChoice r d) (h' : IsOddGreedyChoice r d') :
    d = d' :=
  le_antisymm (h.min h'.pos_d h'.odd h'.inv_le)
    (h'.min h.pos_d h.odd h.inv_le)

/-- **Characterization of the odd greedy choice.** A natural number $d$ is the odd greedy choice
at a rational number $r$ if and only if $r > 0$ and $d$ is the least element of the set of
positive odd natural numbers $e$ with $1/e \le r$. -/
theorem isOddGreedyChoice_iff {r : ℚ} {d : ℕ} :
    IsOddGreedyChoice r d ↔
      0 < r ∧ IsLeast {e : ℕ | 0 < e ∧ Odd e ∧ (1 : ℚ) / (e : ℚ) ≤ r} d := by
  constructor
  · intro h
    exact ⟨h.pos_r, ⟨⟨h.pos_d, h.odd, h.inv_le⟩,
      fun e he => h.min he.1 he.2.1 he.2.2⟩⟩
  · rintro ⟨hr, ⟨hd, hodd, hle⟩, hmin⟩
    exact ⟨hr, hd, hodd, hle, fun e he hodd' hle' =>
      hmin ⟨he, hodd', hle'⟩⟩

end

end MetaMathlibExt
