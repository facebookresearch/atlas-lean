/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.PenultsOfTak.WeightedCrossBound
import Mathlib.Tactic.Linarith

/-!
# A one-fifth lower bound for Impartial Tak penults

`MetaMathlibExt.impartialTak_penult_card_ge_fifth` bounds the token count below by
`n ^ 2 / 5 - (8 / 5) * n` using the weighted Cross bound.
-/

namespace MetaMathlibExt

/-- **An $n^2/5$ lower bound for Impartial Tak penults.** Impartial Tak is the placement game on
the $n \times n$ board whose play ends once the tokens contain a road. There is a real constant $C$
such that for every natural number $n$, every Impartial Tak penult on the $n \times n$ board has at
least $n^2/5 - Cn$ tokens; that is, every penult has at least $n^2/5 + O(n)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 9 (`integers-2025-G1-prop-9`). -/
public theorem impartialTak_penult_card_ge_fifth :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 5 - C * n ≤ S.card := by
  refine ⟨8 / 5, fun n S hS => ?_⟩
  by_cases hn : 5 ≤ n
  · have h : (7 : ℝ) * ((n - 4 : ℕ) : ℝ) ^ 2 ≤ 26 * S.card := by
      exact_mod_cast impartialTak_penult_card_ge_weightedCross hn hS
    rw [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_ofNat] at h
    nlinarith only [h, sq_nonneg ((n : ℝ) - 4)]
  · have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast (by omega : n ≤ 4)
    have hsmall := mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hsmall, Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) S.card]

end MetaMathlibExt
