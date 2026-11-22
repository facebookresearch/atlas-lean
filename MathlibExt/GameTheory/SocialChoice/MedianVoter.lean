/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Nat.Even

@[expose] public section

/-!
# Black's median voter theorem (Atlas AP03.T02)

Alternatives lie on a line, a linearly ordered type `α`. Each voter `v` in a
finite electorate `V` has a peak `peak v` and a utility `utility v` that is
strictly increasing up to the peak and strictly decreasing after it (strict
single-peakedness; alternatives on opposite sides of the peak may tie).

An alternative `m` is a median of the peaks when at least half of the voters
have peak `≤ m` and at least half have peak `≥ m`. With an odd number of
voters, a median peak is a Condorcet winner: against every other alternative
`b`, a strict majority of voters strictly prefers `m` to `b`. Even electorates
are excluded: with two voters whose peaks differ, no alternative wins a strict
majority against the other peak.

## References

* D. Black, "On the rationale of group decision-making", J. Political Economy
  56 (1948), 23--34.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*,
  Oxford University Press, 1995, Definition 21.D.3 (single-peaked preferences)
  and Proposition 21.D.1 (median voter theorem).
* K. Dougherty, *The Median Voter Theorem (one dimension)*, University of
  Georgia lecture slides (statement and proof for an odd number of voters).
-/

namespace MathlibExt.GameTheory.SocialChoice

/-- A strictly single-peaked utility profile over a linearly ordered set of
alternatives `α`, for voters `V`. -/
structure SinglePeakedProfile (V α : Type*) [LinearOrder α] where
  /-- `utility v a` is voter `v`'s utility of alternative `a`. -/
  utility : V → α → ℝ
  /-- `peak v` is voter `v`'s most preferred alternative. -/
  peak : V → α
  /-- Utility strictly increases on alternatives up to the peak. -/
  lt_of_lt_of_le_peak : ∀ v a b, a < b → b ≤ peak v → utility v a < utility v b
  /-- Utility strictly decreases on alternatives from the peak on. -/
  lt_of_peak_le_of_lt : ∀ v a b, peak v ≤ a → a < b → utility v b < utility v a

namespace SinglePeakedProfile

/-- `m` is a Condorcet winner: against every other alternative `b`, more than
half of the voters strictly prefer `m` to `b`. -/
def IsCondorcetWinner {V α : Type*} [Fintype V] [LinearOrder α]
    (P : SinglePeakedProfile V α) (m : α) : Prop :=
  ∀ b, b ≠ m →
    Fintype.card V < 2 * (Finset.univ.filter fun v => P.utility v b < P.utility v m).card

/-- **Median voter theorem.** With an odd number of voters, a median of the
peaks of a strictly single-peaked profile is a Condorcet winner. -/
theorem isCondorcetWinner_of_median {V α : Type*} [Fintype V] [LinearOrder α]
    (P : SinglePeakedProfile V α) (hodd : Odd (Fintype.card V)) {m : α}
    (hle : Fintype.card V ≤ 2 * (Finset.univ.filter fun v => P.peak v ≤ m).card)
    (hge : Fintype.card V ≤ 2 * (Finset.univ.filter fun v => m ≤ P.peak v).card) :
    P.IsCondorcetWinner m := by
  intro b hb
  rcases lt_or_gt_of_ne hb with hbm | hmb
  · have hsub : Finset.univ.filter (fun v => m ≤ P.peak v) ⊆
        Finset.univ.filter (fun v => P.utility v b < P.utility v m) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact P.lt_of_lt_of_le_peak v b m hbm hv
    have hcard := Finset.card_le_card hsub
    rcases hodd with ⟨k, hk⟩
    omega
  · have hsub : Finset.univ.filter (fun v => P.peak v ≤ m) ⊆
        Finset.univ.filter (fun v => P.utility v b < P.utility v m) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact P.lt_of_peak_le_of_lt v m b hv hmb
    have hcard := Finset.card_le_card hsub
    rcases hodd with ⟨k, hk⟩
    omega

end SinglePeakedProfile

end MathlibExt.GameTheory.SocialChoice
