/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Hamilton apportionment and the Alabama paradox

With total population `P > 0`, the quota of state `i` is `house * pop i / P`.
Euclidean division gives its lower quota and a remainder with common denominator `P`.
Thus integer comparisons suffice to rank the fractional parts exactly. The rule is a
relation: a tie across the last available seat need not be broken in a particular way.
-/

@[expose] public section

namespace MathlibExt.GameTheory.SocialChoice.Hamilton

variable {ι : Type*} [Fintype ι]

/-- For natural populations `pop` on finitely many states, the lower quota of state `i` is
`house * pop i` divided by the total population, rounded down. Natural division gives zero
when the total is zero; the apportionment rule itself requires a positive total. -/
def lowerQuota (pop : ι → ℕ) (house : ℕ) (i : ι) : ℕ :=
  house * pop i / (∑ j, pop j)

/-- For natural populations on finitely many states, the residue of `house * pop i` modulo
total population `P`. When `P > 0` this is the numerator of the fractional part of state `i`'s
quota over the common denominator `P`; natural remainder modulo zero returns the dividend. -/
def remainderNumerator (pop : ι → ℕ) (house : ℕ) (i : ι) : ℕ :=
  house * pop i % (∑ j, pop j)

variable [DecidableEq ι]

/-- For finitely many states with natural populations, a set qualifies for the extra seats
exactly when total population is positive, its size plus the sum of lower quotas equals the
house size, and every member's remainder is at least every nonmember's. Ties are allowed. -/
def IsAwardSet (pop : ι → ℕ) (house : ℕ) (awards : Finset ι) : Prop :=
  0 < ∑ i, pop i ∧
    (∑ i, lowerQuota pop house i) + awards.card = house ∧
    ∀ i ∈ awards, ∀ j ∉ awards, remainderNumerator pop house j ≤ remainderNumerator pop house i

/-- Given natural populations on finitely many states, a house size and any set of awardees,
assign each state its lower quota plus one seat if it belongs to the set, and just its lower
quota otherwise. -/
def seatsOfAwards (pop : ι → ℕ) (house : ℕ) (awards : Finset ι) (i : ι) : ℕ :=
  lowerQuota pop house i + if i ∈ awards then 1 else 0

/-- For finitely many states with natural populations, a seat vector is a Hamilton allocation
exactly when total population is positive and the vector assigns the lower quotas plus one seat
to each member of some set of the right size to fill the house, with no omitted remainder
strictly larger than a selected one. -/
def IsHamilton (pop : ι → ℕ) (house : ℕ) (a : ι → ℕ) : Prop :=
  ∃ awards, IsAwardSet pop house awards ∧ a = seatsOfAwards pop house awards

/-- Every Hamilton allocation of a house among finitely many states has total seat count
exactly equal to the house size; positive total population is part of `IsHamilton`. -/
theorem IsHamilton.sum_eq {pop : ι → ℕ} {house : ℕ} {a : ι → ℕ} (ha : IsHamilton pop house a) :
    ∑ i, a i = house := by
  obtain ⟨awards, ⟨_, hcard, _⟩, rfl⟩ := ha
  simpa [seatsOfAwards, Finset.sum_add_distrib] using hcard

/-- With populations `(6, 6, 2)` and ten seats, a seat vector is a Hamilton allocation if and
only if it is `(4, 4, 2)`: the third state alone receives a remainder seat. -/
theorem isHamilton_ten_iff (a : Fin 3 → ℕ) :
    IsHamilton ![6, 6, 2] 10 a ↔ a = ![4, 4, 2] := by
  have awards : ∀ s : Finset (Fin 3), IsAwardSet ![6, 6, 2] 10 s ↔ s = {2} := by
    unfold IsAwardSet
    decide
  have seats : seatsOfAwards ![6, 6, 2] 10 {2} = ![4, 4, 2] := by decide
  simp [IsHamilton, awards, seats]

/-- With populations `(6, 6, 2)` and eleven seats, a seat vector is a Hamilton allocation if
and only if it is `(5, 5, 1)`: both larger states receive a remainder seat. -/
theorem isHamilton_eleven_iff (a : Fin 3 → ℕ) :
    IsHamilton ![6, 6, 2] 11 a ↔ a = ![5, 5, 1] := by
  have awards : ∀ s : Finset (Fin 3), IsAwardSet ![6, 6, 2] 11 s ↔ s = {0, 1} := by
    unfold IsAwardSet
    decide
  have seats : seatsOfAwards ![6, 6, 2] 11 {0, 1} = ![5, 5, 1] := by decide
  simp [IsHamilton, awards, seats]

/-- A rule for fixed populations is house-monotone if every allowed allocation at each house
size has an allowed allocation with one more seat in which no state loses a seat. For a
rule with ties this only asks for some such successor, not that every successor work. -/
def IsHouseMonotone {σ : Type*} (rule : ℕ → (σ → ℕ) → Prop) : Prop :=
  ∀ ⦃house a⦄, rule house a → ∃ b, rule (house + 1) b ∧ ∀ i, a i ≤ b i

/-- For the fixed populations `(6, 6, 2)`, Hamilton apportionment is not house-monotone:
its ten-seat allocation `(4, 4, 2)` has no nondecreasing eleven-seat successor, since the
only eleven-seat allocation `(5, 5, 1)` gives the third state one seat instead of two. -/
theorem alabamaParadox : ¬ IsHouseMonotone (IsHamilton ![6, 6, 2]) := by
  intro mono
  obtain ⟨b, hb, hle⟩ := mono ((isHamilton_ten_iff _).2 rfl)
  obtain rfl := (isHamilton_eleven_iff b).1 hb
  exact (by decide : ¬ (2 : ℕ) ≤ 1) (hle 2)

end MathlibExt.GameTheory.SocialChoice.Hamilton
