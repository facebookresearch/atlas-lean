/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The fourth positive element in the greedy `B_h`-set

Statements from Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth
Positive Element in the Greedy `B_h`-Set", *Journal of Integer
Sequences* 27 (2024), Article 24.7.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/OBryant2/obryant4.html>).

The greedy choice is expressed stage by stage with MathlibExt's
canonical `AdditiveCombinatorics.IsBhSet`, using the paper's known
terms `a₀(h) = 0`, `a₁(h) = 1`, `a₂(h) = h + 1`, and
`a₃(h) = h² + h + 1`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.Additive.BhSet

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.GreedyBhFourthWanted

/-- `a` is the next greedy choice after the finite set `A`: it is
greater than every element of `A`, adjoining it preserves the
`B_h` property, and no smaller integer greater than every element
of `A` has that property. -/
def IsNextGreedyBh (h : ℕ) (A : Set ℕ) (a : ℕ) : Prop :=
  (∀ x ∈ A, x < a) ∧ AdditiveCombinatorics.IsBhSet (insert a A) h ∧
    ∀ b : ℕ, (∀ x ∈ A, x < b) → b < a →
      ¬AdditiveCombinatorics.IsBhSet (insert b A) h

/-- `a` is the fourth positive element `a₄(h)` of the greedy
`B_h`-set, with the preceding greedy stages and their known values
spelled out. -/
def IsFourthGreedyBh (h a : ℕ) : Prop :=
  IsNextGreedyBh h {0} 1 ∧
    IsNextGreedyBh h {0, 1} (h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1} (h ^ 2 + h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1, h ^ 2 + h + 1} a

/-- The piecewise value in the paper. The divisions are exact in
the parity cases shown. -/
def fourthValue (h : ℕ) : ℕ :=
  if Odd h then (h ^ 3 + 3 * h ^ 2 + 3 * h + 1) / 2
  else (h ^ 3 + 2 * h ^ 2 + 3 * h + 2) / 2

/-- Nathanson and O'Bryant's Theorem 1: the fourth positive greedy
`B_h` term is the displayed quasipolynomial.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Theorem 1. -/
theorem_wanted isFourthGreedyBh_fourthValue
    (h : ℕ) (hh : 0 < h) :
    IsFourthGreedyBh h (fourthValue h)

/-- Nathanson and O'Bryant's Lemma 2 (their TeX label
`Bhlemma1`): the displayed lower bound for the fourth greedy term,
for `h ≥ 2`.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Lemma 2. -/
theorem_wanted fourthValue_le_of_isFourthGreedyBh
    (h a : ℕ) (hh : 2 ≤ h) (ha : IsFourthGreedyBh h a) :
    fourthValue h ≤ a

/-- Nathanson and O'Bryant's Lemma 3 (their TeX label
`Bhlemma2`): the displayed upper bound for the fourth greedy term,
for positive `h`.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Lemma 3. -/
theorem_wanted isFourthGreedyBh_le_fourthValue
    (h a : ℕ) (hh : 0 < h) (ha : IsFourthGreedyBh h a) :
    a ≤ fourthValue h

end MathlibExt.Combinatorics.GreedyBhFourthWanted
