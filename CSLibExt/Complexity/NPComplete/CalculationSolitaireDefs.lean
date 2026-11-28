/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED CALCULATION SOLITAIRE: definitions

Source:
C. Iwamoto and T. Ide, "Calculation Solitaire is NP-complete", IEICE Transactions on
Information and Systems E106-D (2023), 328-332, doi:10.1587/transinf.2022FCL0002, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire

/-- An instance: the number of ranks `k`, the numbers of cards on the foundations (entry
`i - 1` for the `i`-foundation), the tableau piles and the stock (top card first). -/
abbrev CalculationSolitaireInstance := ℕ × List ℕ × List (List ℕ) × List ℕ

/-- The `t`-th card (`t ≥ 1`) of the `i`-foundation: the rank in `1, …, k` congruent to `i t`
modulo `k`. -/
def card (k i t : ℕ) : ℕ := (i * t - 1) % k + 1

/-- A position: the foundation sizes, the tableau piles and the stock. -/
abbrev Position := List ℕ × List (List ℕ) × List ℕ

/-- One move with `k` ranks: the top card of the stock onto a foundation or onto a tableau pile,
or the top card of a tableau pile onto a foundation. Foundation `idx` is the
`(idx + 1)`-foundation. -/
def Step (k : ℕ) (c c' : Position) : Prop :=
  (∃ x rest idx h, c.2.2 = x :: rest ∧ c.1[idx]? = some h ∧ h < k ∧
      x = card k (idx + 1) (h + 1) ∧ c' = (c.1.set idx (h + 1), c.2.1, rest)) ∨
    (∃ x rest j p, c.2.2 = x :: rest ∧ c.2.1[j]? = some p ∧
      c' = (c.1, c.2.1.set j (x :: p), rest)) ∨
    (∃ x p j idx h, c.2.1[j]? = some (x :: p) ∧ c.1[idx]? = some h ∧ h < k ∧
      x = card k (idx + 1) (h + 1) ∧ c' = (c.1.set idx (h + 1), c.2.1.set j p, c.2.2))

/-- The number of foundations holding a card of rank `r`. -/
def onFoundations (i : CalculationSolitaireInstance) (r : ℕ) : ℕ :=
  ((List.range i.2.1.length).filter fun idx =>
    (List.range' 1 (i.2.1.getD idx 0)).any fun t => card i.1 (idx + 1) t == r).length

/-- Well-formedness: `k` is prime, there are `s ≥ 1` foundations with `s < k`, each holding
between `1` and `k` cards, exactly `s` tableau piles (some possibly empty), all cards of the
tableau piles and the stock have ranks in `1, …, k`, and every rank occurs exactly `s` times in
the configuration. -/
def WellFormed (i : CalculationSolitaireInstance) : Prop :=
  i.1.Prime ∧ 0 < i.2.1.length ∧ i.2.1.length < i.1 ∧
    (∀ h ∈ i.2.1, 1 ≤ h ∧ h ≤ i.1) ∧ i.2.2.1.length = i.2.1.length ∧
    (∀ x ∈ i.2.2.1.flatten ++ i.2.2.2, 1 ≤ x ∧ x ≤ i.1) ∧
    ∀ r, 1 ≤ r → r ≤ i.1 →
      onFoundations i r + (i.2.2.1.flatten ++ i.2.2.2).count r = i.2.1.length

/-- Some sequence of moves empties the stock and every tableau pile. -/
def CalculationSolitaireFeasible (i : CalculationSolitaireInstance) : Prop :=
  ∃ f, Relation.ReflTransGen (Step i.1) (i.2.1, i.2.2.1, i.2.2.2)
    (f, List.replicate i.2.2.1.length [], [])

open Classical in
/-- GENERALIZED CALCULATION SOLITAIRE as a decision problem over bitstrings. -/
noncomputable def calculationSolitaireDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CalculationSolitaireInstance) x with
  | some i => decide (WellFormed i ∧ CalculationSolitaireFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire
