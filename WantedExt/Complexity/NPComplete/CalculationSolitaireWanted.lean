/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED CALCULATION SOLITAIRE is NP-complete

Source:
C. Iwamoto and T. Ide, "Calculation Solitaire is NP-complete", IEICE Transactions on
Information and Systems E106-D (2023), 328-332, doi:10.1587/transinf.2022FCL0002, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire

/-!
# GENERALIZED CALCULATION SOLITAIRE is NP-complete

Calculation is a solitaire card game (Iwamoto and Ide, Section 1). The generalized
`(s × k)`-card deck has `s` suits of `k` ranks `1, …, k`, where `k` is prime; suits play no
role. The `i`-foundation (`1 ≤ i ≤ s`) starts with a card `i` and is built up by `i`s until a
card `k` is reached, a card of rank `r` being usable as a card of rank `r + k j`: its cards are,
in order, the ranks congruent to `i, 2i, 3i, …, ki` modulo `k`, the last one being `k`. The
player moves (i) the top card of the stock either onto a foundation or to the top of a tableau
pile, or (ii) the top card of a tableau pile onto a foundation.

INSTANCE: a mid-play configuration of the generalized game: `s` foundations, at most `s`
tableau piles, and a stock.
QUESTION: can the player move all cards of the stock and the tableau piles to the foundations?
(Iwamoto and Ide prove this NP-complete, Theorem 1.)

A foundation is determined by its number of cards `h` (`1 ≤ h ≤ k`): the `t`-th card of the
`i`-foundation has rank `card k i t`, the rank in `1, …, k` congruent to `i t` modulo `k`. Its
next card is `card k i (h + 1)` while `h < k`. The tableau piles and the stock are lists of
ranks, top card first. The configuration lists exactly `s` piles, empty ones included, so that
every pile of the game is available (at most `s` of them hold cards). The steps `1, …, s` are
invertible modulo `k` because `s < k` (implicit in the source: otherwise a foundation could not
be built up to `k`). The configuration uses exactly the deck: every rank `1, …, k` occurs `s`
times in total on the foundations, the tableau piles and the stock.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **GENERALIZED CALCULATION SOLITAIRE is NP-complete.** Source: Iwamoto and Ide (2023),
Theorem 1. -/
public theorem_wanted calculationSolitaire_npComplete :
    calculationSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L calculationSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire
