/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMBINATORIAL AUCTION WINNER DETERMINATION: definitions

Source:
M. H. Rothkopf, A. Pekeč and R. M. Harstad, "Computationally manageable combinational
auctions", Management Science 44(8) (1998), 1131-1147, doi:10.1287/mnsc.44.8.1131;
T. Sandholm, "Algorithm for optimal winner determination in combinatorial auctions",
Artificial Intelligence 135(1-2) (2002), 1-54, doi:10.1016/S0004-3702(01)00159-X.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Pairwise.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination

/-- An instance: the number of items `m`, the bids `(items, price)`, and the bound `K`. -/
abbrev CombinatorialAuctionWinnerDeterminationInstance := ℕ × List (List ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every bid lists distinct items, all below `m`. -/
def WellFormed (i : CombinatorialAuctionWinnerDeterminationInstance) : Prop :=
  ∀ b ∈ i.2.1, b.1.Nodup ∧ ∀ x ∈ b.1, x < i.1

/-- Some set `W` of bid positions has pairwise disjoint item sets and total price at least
`K`. -/
def CombinatorialAuctionWinnerDeterminationFeasible
    (i : CombinatorialAuctionWinnerDeterminationInstance) : Prop :=
  ∃ W : Finset (Fin i.2.1.length),
    (W : Set (Fin i.2.1.length)).PairwiseDisjoint (fun j => (i.2.1.get j).1.toFinset) ∧
      i.2.2 ≤ ∑ j ∈ W, (i.2.1.get j).2

open Classical in
/-- COMBINATORIAL AUCTION WINNER DETERMINATION as a decision problem over bitstrings. -/
noncomputable def combinatorialAuctionWinnerDeterminationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CombinatorialAuctionWinnerDeterminationInstance) x with
  | some i => decide (WellFormed i ∧ CombinatorialAuctionWinnerDeterminationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination
