/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMBINATORIAL AUCTION WINNER DETERMINATION is NP-complete

Source:
M. H. Rothkopf, A. Pekeč and R. M. Harstad, "Computationally manageable combinational
auctions", Management Science 44(8) (1998), 1131-1147, doi:10.1287/mnsc.44.8.1131;
T. Sandholm, "Algorithm for optimal winner determination in combinatorial auctions",
Artificial Intelligence 135(1-2) (2002), 1-54, doi:10.1016/S0004-3702(01)00159-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDeterminationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination

/-!
# COMBINATORIAL AUCTION WINNER DETERMINATION is NP-complete

INSTANCE: a finite set `M` of items, a collection of bids `(S_j, p_j)`, each a set `S_j ⊆ M` of
items with a price `p_j ∈ ℤ₀⁺`, and an integer `K`. QUESTION: is there a set of pairwise
disjoint bids (no item is in two accepted bids) whose total price is at least `K`?

Items are `0, ..., m - 1`. Bids are listed and referred to by their position, so two bidders may
place equal bids; a bid's item set is a duplicate-free list. Accepted bids are a `Finset` of
positions whose item sets are pairwise disjoint in Mathlib's `Set.PairwiseDisjoint` sense.
Prices and `K` are natural numbers in binary; `K = 0` is a trivial yes-instance (accept no bid).
SET PACKING ([SP3], `SetPackingWanted`) reduces to the unit-price case: after removing repeated
sets (`SetPackingWanted` selects distinct sets, while equal bids here are distinct positions and
two empty bids are disjoint), give every set price `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMBINATORIAL AUCTION WINNER DETERMINATION is NP-complete.** Source: Rothkopf, Pekeč and
Harstad (1998); Sandholm (2002). -/
public theorem_wanted combinatorialAuctionWinnerDetermination_npComplete :
    combinatorialAuctionWinnerDeterminationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L combinatorialAuctionWinnerDeterminationDec

end MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination
