/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITY REPRESENTATIVES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM CAPACITY
REPRESENTATIVES;
M. Bellare, "Interactive proofs and approximation: reductions from two provers in one round",
Proceedings of the 2nd Israel Symposium on Theory and Computing Systems (ISTCS 1993), 266-274,
doi:10.1109/ISTCS.1993.253462.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CapacityRepresentativesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

/-!
# CAPACITY REPRESENTATIVES is NP-complete

INSTANCE: disjoint sets `S₁, ..., S_m` and, for any `i ≠ j`, `x ∈ Sᵢ` and `y ∈ S_j`, a
nonnegative capacity `c(x, y)`; a positive integer `K`. QUESTION: is there a system of
representatives `T`, i.e. a set `T` with `|T ∩ Sᵢ| = 1` for every `i`, whose capacity
`∑_{x, y ∈ T} c(x, y)` is at least `K`?

This is the decision version of Crescenzi and Kann's MAXIMUM CAPACITY REPRESENTATIVES,
whose entry records that it "does not admit a PTAS" (Bellare), so the decision version is
NP-hard. It contains MAX CUT directly: for a graph with edge weights `w`, take
`S_v = {v⁰, v¹}` for every vertex `v` and `c(uᵃ, vᵇ) = w(uv)` when `uv` is an edge and `a ≠ b`
(else `0`); a system of representatives is a 2-coloring, and its capacity is twice the weight of
the cut. Membership in NP: `T` is a certificate.

The elements are `0, ..., N - 1` and the capacities are an `N × N` matrix of natural numbers
(nonnegative) given as a list of rows, entry `c(x, y)` in row `x` and column `y`; entries for
two elements of the same set are never used. The sets `S₁, ..., S_m` are lists of elements,
duplicate-free and pairwise disjoint (the concatenation has no duplicates). Since the sets are
disjoint, a system of representatives is a choice of one element `tᵢ ∈ Sᵢ` for every `i` (a list
`t` with `t[i] ∈ Sᵢ`), and `∑_{x, y ∈ T} c(x, y)` is the sum of `c(tᵢ, t_j)` over the ordered
pairs `i ≠ j` (`c(x, y)` is given only for elements of different sets).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CAPACITY REPRESENTATIVES is NP-complete.** Source: Crescenzi and Kann, MAXIMUM CAPACITY
REPRESENTATIVES; Bellare (1993). -/
public theorem_wanted capacityRepresentatives_npComplete :
    capacityRepresentativesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacityRepresentativesDec

end MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives
