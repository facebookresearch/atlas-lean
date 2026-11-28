/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-FACILITY LOCATION is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-FACILITY LOCATION;
G. Cornuéjols, M. L. Fisher, and G. L. Nemhauser, "Location of bank accounts to optimize
float: an analytic study of exact and approximate algorithms", Management Science 23 (1977),
789-810, doi:10.1287/mnsc.23.8.789.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KFacilityLocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityLocation

/-!
# K-FACILITY LOCATION is NP-complete

INSTANCE: a complete graph `G = (V, E)`, profits `p(vᵢ, vⱼ) ∈ ℕ`, an integer `k`, and a positive
integer `K`.
QUESTION: is there a set of `k` facilities, i.e. a subset `F ⊆ V` with `|F| = k`, such that the
total profit `∑_{v ∈ V} max_{f ∈ F} p(v, f)` is at least `K`?

This is the decision version of MAXIMUM K-FACILITY LOCATION from the Crescenzi-Kann compendium, the
bank-account location problem of Cornuéjols, Fisher and Nemhauser with the clients and the candidate
locations both identified with `V`: each vertex `v` collects the largest profit `p(v, f)` over the
open facilities `f ∈ F`. The total profit uses `p(v, f)` for every ordered pair, including `p(v, v)`
when `v ∈ F`, so the instance gives the profits as a `|V| × |V|` matrix, one row per vertex `v` (as
a client) and one column per vertex `f` (as a facility). As in the bank-account model, the matrix
need not be symmetric.

The maximum over `F` is `Finset.sup` (for `k = 0` the empty maximum is `0 < K`, a
no-instance). NP-hardness: DOMINATING SET is the special case `p(v, f) = 1` if `f = v` or `f` is
adjacent to `v`, `p(v, f) = 0` otherwise, and `K = |V|` (a dominating set of size at most
`k ≤ |V|` extends to one of size exactly `k`). Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **K-FACILITY LOCATION is NP-complete.** Source: Crescenzi and Kann, MAXIMUM K-FACILITY LOCATION;
Cornuéjols, Fisher, and Nemhauser (1977). -/
public theorem_wanted kFacilityLocation_npComplete :
    kFacilityLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kFacilityLocationDec

end MetaMathlibExt.Complexity.NPComplete.KFacilityLocation
