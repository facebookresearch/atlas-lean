/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS OUT is NP-complete

Source:
T. Ishibashi, R. Yoshinaka and A. Shinohara, "BusOut is NP-complete", arXiv:2505.09165 (2025),
Section 2 and Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BusOutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusOut

/-!
# BUS OUT is NP-complete

Ishibashi, Yoshinaka and Shinohara (Section 2) formalize the smartphone game Bus Out. A
configuration `(G, Q, S)` consists of a congestion graph `G`, whose vertices are the buses in
traffic, each labeled with a color and a capacity, with an edge from a bus to each bus that
blocks it (a bus is free when its out-degree is zero); a passenger queue `Q`, a sequence of
colors; and a spot occupancy state `S`, whose entries are the parking spots, each empty (`ε`) or
holding a bus `(x, k)` of color `x` with `k` remaining seats. A configuration can move to
`(G', Q', S')` when
* (dispatch) `Q' = Q`, `G'` is `G` minus a free vertex labeled `(x, k)`, and `S'` is `S` with
  an `ε` replaced by `(x, k)`; or
* (board) `G' = G`, `Q'` is `Q` with its first element `x` removed, and `S'` is `S` with an
  element `(x, k + 1)` replaced by `(x, k)` for some `k ≥ 1`, or `(x, 1)` replaced by `ε`;
and whenever a board move is applicable it takes place before the player dispatches a bus.
A configuration is solvable if some sequence of moves empties it (no buses in traffic, no
passengers, all spots empty). The instances of BUSOUT are the eligible configurations (`G` has
no cycle, and for every color the total capacity of its buses equals its number of passengers)
whose spot state is `εˢ`, `s` empty spots; capacities and `s` are positive integers.

INSTANCE: an eligible configuration `(G, Q, εˢ)`.
QUESTION: is it solvable? (NP-complete already for one spot, two colors and capacity `1`,
Theorem 2.)

The buses are `Fin n`, given by their labels `(color, capacity)`; a pair `(u, v)` in the edge
list means that bus `v` blocks bus `u`. Colors are natural numbers. A state records the set of
buses still in traffic, the remaining queue (first passenger first), and the `s` spots.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BUS OUT is NP-complete.** Source: Ishibashi, Yoshinaka and Shinohara (2025), Theorem 2. -/
public theorem_wanted busOut_npComplete :
    busOutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L busOutDec

end MetaMathlibExt.Complexity.NPComplete.BusOut
