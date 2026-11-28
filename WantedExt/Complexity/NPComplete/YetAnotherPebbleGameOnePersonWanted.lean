/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YET ANOTHER PEBBLE GAME (one-person version) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 397-411,
doi:10.1016/0196-6774(83)90019-6, problem [4] YET ANOTHER PEBBLE GAME, comment;
T. Kasai, A. Adachi and S. Iwata, "Classes of pebble games and complete problems", SIAM Journal
on Computing 8 (1979), 574-586, doi:10.1137/0208046.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.YetAnotherPebbleGameOnePersonDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.YetAnotherPebbleGameOnePerson

/-!
# YET ANOTHER PEBBLE GAME (one-person version) is NP-complete

Johnson's column states YET ANOTHER PEBBLE GAME on an acyclic directed graph `G = (V, A)` with a
distinguished goal vertex `v₀`, a set `S ⊆ V` of start vertices, and a collection `R` of rules,
each rule being a triple `(x, y, z)` of distinct vertices where `(x, z)` and `(y, z)` are both
arcs in `A`. Initially there is a pebble on each vertex in `S`; given a configuration of pebbles,
a rule `(x, y, z) ∈ R` is applicable if there are pebbles on `x` and `y` but not on `z`, and its
application moves the pebble from `x` to `z`. The two-person game is PSPACE-complete; the
column's comment: "The corresponding one-person game (can a single player pebble `v₀` by
starting from the initial position and repeatedly applying applicable rules?) is NP-complete"
(Kasai, Adachi and Iwata). This is the one-person game:

INSTANCE: an acyclic directed graph `G = (V, A)`, a goal vertex `v₀`, a set `S ⊆ V` of start
vertices, and a collection `R` of rules as above.
QUESTION: can a single player, starting with a pebble on each vertex of `S` and repeatedly
applying applicable rules, place a pebble on `v₀`?

The vertices are `0, …, n - 1`; arcs, the start set and rules are lists. `G` is acyclic when no
vertex reaches itself by a nonempty sequence of arcs (`Relation.TransGen`). A configuration is
the finite set of pebbled vertices, and the positions reachable from the initial one are those
of `Relation.ReflTransGen` of single rule applications.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **YET ANOTHER PEBBLE GAME (one-person version) is NP-complete.** Source: Johnson (1983),
problem [4], comment; Kasai, Adachi and Iwata (1979). -/
public theorem_wanted yetAnotherPebbleGameOnePerson_npComplete :
    yetAnotherPebbleGameOnePersonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yetAnotherPebbleGameOnePersonDec

end MetaMathlibExt.Complexity.NPComplete.YetAnotherPebbleGameOnePerson
