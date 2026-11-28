/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-CONTAINMENT FOR FREE B-SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 277, problem [PO18]
NON-CONTAINMENT FOR FREE B-SCHEMES (credited there to Fortune, Hopcroft, and
Schmidt, 1977; transformation from 3SAT);
S. Fortune, J. Hopcroft, and E. M. Schmidt, "The complexity of equivalence and
containment for free single variable program schemes", Automata, Languages and
Programming (ICALP 1978), Lecture Notes in Computer Science 62 (1978), 227-240,
doi:10.1007/3-540-08860-1_17.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NonContainmentForFreeBSchemesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonContainmentForFreeBSchemes

/-!
# NON-CONTAINMENT FOR FREE B-SCHEMES is NP-complete

INSTANCE: two free `B`-schemes `S₁` and `S₂`, where a free `B`-scheme is a rooted, directed
acyclic graph `G = (V, A)`, all of whose vertices have out-degree `0` (leaves) or `2` (tests),
with the two arcs leaving a test vertex labeled `L` and `R` respectively, together with a set
`B` of Boolean variable symbols and a label `l(v) ∈ B` for each test vertex, such that no two
test vertices on the same directed path get the same label, and a set `F` of function symbols
along with a label `l(v) ∈ F ∪ {Ω}` for each leaf in `V`. QUESTION: is `S₁` not "contained"
in `S₂`, i.e., is there an assignment `t : B₁ ∪ B₂ → {L, R}` such that if the paths from the
roots of `G₁` and `G₂` to leaf vertices determined by always leaving a test vertex `v` by the
arc labeled `t(l(v))` terminate at leaves labeled `f₁` and `f₂` respectively, then `f₁ ≠ f₂`
and `f₁ ≠ Ω`?

Representation. A scheme is a list of vertices `0, ..., |V| - 1` with root `0`. A vertex is
`(true, b, l, r)`, a test labeled with the variable symbol `b` whose `L`-arc goes to `l` and
whose `R`-arc goes to `r`, or `(false, f, 0, 0)`, a leaf labeled `f`, where the function symbols
are the positive numbers and `0` is `Ω`. Both schemes draw their symbols from `ℕ`, so a symbol
used in both is the same symbol. "Rooted" means that every vertex is reachable from the root.
An assignment is `t : ℕ → Bool` with `true` for `L` (its values off `B₁ ∪ B₂` are irrelevant).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NON-CONTAINMENT FOR FREE B-SCHEMES is NP-complete.** Source: Garey and Johnson (1979),
[PO18]; Fortune, Hopcroft, and Schmidt (1978). -/
public theorem_wanted nonContainmentForFreeBSchemes_npComplete :
    nonContainmentForFreeBSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonContainmentForFreeBSchemesDec

end MetaMathlibExt.Complexity.NPComplete.NonContainmentForFreeBSchemes
