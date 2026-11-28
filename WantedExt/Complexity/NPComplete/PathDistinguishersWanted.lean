/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH DISTINGUISHERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT60] PATH DISTINGUISHERS;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Report CU-CS-092-76,
Department of Computer Science, University of Colorado, Boulder (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathDistinguishersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathDistinguishers

/-!
# PATH DISTINGUISHERS is NP-complete

Given an acyclic directed graph `G = (V, A)`, specified vertices `s, t ∈ V`, and a positive
integer `K ≤ |A|`, is there a subset `A' ⊆ A` with `|A'| ≤ K` such that, for any pair `p₁, p₂`
of directed paths from `s` to `t` in `G`, `p₁` and `p₂` are identical if and only if they
contain the same arcs of `A'`?

The digraph has vertices `Fin n` and is given by its arc list, with no loops and no multiple
arcs; acyclicity (no vertex reaches itself by a nonempty sequence of arcs) is part of
`WellFormed`. A directed path from `s` to `t` is a list of vertices without repetitions that
starts at `s`, ends at `t`, and has an arc from each vertex to the next; its arcs are the
consecutive pairs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATH DISTINGUISHERS is NP-complete.** Source: Garey and Johnson (1979), [GT60];
Maheshwari (1976). -/
public theorem_wanted pathDistinguishers_npComplete :
    pathDistinguishersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathDistinguishersDec

end MetaMathlibExt.Complexity.NPComplete.PathDistinguishers
