/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TARGET SET SELECTION is NP-complete

Source:
P. A. Dreyer Jr. and F. S. Roberts, "Irreversible k-threshold processes: graph-theoretical
threshold models of the spread of disease and of opinion", Discrete Applied Mathematics 157(7)
(2009), 1615-1627, doi:10.1016/j.dam.2008.09.012;
N. Chen, "On the approximability of influence in social networks", SIAM Journal on Discrete
Mathematics 23(3) (2009), 1400-1415, doi:10.1137/08073617X;
J. Kynčl, B. Lidický and T. Vyskočil, "Irreversible 2-conversion set in graphs of bounded
degree", Discrete Mathematics & Theoretical Computer Science 19(3) (2017),
doi:10.23638/DMTCS-19-3-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TargetSetSelectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TargetSetSelection

/-!
# TARGET SET SELECTION is NP-complete

INSTANCE: a graph `G = (V, E)`, a threshold `t(v) ∈ {1, 2, …}` for every vertex `v`, and a
positive integer `K ≤ |V|`.

QUESTION: is there a target set `S ⊆ V` with `|S| ≤ K`, that is, a set whose activation activates
every vertex in the following irreversible process: initially the vertices of `S` are active, and
in each round every vertex `v` with at least `t(v)` active neighbors becomes active?

Active vertices stay active, so the active sets grow; while the process has not stopped, each
round activates a new vertex, so after `|V|` rounds the active set is the final one. Kynčl,
Lidický and Vyskočil (2017, Section 1) define the irreversible `k`-threshold process (every vertex
has threshold `k`) and the decision problem "Input: a graph G and a positive integer s. Output:
YES if there exists an irreversible k-conversion set of size s in G", and record that Dreyer and
Roberts proved it NP-complete for every fixed `k ≥ 3` (by a reduction from INDEPENDENT SET) and
that the case `k = 2` was first proved NP-complete by Chen (2009).
These are the instances with constant thresholds; general positive thresholds, as in TARGET SET
SELECTION, include them (and a superset of a target set is a target set, so "size `s`" and "size
at most `s`" agree for `s ≤ |V|`). Membership in NP: `S` is a certificate, checked by running
the process for `|V|` rounds. `K ≤ |V|` follows the convention of Garey and Johnson: for
`K ≥ |V|` the answer is trivially yes.

The graph is given by a vertex count `n` (vertices `Fin n`) and an edge list, as
`Cslib.Complexity.Karp.edgeGraph`, and the thresholds by a list of length `n`. The active set after
`k` rounds is `activated i S k`; the number of active neighbors of `v` is the `Set.ncard` of the
active part of Mathlib's `SimpleGraph.neighborSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TARGET SET SELECTION is NP-complete.** Source: Dreyer and Roberts (2009); Chen (2009);
Kynčl, Lidický and Vyskočil (2017). -/
public theorem_wanted targetSetSelection_npComplete :
    targetSetSelectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L targetSetSelectionDec

end MetaMathlibExt.Complexity.NPComplete.TargetSetSelection
