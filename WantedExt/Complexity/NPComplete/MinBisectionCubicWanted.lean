/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BISECTION on 3-regular graphs is NP-complete

Source:
T. N. Bui, S. Chaudhuri, F. T. Leighton and M. Sipser, "Graph bisection algorithms with good
average case behavior", Combinatorica 7(2) (1987), 171-191, doi:10.1007/BF02579448;
L. Lichev and D. Mitsche, "On the minimum bisection of random 3-regular graphs", The Electronic
Journal of Combinatorics 30(2) (2023), doi:10.37236/11085, Section 1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO BOUNDED SETS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinBisectionWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinBisectionCubic

open MinBisection (MinBisectionInstance MinBisectionFeasible)

/-!
# MINIMUM BISECTION on 3-regular graphs is NP-complete

INSTANCE: a 3-regular graph `G = (V, E)` (every vertex has degree exactly `3`; then `|V|` is
even) and a bound `K`.
QUESTION: is there a partition of `V` into two sets of `|V| / 2` vertices each with at most `K`
edges joining the two sets?

This is MINIMUM BISECTION (`MinBisectionWanted`; the `B = |V| / 2`, unit-weight case of
[ND17]) restricted to `d`-regular graphs with `d = 3`. Bui, Chaudhuri, Leighton and Sipser
prove the bisection problem NP-complete for 3-regular graphs; Lichev and Mitsche (Section 1)
record that finding a minimum bisection "is well known to be NP-complete in general and even
in the particular case of 3-regular graphs", citing them. Restricting to the smallest degree
for which hardness is proved gives the strongest statement; hardness on all regular graphs
follows by inclusion.

The instance type and the question are reused from `MinBisectionWanted` (a simple edge list on
the vertices `0, …, n - 1` with `n` even, and a set `S` of `n / 2` vertices such that no `K + 1`
listed edges cross between `S` and its complement); only 3-regularity of the graph
(`Cslib.Complexity.Karp.edgeGraph`, Mathlib's `SimpleGraph.IsRegularOfDegree 3`) is added to
the well-formedness. A 3-regular graph has `3n / 2` edges, so the vertex count is bounded by
the input length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinBisectionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: well-formed for MINIMUM BISECTION (`n` even, a simple edge
list on `0, …, n - 1`), and the graph is 3-regular. -/
def WellFormed (i : MinBisectionInstance) : Prop :=
  MinBisection.WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- MINIMUM BISECTION on 3-regular graphs as a decision problem over bitstrings. -/
noncomputable def minBisectionCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinBisectionInstance) x with
  | some i => decide (WellFormed i ∧ MinBisectionFeasible i)
  | none => false

/-- **MINIMUM BISECTION on 3-regular graphs is NP-complete.** Source: Bui, Chaudhuri, Leighton
and Sipser (1987), as recorded by Lichev and Mitsche (2023); Garey and Johnson (1979), [ND17]. -/
public theorem_wanted minBisectionCubic_npComplete :
    minBisectionCubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minBisectionCubicDec

end MetaMathlibExt.Complexity.NPComplete.MinBisectionCubic
