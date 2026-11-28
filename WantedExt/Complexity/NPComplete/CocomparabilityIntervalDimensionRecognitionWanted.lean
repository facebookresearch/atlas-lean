/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF CO-COMPARABILITY GRAPHS OF POSETS OF INTERVAL DIMENSION d is NP-complete

Source:
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036;
M. Habib, D. Kelly and R. H. Möhring, "Interval dimension is a comparability invariant",
Discrete Mathematics 88 (1991), 211-229, doi:10.1016/0012-365X(91)90010-Y;
H. L. Bodlaender, T. Kloks, D. Kratsch and H. Müller, "Treewidth and minimum fill-in on
d-trapezoid graphs", Journal of Graph Algorithms and Applications 2(5) (1998), 1-23,
doi:10.7155/jgaa.00008 (Theorem 14 and the remarks after it);
ISGCI, class "co-comparability graphs of posets of interval dimension d" (gc_905), problem
Recognition.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition

/-!
# RECOGNITION OF CO-COMPARABILITY GRAPHS OF POSETS OF INTERVAL DIMENSION d is NP-complete

For a fixed integer `d ≥ 3`: INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` the
co-comparability graph of a poset of interval dimension at most `d`, i.e. is the complement of
`G` the comparability graph of such a poset?

An interval order on `V` is a strict order `<` for which each vertex `v` has a closed real
interval `[l v, h v]` (`l v ≤ h v`) with `u < v` exactly when the interval of `u` lies entirely
to the left of the interval of `v`, i.e. `h u < l v`. The interval dimension of a poset `P` is
the least number of interval orders whose intersection is `P`; it is at most `d` when some
`k ≤ d` interval orders on `V` have `P` as their intersection (`HasIntervalDimensionAtMost`).
The comparability graph of a strict partial order `r` joins two distinct vertices exactly when
they are comparable under `r` (as in `ComparabilityGraphSandwich.IsComparabilityGraph`, here
with the order named), and the co-comparability graph is its complement (Mathlib's `Gᶜ`).
These graphs are the `d`-trapezoid graphs (Bodlaender, Kloks, Kratsch and Müller 1998,
Theorem 14: "The d-trapezoid graphs are exactly the cocomparability graphs of partially ordered
sets of interval dimension at most d"; ISGCI lists the two classes as equivalent).

Bodlaender, Kloks, Kratsch and Müller (1998, Section 1): "the recognition problem for
d-trapezoid graphs is NP-complete for any fixed d ≥ 3 [Yannakakis 1982]"; Section 3: "the
problem 'Given a partially ordered set P, decide whether the interval dimension of P is at most
d' is NP-complete for any fixed d ≥ 3". The graph version follows because interval dimension is
a comparability invariant (Habib, Kelly and Möhring 1991) and comparability graphs can be
recognized in polynomial time. For `d ≤ 2` the classes are the interval graphs and the trapezoid
graphs, which are recognizable in polynomial time, so the theorem assumes `d ≥ 3`.

The graph is given by an edge list on `Fin n`. Isolated vertices do not change the answer (a
vertex adjacent to no other vertex can be placed above all others, with an interval to the right
of every other interval in each interval order), so the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF CO-COMPARABILITY GRAPHS OF POSETS OF INTERVAL DIMENSION d is
NP-complete.** For every fixed `d ≥ 3`, deciding whether a graph is the co-comparability graph
of a poset of interval dimension at most `d` (a `d`-trapezoid graph) is NP-complete. Source:
Yannakakis (1982); Habib, Kelly and Möhring (1991); Bodlaender, Kloks, Kratsch and Müller
(1998); ISGCI gc_905. -/
public theorem_wanted cocomparabilityIntervalDimensionRecognition_npComplete (d : ℕ)
    (_hd : 3 ≤ d) :
    cocomparabilityIntervalDimensionRecognitionDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (cocomparabilityIntervalDimensionRecognitionDec d)

end MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition
