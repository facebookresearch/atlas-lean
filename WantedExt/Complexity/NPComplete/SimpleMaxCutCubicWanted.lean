/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on cubic graphs is NP-complete

Source:
P. Berman and M. Karpinski, "On some tighter inapproximability results (extended abstract)",
Automata, Languages and Programming (ICALP 1999), LNCS 1644 (1999), 200-209,
doi:10.1007/3-540-48523-6_17 (approximating MAX CUT on 3-regular graphs within some constant
factor below 1 is NP-hard);
J. Díaz and G. B. Mertzios, "Minimum bisection is NP-hard on unit disk graphs", Information and
Computation 256 (2017), 83-92, doi:10.1016/j.ic.2017.04.010, proof of Lemma 1 ("The Max-Cut
problem is NP-hard, even when restricted to cubic graphs, i.e. to graphs G = (V, E) where
|N(u)| = 3 for every vertex u ∈ V", citing M. Yannakakis, "Node- and edge-deletion NP-complete
problems", STOC 1978, 253-264, doi:10.1145/800133.804355).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimpleMaxCutCubicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCubic

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on cubic graphs is NP-complete

INSTANCE: a cubic graph `G = (V, E)` (every vertex has degree `3`) and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to cubic graphs. The
instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutDefs`, whose question counts edges), reused as in `SimpleMaxCutDegreeThreeWanted`,
which bounds degrees by `3`; here `Cslib.Complexity.Karp.edgeGraph` is cubic, Mathlib's
`IsRegularOfDegree 3` (every vertex has degree exactly `3`), and `0 < K`. Every vertex lies on
three edges, so `3 |V| = 2 |E|` and the binary vertex count does not make the problem succinct.

Hardness: Díaz and Mertzios record that MAX CUT is NP-hard on cubic graphs, citing Yannakakis;
Berman and Karpinski show moreover that approximating it on 3-regular graphs within some constant
factor below 1 is NP-hard. Membership in NP: a cut is a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMPLE MAX CUT on cubic graphs is NP-complete.** Source: Berman and Karpinski (1999);
Díaz and Mertzios (2017), citing Yannakakis (1978). -/
public theorem_wanted simpleMaxCutCubic_npComplete :
    simpleMaxCutCubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutCubicDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCubic
