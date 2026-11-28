/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF INTERVAL FILAMENT GRAPHS is NP-complete

Source:
M. Pergel, "Recognition of polygon-circle graphs and graphs of interval filaments is
NP-complete", Graph-Theoretic Concepts in Computer Science (WG 2007), LNCS 4769 (2007), 238-247,
doi:10.1007/978-3-540-74839-7_23;
F. Gavril, "Maximum weight independent sets and cliques in intersection graphs of filaments",
Information Processing Letters 73 (2000), 181-188, doi:10.1016/S0020-0190(00)00025-9 (the class).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntervalFilamentGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalFilamentGraphRecognition

/-!
# RECOGNITION OF INTERVAL FILAMENT GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` an interval filament graph (ISGCI `gc_390`), i.e.
"the intersection graph of continuous non-negative functions defined on closed intervals with
zero-values on their endpoints"? Pergel (2007) proved recognition of this class NP-complete.

The graph is given by an edge list on `Fin n`. The filament of a vertex `v` is the graph
`{(x, f v x) | x ∈ [a v, b v]}` of a function `f v : ℝ → ℝ` that is continuous on the closed
interval `[a v, b v]` (`ContinuousOn`), non-negative there, and zero at `a v` and `b v`; values of
`f v` outside the interval are irrelevant. The interval is non-degenerate, `a v < b v`, as in
ISGCI's equivalent description ("a curve `cᵢ` connecting its two endpoints, such that `cᵢ` remains
within the limits of `i`"); a point filament `(a, 0)` would not enlarge the class, since a small
bump around `a` meets the same filaments. Two filaments intersect exactly when there is a common
abscissa `x` in both intervals with `f u x = f v x`.

Membership in NP is part of Pergel's theorem. Isolated vertices do not change the answer (each is
a small filament over an interval to the right of all others), so a model of the subgraph on the
vertices that occur in edges decides the instance, and the binary vertex count does not make the
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

/-- **RECOGNITION OF INTERVAL FILAMENT GRAPHS is NP-complete.** Source: Pergel (2007). -/
public theorem_wanted intervalFilamentGraphRecognition_npComplete :
    intervalFilamentGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intervalFilamentGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.IntervalFilamentGraphRecognition
