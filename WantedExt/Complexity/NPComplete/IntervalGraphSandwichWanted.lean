/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL GRAPH SANDWICH is NP-complete

Source:
M. C. Golumbic and R. Shamir, "Complexity and algorithms for reasoning about time: a
graph-theoretic approach", Journal of the ACM 40 (1993), 1108-1133, doi:10.1145/174147.169675
("the interval graph sandwich problem is introduced, and is shown to be NP-complete");
M. C. Golumbic, H. Kaplan, and R. Shamir, "On the complexity of DNA physical mapping",
Advances in Applied Mathematics 15 (1994), 251-261, doi:10.1006/aama.1994.1009.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntervalGraphSandwichDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalGraphSandwich

open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-!
# INTERVAL GRAPH SANDWICH is NP-complete

INSTANCE: graphs `G₁ = (V, E₁)` and `G₂ = (V, E₂)` on the same vertex set with `E₁ ⊆ E₂`.
QUESTION: is there an interval graph `G = (V, E)` with `E₁ ⊆ E ⊆ E₂`?

`E₁` holds the edges that must be present and `E₂ - E₁` the optional ones. The sandwich graph
`G` is a `SimpleGraph` `H` on the same vertices with `G₁ ≤ H ≤ G₂`. Interval graphs are
`IsIntervalGraph` from `WantedExt.Complexity.NPComplete.IntervalGraphCompletionWanted`: closed
real intervals `[l v, r v]`, one per vertex, such that two distinct vertices are adjacent
exactly when their intervals intersect.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTERVAL GRAPH SANDWICH is NP-complete.** Source: Golumbic and Shamir (1993); Golumbic,
Kaplan, and Shamir (1994). -/
public theorem_wanted intervalGraphSandwich_npComplete :
    intervalGraphSandwichDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intervalGraphSandwichDec

end MetaMathlibExt.Complexity.NPComplete.IntervalGraphSandwich
