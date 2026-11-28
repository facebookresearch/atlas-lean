/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSPLITTABLE FLOW is NP-complete

Source:
J. M. Kleinberg, "Single-source unsplittable flow", in *Proceedings of the 37th Annual
Symposium on Foundations of Computer Science*, IEEE (1996), 68-77,
doi:10.1109/SFCS.1996.548465 (the single-source unsplittable flow problem, "a natural, NP-hard
generalization" of the single-source disjoint paths problem);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM UNSPLITTABLE FLOW.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnsplittableFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow

/-!
# UNSPLITTABLE FLOW is NP-complete

INSTANCE: a graph `G = (V, E)` with edge capacities `c : E → ℤ⁺`, a source vertex `s`, sinks
`t₁, …, t_k` with positive integer demands `ρ₁, …, ρ_k` such that `ρ_i ≤ c(e)` for all `e ∈ E`
and `i`, and a positive integer `K`.
The sinks are distinct vertices (one demand per sink), each different from `s`.
QUESTION: is there a single `s`-`t_i` flow path for each commodity `i` such that
`max_{e ∈ E} f(e) / c(e) ≤ K`, where `f(e)` is the total demand of the commodities whose paths
use `e`?

This is the decision version of MINIMUM UNSPLITTABLE FLOW in the Crescenzi-Kann compendium,
the single-source unsplittable flow problem of Kleinberg: "each terminal t_i has a demand ρ_i ≤ 1,
and each edge e of G has a capacity c_e ≥ 1. The problem is to decide whether one can choose a
single s-t_i path for each i, so that the resulting set of paths respects the capacity
constraints", which he calls NP-hard; with `K = 1` the question here is that one. A
certificate is the list of paths.

Demands are positive, as Kleinberg's are; the compendium allows demand `0`, and such a commodity
only asks that its sink be reachable from `s`. Since every capacity is positive,
`f(e) / c(e) ≤ K` is stated as `f(e) ≤ K · c(e)`. The graph
is given as a list of edges `(u, v, c)`, at most one per unordered pair, and the commodities as a
list of pairs `(t_i, ρ_i)`; paths are Mathlib's `SimpleGraph.Path`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNSPLITTABLE FLOW is NP-complete.** Source: Kleinberg (1996); Crescenzi and Kann,
MINIMUM UNSPLITTABLE FLOW. -/
public theorem_wanted unsplittableFlow_npComplete :
    unsplittableFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsplittableFlowDec

end MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow
