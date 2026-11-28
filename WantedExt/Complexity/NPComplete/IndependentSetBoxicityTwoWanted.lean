/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on boxicity-2 graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
C. S. Rim and K. Nakajima, "On rectangle intersection and overlap graphs", IEEE Transactions on
Circuits and Systems I: Fundamental Theory and Applications 42(9) (1995), 549-553,
doi:10.1109/81.414831.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetBoxicityTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetBoxicityTwo

/-!
# INDEPENDENT SET on boxicity-2 graphs is NP-complete

INSTANCE: a graph `G = (V, E)` of boxicity at most 2, i.e. the intersection graph of a family of
axis-parallel rectangles in the plane, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to the ISGCI class "boxicity 2" (`gc_239`): graphs
with an intersection model consisting of axis-parallel boxes in the plane. The class is
`BoxicityTwo.BoxicityTwoFeasible` from `WantedExt.Complexity.NPComplete.BoxicityTwoWanted`, applied
to the vertex count and edge list (vertex `v` gets a nonempty closed rectangle
`Set.Icc (lo v) (hi v)` of `ℝ × ℝ`, and two distinct vertices are adjacent exactly when their
rectangles intersect), and the simple-edge-list condition is `BoxicityTwo.WellFormed`. The
rectangle model is not part of the input.

Rim and Nakajima prove that the maximum independent set problem is NP-hard even for cubic planar
rectangle intersection graphs (isooriented rectangles, adjacent when they intersect); their
reduction outputs rectangle intersection graphs, so it is a reduction to this problem.
Membership in NP: the certificate is `V'` together with a rectangle model; the coordinates can
be replaced by their ranks among the `4|V|` rectangle endpoints without changing which
rectangles intersect, so the model has polynomial size and is checked in polynomial time.

The instance, the graph and the question follow
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`: a vertex count `n`
(vertices `Fin n`), an edge list and the bound `K`; the independent set is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET on boxicity-2 graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20];
Rim and Nakajima (1995). -/
public theorem_wanted independentSetBoxicityTwo_npComplete :
    independentSetBoxicityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetBoxicityTwoDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetBoxicityTwo
