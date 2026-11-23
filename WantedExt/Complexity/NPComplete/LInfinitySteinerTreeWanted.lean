/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC STEINER TREE in the L∞ metric is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC STEINER TREE, p. 209
(comment: "Remains so if the distance measure is replaced by the L₁ "rectilinear" metric,
|x₁ − x₂| + |y₁ − y₂|, [Garey and Johnson, 1977a] or the L∞ metric, max {|x₁ − x₂|, |y₁ − y₂|},
which is equivalent to L₁ under a 45° rotation");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RectilinearSteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree

open RectilinearSteinerTree (RectilinearSteinerTreeInstance points)

/-!
# GEOMETRIC STEINER TREE in the L∞ metric is NP-complete

INSTANCE: a set `P ⊆ ℤ × ℤ` of points in the plane and a positive integer `K`.
QUESTION: is there a finite set `Q ⊆ ℤ × ℤ` such that there is a spanning tree of total
weight `K` or less for the vertex set `P ∪ Q`, where the weight of an edge
`{(x₁, y₁), (x₂, y₂)}` is the `L∞` distance `max {|x₁ - x₂|, |y₁ - y₂|}`?

This is the `L∞` variant in Garey and Johnson's comment to [ND13]. The instance encoding, the
point set `points` and `WellFormed` (`0 < K`) are those of the `L₁` variant,
`WantedExt.Complexity.NPComplete.RectilinearSteinerTreeWanted`, reused unchanged; the edge weight
is the `L∞` distance (`chebyshev`) in place of the rectilinear one, and the spanning tree is, as
there, a graph on the vertex type `P ∪ Q` (a `Finset (ℤ × ℤ)`) that is a Mathlib
`SimpleGraph.IsTree`, weighted by the sum over its edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The `L∞` distance `max {|x₁ - x₂|, |y₁ - y₂|}`. -/
def chebyshev (a b : ℤ × ℤ) : ℤ := max |a.1 - b.1| |a.2 - b.2|

/-- The `L∞` distance between the endpoints of an unordered pair of points. -/
def edgeWeight {V : Finset (ℤ × ℤ)} : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => chebyshev a b, fun a b => by
    simp only [chebyshev, abs_sub_comm (a : ℤ × ℤ).1, abs_sub_comm (a : ℤ × ℤ).2]⟩

/-- The total weight of a graph on a finite set of points: the sum of the `L∞` lengths of its
edges. -/
noncomputable def totalWeight {V : Finset (ℤ × ℤ)} (T : SimpleGraph V) : ℤ :=
  ∑ᶠ e ∈ T.edgeSet, edgeWeight e

/-- Some finite `Q ⊆ ℤ × ℤ` and some tree `T` on the vertex set `P ∪ Q` have total `L∞`
weight at most `K`. -/
def LInfinitySteinerTreeFeasible (i : RectilinearSteinerTreeInstance) : Prop :=
  ∃ Q : Finset (ℤ × ℤ), ∃ T : SimpleGraph ↥(points i ∪ Q), T.IsTree ∧
    totalWeight T ≤ i.2

open Classical in
/-- GEOMETRIC STEINER TREE in the `L∞` metric as a decision problem over bitstrings. -/
noncomputable def lInfinitySteinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearSteinerTreeInstance) x with
  | some i => decide (RectilinearSteinerTree.WellFormed i ∧ LInfinitySteinerTreeFeasible i)
  | none => false

/-- **GEOMETRIC STEINER TREE in the `L∞` metric is NP-complete.** Source: Garey and Johnson
(1979), [ND13], comment; Garey and Johnson (1977). -/
public theorem_wanted lInfinitySteinerTree_npComplete :
    lInfinitySteinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lInfinitySteinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree
