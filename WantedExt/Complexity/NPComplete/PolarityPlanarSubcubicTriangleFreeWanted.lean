/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar graphs",
Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032;
V. B. Le and R. Nevries, "Recognizing polar planar graphs using new results for monopolarity",
Algorithms and Computation (ISAAC 2011), Lecture Notes in Computer Science 7074, Springer (2011),
120-129, doi:10.1007/978-3-642-25591-5_14 (introduction: "NP-completeness for monopolarity and
polarity on planar graphs and triangle-free graphs of maximum degree 3");
ISGCI, *Information System on Graph Classes and their Inclusions*, class "maximum degree 3 ∩
planar ∩ triangle-free" (gc_1274), problem Polarity: NP-complete, with the reference to Le and
Nevries (2014).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubicWanted
public import WantedExt.Complexity.NPComplete.PolarityTriangleFreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityPlanarSubcubicTriangleFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree
  (PolarityTriangleFreeInstance IsPolar PolarityTriangleFreeFeasible)

/-!
# POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is planar, triangle-free and of
maximum degree at most 3.
QUESTION: is `G` polar, i.e. can `V` be partitioned into sets `A` and `B` such that `A` induces a
complete multipartite graph and `B` induces a disjoint union of cliques?

This is POLARITY ON TRIANGLE-FREE GRAPHS (`PolarityTriangleFreeWanted`) further restricted to
planar graphs of maximum degree 3, the ISGCI class `gc_1274`. The question, the polar-graph
predicate `IsPolar` and the instance type are reused from that module. The instance class is the
one of `MonopolarityTriangleFreePlanarSubcubicWanted` (MONOPOLARITY on the same class, from the same
paper), whose well-formedness is reused unchanged: a simple edge list whose graph is planar (the
repository's `SimpleGraph.IsPlanar`, a crossing-free straight-line drawing; by Fáry's theorem this
is planarity), triangle-free (`CliqueFree 3`) and has every vertex degree at most 3. Both modules
build the graph as `Cslib.Complexity.Karp.edgeGraph n E` from the same vertex count and edge list.
Le and Nevries prove that recognizing polar (and monopolar) graphs remains NP-complete on this
class; membership in NP holds for all graphs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over
bitstrings. -/
noncomputable def polarityPlanarSubcubicTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTriangleFreeInstance) x with
  | some i => decide (MonopolarityTriangleFreePlanarSubcubic.WellFormed i ∧
      PolarityTriangleFreeFeasible i)
  | none => false

/-- **POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete.** Source: Le and
Nevries (2014); ISGCI, class `gc_1274`, problem Polarity. -/
public theorem_wanted polarityPlanarSubcubicTriangleFree_npComplete :
    polarityPlanarSubcubicTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polarityPlanarSubcubicTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.PolarityPlanarSubcubicTriangleFree
