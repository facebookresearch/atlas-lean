/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY is NP-complete for every fixed K ≥ 4

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), comment "remains NP-complete for all fixed K ≥ 3";
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedKColorability

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# GRAPH K-COLORABILITY is NP-complete for every fixed K ≥ 4

Fix an integer `K ≥ 4`.
INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` `K`-colorable, that is, is there a function `f : V → {1, 2, …, K}` such that
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`? Equivalently (the ISGCI class "K-colorable"): can `V` be
partitioned into `K` independent sets?

Garey and Johnson [GT4] state GRAPH K-COLORABILITY with `K` in the instance (Karp 1972) and
comment: "Solvable in polynomial time for K = 2, but remains NP-complete for all fixed K ≥ 3 and,
for K = 3, for planar graphs having no vertex degree exceeding 4 [Garey, Johnson, and
Stockmeyer, 1976]." The case `K = 3` (3-COLORING) is already proved NP-complete in
`CSLibExt.Computability.Complexity.Karp.Color`; this module states the remaining fixed values
`K ≥ 4`. (A graph `G` is 3-colorable exactly when `G` plus `K - 3` new vertices adjacent to
everything, and to each other, is `K`-colorable, which carries hardness from `K = 3` to every
larger fixed `K`.) The ISGCI database lists recognition of the classes "4-colorable" (gc_1071),
"5-colorable" (gc_1182) and "6-colorable" (gc_1342) as NP-complete, citing Garey and Johnson.

`K` is fixed, not part of the input: the decision problem is `fixedKColorabilityDec k`, and the
theorem holds for every `k ≥ 4`. The instance, the graph and the question are those of
`GraphColoringWanted` ([GT4]), reused unchanged: vertex count, edge list on `Fin n` and number of
colors, with `GraphColoring.WellFormed` (a simple edge list), `GraphColoring.Graph` and
`GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`, Mathlib's
`SimpleGraph.Colorable`). The restriction adds to well-formedness that the number of colors in the
instance is the fixed `k`, as in `TriangleFreeKColorabilityWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed number of colors `k`: a well-formed GRAPH
K-COLORABILITY instance whose number of colors is `k`. -/
def WellFormed (k : ℕ) (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = k

open Classical in
/-- GRAPH K-COLORABILITY, for the fixed number of colors `k`, as a decision problem over
bitstrings. -/
noncomputable def fixedKColorabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **GRAPH K-COLORABILITY is NP-complete for every fixed `K ≥ 4`.** Source: Garey and Johnson
(1979), [GT4]; Garey, Johnson and Stockmeyer (1976); Karp (1972). -/
public theorem_wanted fixedKColorability_npComplete (k : ℕ) (_hk : 4 ≤ k) :
    fixedKColorabilityDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedKColorabilityDec k)

end MetaMathlibExt.Complexity.NPComplete.FixedKColorability
