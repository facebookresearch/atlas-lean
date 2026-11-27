/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on B₀-CPG graphs is NP-complete

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018
(arXiv:1903.01805), Theorem 11;
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), LNCS 11282, doi:10.1007/978-3-030-04414-5_22 (the class
CPG);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Basic
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPG

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on B₀-CPG graphs is NP-complete

INSTANCE: a `B₀-CPG` graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: can `V` be partitioned into `k ≤ K` disjoint sets `V₁, …, V_k` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesWanted`) restricted to the graph
class `B₀-CPG` (ISGCI `gc_1337`). A graph is a CPG graph (Deniz, Galby, Munaro and Ries 2018) if
its vertices can be represented by a family of pairwise interiorly disjoint paths on a grid, two
vertices being adjacent exactly when their paths touch; the paths may not have common interior
points (points of a path other than its two endpoints) but only touch. It is `B₀-CPG` if every
path has no bend, i.e., is a horizontal or vertical grid segment. Champseix, Galby, Munaro and
Ries (2021), Theorem 11, prove that clique cover (the minimum number of cliques covering the
vertices) is NP-complete for `B₀-CPG` line graphs, hence for `B₀-CPG` graphs; a cover by cliques
can be made a partition, since subsets of cliques are cliques.

The instance, the graph, the well-formedness `0 < K ≤ |V|` and the question are those of
`PartitionIntoCliquesWanted`; the restriction `IsBZeroCPG` is added to the well-formedness. A
grid segment is given by its endpoints `p < q` in `ℕ × ℕ` (componentwise order, so `p ≠ q`) with
one coordinate equal; its grid points are `Set.Icc p q`. Two such segments touch, i.e. have a
common point in the plane, exactly when they have a common grid point (perpendicular segments
meet at a grid point, and collinear segments overlapping in an interval overlap in a grid point).
Common interior points are tested on the grid refined by a factor of `2`: the interior points of
the segment from `p` to `q` that are grid points of the refined grid are those of
`Set.Icc (2p) (2q)` other than `2p` and `2q`, and two segments have a common interior point in
the plane exactly when they have one on the refined grid (a crossing is at a grid point, and a
collinear overlap of positive length contains the midpoint of a grid edge). The segment model is
not part of the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The grid point `2p` of the grid refined by a factor of `2`. -/
def double (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1, 2 * p.2)

/-- The interior points of the segment from `p` to `q` on the refined grid. -/
def interiorPoints (s : (ℕ × ℕ) × (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  Set.Icc (double s.1) (double s.2) \ {double s.1, double s.2}

/-- `G` is a `B₀-CPG` graph: there are horizontal or vertical grid segments `P v` from
`(P v).1` to `(P v).2 > (P v).1`, one per vertex, pairwise without common interior points, such
that two distinct vertices are adjacent exactly when their segments have a common point. -/
def IsBZeroCPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → (ℕ × ℕ) × (ℕ × ℕ),
    (∀ v, (P v).1 < (P v).2 ∧ ((P v).1.1 = (P v).2.1 ∨ (P v).1.2 = (P v).2.2)) ∧
    (∀ u v, u ≠ v → interiorPoints (P u) ∩ interiorPoints (P v) = ∅) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (Set.Icc (P u).1 (P u).2 ∩ Set.Icc (P v).1 (P v).2).Nonempty)

/-- Well-formedness of an instance: well formed for PARTITION INTO CLIQUES (a simple graph on
`Fin n` and `0 < K ≤ n`), and the graph is a `B₀-CPG` graph. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ IsBZeroCPG (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on `B₀-CPG` graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesBZeroCPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on `B₀-CPG` graphs is NP-complete.** Source: Champseix, Galby,
Munaro and Ries (2021), Theorem 11; Deniz, Galby, Munaro and Ries (2018) (the class); Garey and
Johnson (1979), [GT15]. -/
public theorem_wanted partitionIntoCliquesBZeroCPG_npComplete :
    partitionIntoCliquesBZeroCPGDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesBZeroCPGDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPG
