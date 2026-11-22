/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B₁-CPG GRAPH RECOGNITION is NP-complete

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018
(arXiv:1903.01805; Section 1: the definition of CPG and `B_k`-CPG graphs; Theorem 9:
"Recognition is NP-complete in `B_k`-CPG for any `k ≥ 1`");
ISGCI (https://www.graphclasses.org/classes/gc_1338.html), class B_1-CPG, problem "Recognition":
NP-complete, citing Champseix, Galby, Munaro and Ries.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CliqueBOneVPGWanted
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPGWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition

open CliqueBOneVPG (BendPath pathPoints)
open PartitionIntoCliquesBZeroCPG (double)

/-!
# B₁-CPG GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a `B₁`-CPG graph, i.e., the contact graph of a
family of pairwise interiorly disjoint paths on a grid, each with at most one bend?

Champseix, Galby, Munaro and Ries (Section 1): "a graph `G = (V, E)` is a CPG graph if there
exists a collection `P` of pairwise interiorly disjoint paths on a grid `G` in one-to-one
correspondence with `V` such that two vertices are adjacent if and only if the corresponding paths
touch. If every such path has at most `k` bends, for some `k ≥ 0`, then the graph is `B_k`-CPG."
Two paths "touch if [they] have a common grid-point", and "an interior point of a path `P` is a
point belonging to `P` and different from its endpoints". Theorem 9 proves recognition
NP-complete for every `k ≥ 1`; membership in NP is witnessed by the endpoints and bend points of
the paths. This module states the case `k = 1` (ISGCI `gc_1338`).

A path with at most one bend is given by its endpoints `a`, `b` and its corner `c`, as the grid
paths of `CliqueBOneVPGWanted` (`BendPath`, with grid points `pathPoints`, those of the legs
`a`-`c` and `c`-`b`); here, as in the CPG model, it is a genuine path from `a` to `b`: the first
leg is horizontal and the second vertical, or the other way round (a leg may have length `0`, so
straight paths are included), and `a ≠ b`, so the path has at least one grid edge. Being
perpendicular, the two legs meet only at `c`, and a bend at `c` exists exactly when both legs have
positive length. Interiorly disjoint paths have no common interior point (so paths of distinct
vertices, each with at least one grid edge, are distinct, as the correspondence requires). As in
`PartitionIntoCliquesBZeroCPGWanted`, interior points are tested on the grid refined by a factor
of `2` (`double`): the points of the refined grid on the doubled path, other than the doubled
endpoints. Two such paths have a common interior point in the plane exactly when they have one on
the refined grid: an isolated common point is the crossing of a horizontal and a vertical leg, at
a grid point, and a common piece of positive length contains the midpoint of a grid edge, which
is no endpoint. Two such paths have a common point exactly when they have a common grid point
(corners and endpoints lie on the grid). Every finite representation can be moved to the grid
`ℕ × ℕ` by replacing coordinates by their ranks, so the class does not depend on these choices.
The paths are not part of the input.

The graph is simple and given by an edge list on `Fin n`. Isolated vertices do not change the
answer (a short segment away from all other paths), so the binary vertex count does not make the
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

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev BOneCPGRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BOneCPGRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BOneCPGRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `P = (a, c, b)` is a grid path from `a` to `b` with at most one bend, at `c`: the leg `a`-`c`
is horizontal and the leg `c`-`b` vertical, or the other way round, and `a ≠ b`. -/
def IsOneBendPath (P : BendPath) : Prop :=
  P.1 ≠ P.2.2 ∧
    ((P.1.2 = P.2.1.2 ∧ P.2.1.1 = P.2.2.1) ∨ (P.1.1 = P.2.1.1 ∧ P.2.1.2 = P.2.2.2))

/-- The interior points of the path on the grid refined by a factor of `2`: the refined grid
points of the doubled path other than its doubled endpoints. -/
def interiorPoints (P : BendPath) : Set (ℕ × ℕ) :=
  pathPoints (double P.1, double P.2.1, double P.2.2) \ {double P.1, double P.2.2}

/-- `G` is a `B₁`-CPG graph: there are grid paths `P v` with at most one bend, one per vertex,
pairwise without common interior points, such that two distinct vertices are adjacent exactly
when their paths have a common grid point. -/
def IsBOneCPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → BendPath, (∀ v, IsOneBendPath (P v)) ∧
    (∀ u v, u ≠ v → interiorPoints (P u) ∩ interiorPoints (P v) = ∅) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (pathPoints (P u) ∩ pathPoints (P v)).Nonempty)

/-- The graph of the instance is a `B₁`-CPG graph. -/
def BOneCPGRecognitionFeasible (i : BOneCPGRecognitionInstance) : Prop :=
  IsBOneCPG (Graph i)

open Classical in
/-- `B₁`-CPG GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def bOneCPGRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BOneCPGRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ BOneCPGRecognitionFeasible i)
  | none => false

/-- **`B₁`-CPG GRAPH RECOGNITION is NP-complete.** Source: Champseix, Galby, Munaro and Ries
(2021), Theorem 9; ISGCI, class `gc_1338`. -/
public theorem_wanted bOneCPGRecognition_npComplete :
    bOneCPGRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bOneCPGRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition
