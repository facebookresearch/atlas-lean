/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B0-CPG GRAPH RECOGNITION is NP-complete

Source:
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), Lecture Notes in Computer Science 11282 (2018), 317-330,
doi:10.1007/978-3-030-04414-5_22, Theorem 2 (arXiv:1803.03468).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.Complexity.NPComplete.ThreeColorabilityB0CPGWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BZeroCPGRecognition

/-!
# B0-CPG GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a `B_0`-CPG graph?

Deniz, Galby, Munaro and Ries: "A graph `G = (V, E)` is CPG if there exists a collection `P` of
interiorly disjoint paths on a grid `G` such that `P` is in one-to-one correspondence with `V` and
two vertices are adjacent in `G` if and only if the corresponding paths touch; if every path in
`P` has at most `k` bends, `G` is `B_k`-CPG" (ISGCI class `gc_1337` for `k = 0`). Their Theorem 2:
"Recognition is NP-complete for `B_0`-CPG graphs" (by a reduction from recognizing rectilinear
planar graphs: a graph is rectilinear planar if and only if its line graph is `B_0`-CPG).

The graph is given by an edge list on `Fin n`. The class is the predicate
`ThreeColorabilityB0CPG.IsB0CPG` of `WantedExt.Complexity.NPComplete.ThreeColorabilityB0CPGWanted`
(same source, Deniz et al.), reused unchanged: every vertex `v` is represented by a straight
horizontal or vertical grid segment from `A v` to `B v` (two distinct points of `ℤ × ℤ` sharing a
coordinate, the closed real segment between them), distinct segments have disjoint interiors, and
two distinct vertices are adjacent exactly when their segments share a grid point that is an
endpoint of at least one of them. The representation is not part of the input. Membership in NP,
although the vertex count `n` is written in binary: a graph is `B_0`-CPG exactly when its
subgraph induced by the non-isolated vertices is (an isolated vertex gets a short segment far from
all others), there are at most `2|E|` non-isolated vertices, and a representation of that subgraph
with every coordinate replaced by its rank (which preserves every condition) is a certificate of
size polynomial in the length of the edge list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev BZeroCPGRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BZeroCPGRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BZeroCPGRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is a `B_0`-CPG graph. -/
def BZeroCPGRecognitionFeasible (i : BZeroCPGRecognitionInstance) : Prop :=
  ThreeColorabilityB0CPG.IsB0CPG (Graph i)

open Classical in
/-- B0-CPG GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def bZeroCPGRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BZeroCPGRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ BZeroCPGRecognitionFeasible i)
  | none => false

/-- **B0-CPG GRAPH RECOGNITION is NP-complete.** Source: Deniz, Galby, Munaro and Ries (2018),
Theorem 2. -/
public theorem_wanted bZeroCPGRecognition_npComplete :
    bZeroCPGRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bZeroCPGRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BZeroCPGRecognition
