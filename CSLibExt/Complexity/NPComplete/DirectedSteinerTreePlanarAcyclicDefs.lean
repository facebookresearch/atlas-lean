/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED STEINER TREE in planar acyclic graphs with equal weights: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 1, STEINER TREE IN GRAPHS [ND12]: the directed version
"is NP-complete even for acyclic planar graphs with all edge weights equal", credited to
J. S. Provan, "A polynomial algorithm for the Steiner tree problem on terminal-planar graphs",
Report No. UNC/ORSA/TR-83/10, University of North Carolina, Chapel Hill (1983) (not available);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedSteinerTreePlanarAcyclic

/-- An instance: vertex count `n`, arc list `A`, source `s`, sink list `T` and bound `B`. -/
abbrev DirectedSteinerTreePlanarAcyclicInstance := ℕ × List (ℕ × ℕ) × ℕ × List ℕ × ℕ

/-- The arc relation of an arc list: `u → v` when `(u, v)` is in the list. -/
def ArcRel (A : List (ℕ × ℕ)) (u v : ℕ) : Prop := (u, v) ∈ A

/-- The underlying undirected simple graph: `u` and `v` are adjacent when `u ≠ v` and `u → v`
or `v → u` is an arc. -/
def UnderlyingGraph (i : DirectedSteinerTreePlanarAcyclicInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the arcs are distinct with endpoints in range; the digraph
is acyclic and planar; the source and the distinct sinks are vertices; and `0 < B`. -/
def WellFormed (i : DirectedSteinerTreePlanarAcyclicInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (ArcRel i.2.1) v v) ∧ (UnderlyingGraph i).IsPlanar ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1.Nodup ∧ (∀ t ∈ i.2.2.2.1, t < i.1) ∧ 0 < i.2.2.2.2

/-- Some set of at most `B` arcs of `G` contains a directed path from `s` to every sink. -/
def DirectedSteinerTreePlanarAcyclicFeasible
    (i : DirectedSteinerTreePlanarAcyclicInstance) : Prop :=
  ∃ A' : List (ℕ × ℕ), A'.Sublist i.2.1 ∧ A'.length ≤ i.2.2.2.2 ∧
    ∀ t ∈ i.2.2.2.1, Relation.ReflTransGen (ArcRel A') i.2.2.1 t

open Classical in
/-- DIRECTED STEINER TREE in planar acyclic graphs with equal weights as a decision problem over
bitstrings. -/
noncomputable def directedSteinerTreePlanarAcyclicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedSteinerTreePlanarAcyclicInstance) x with
  | some i => decide (WellFormed i ∧ DirectedSteinerTreePlanarAcyclicFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedSteinerTreePlanarAcyclic
