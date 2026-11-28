/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLARITY on triangle-free planar graphs of maximum degree 3: definitions

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubic

/-- An instance: the vertex count `n` (vertices `0, …, n - 1`) and the edge list. -/
abbrev MonopolarityInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MonopolarityInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

open Classical in
/-- Well-formedness of an instance: a simple edge list on `Fin n` (no duplicate edges in either
orientation, no self-loops, endpoints in range) whose graph is planar, triangle-free, and has no
vertex of degree exceeding `3`. -/
def WellFormed (i : MonopolarityInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsPlanar ∧ (Graph i).CliqueFree 3 ∧ ∀ v, (Graph i).degree v ≤ 3

/-- The graph is monopolar: a stable set whose complement induces a disjoint union of cliques. -/
def MonopolarityFeasible (i : MonopolarityInstance) : Prop :=
  PartitionIntoCliquesMonopolar.IsMonopolar (Graph i)

open Classical in
/-- MONOPOLARITY on triangle-free planar graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def monopolarityTriangleFreePlanarSubcubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonopolarityInstance) x with
  | some i => decide (WellFormed i ∧ MonopolarityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubic
