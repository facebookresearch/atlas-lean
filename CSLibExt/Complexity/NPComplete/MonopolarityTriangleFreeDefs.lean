/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLARITY OF TRIANGLE-FREE GRAPHS: definitions

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755;
ISGCI (Information System on Graph Classes and their Inclusions), class triangle-free (gc_371),
problem Monopolarity: NP-complete [Churchley and Huang 2014].
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityMonopolarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFree

/-- An instance: vertex count and edge list. -/
abbrev MonopolarityTriangleFreeInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MonopolarityTriangleFreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, and the
graph has no triangle. -/
def WellFormed (i : MonopolarityTriangleFreeInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).CliqueFree 3

/-- The graph is monopolar. -/
def MonopolarityTriangleFreeFeasible (i : MonopolarityTriangleFreeInstance) : Prop :=
  ThreeColorabilityMonopolar.IsMonopolar (Graph i)

open Classical in
/-- MONOPOLARITY OF TRIANGLE-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def monopolarityTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MonopolarityTriangleFreeInstance) x with
  | some i => decide (WellFormed i ∧ MonopolarityTriangleFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFree
