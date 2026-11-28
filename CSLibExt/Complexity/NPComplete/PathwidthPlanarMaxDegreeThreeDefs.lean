/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF PLANAR GRAPHS OF MAXIMUM DEGREE 3: definitions

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58 (1988), 209-229, doi:10.1016/0304-3975(88)90028-X (Vertex Separation for
planar graphs of maximum vertex degree 3);
N. G. Kinnersley, "The vertex separation number of a graph equals its path-width", Information
Processing Letters 42 (1992), 345-350, doi:10.1016/0020-0190(92)90234-M.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the
graph is planar with every vertex degree at most `3`, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsPlanar ∧ (∀ v, (Graph i).degree v ≤ 3) ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF PLANAR GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over bitstrings. -/
noncomputable def pathwidthPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphs.PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthPlanarMaxDegreeThree
