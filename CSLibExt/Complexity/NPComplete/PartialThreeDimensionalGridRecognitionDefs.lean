/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL 3D GRID GRAPH RECOGNITION: definitions

Source:
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo, "Complexity
dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011), 2370-2379,
doi:10.1016/j.tcs.2011.01.018 (abstract: "the three-dimensional version of the problem was for
the first time proven to be NP-complete");
ISGCI (https://www.graphclasses.org/classes/gc_850.html), problem "Recognition" on partial 3d
grid graphs: NP-complete.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartialGridRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialThreeDimensionalGridRecognition

open UnitLengthTreeGridEmbedding (UnitLengthTreeGridEmbeddingInstance Graph)

/-- The graph is a subgraph of the infinite three-dimensional grid: it is contained in
`hypercubicLattice 3`. -/
def PartialThreeDimensionalGridFeasible (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  (Graph i).IsContained (StatMech.Lattice.hypercubicLattice 3)

open Classical in
/-- PARTIAL 3D GRID GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def partialThreeDimensionalGridRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitLengthTreeGridEmbeddingInstance) x with
  | some i => decide (PartialGridRecognition.WellFormed i ∧
      PartialThreeDimensionalGridFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialThreeDimensionalGridRecognition
