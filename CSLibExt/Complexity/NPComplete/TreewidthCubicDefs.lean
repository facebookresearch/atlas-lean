/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF CUBIC GRAPHS: definitions

Source:
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, "Treewidth is NP-complete on cubic
graphs (and related results)", Theorem 4.1: "Treewidth is NP-complete on regular graphs of
degree 3").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TreewidthDefs
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCubic

open MetaMathlibExt.Complexity.NPComplete.Treewidth

open Classical in
/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is cubic: every vertex has degree exactly 3. -/
def CubicWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- TREEWIDTH OF CUBIC GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (CubicWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthCubic
