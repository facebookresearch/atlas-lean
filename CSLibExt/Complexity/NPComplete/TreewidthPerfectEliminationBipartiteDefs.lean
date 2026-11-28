/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS: definitions

Source:
T. Liu, "Restricted bipartite graphs: comparison and hardness results", in Algorithmic Aspects
in Information and Management (AAIM 2014), Lecture Notes in Computer Science 8546, Springer
(2014), 241-252, doi:10.1007/978-3-319-07956-1_22 (abstract: "We also show the
NP-completeness of treewidth and feedback vertex set for perfect elimination bipartite
graphs.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartiteDefs
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthPerfectEliminationBipartite

open MetaMathlibExt.Complexity.NPComplete.Treewidth
open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite
  (IsPerfectEliminationBipartite)

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is perfect elimination bipartite (bipartite, with a perfect edge elimination ordering). -/
def PerfectEliminationBipartiteWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ IsPerfectEliminationBipartite (Graph i)

open Classical in
/-- TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthPerfectEliminationBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (PerfectEliminationBipartiteWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthPerfectEliminationBipartite
