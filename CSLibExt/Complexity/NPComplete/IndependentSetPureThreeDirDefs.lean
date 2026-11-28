/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on PURE-3-DIR graphs: definitions

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1);
J. Kratochvíl and J. Matoušek, "Intersection graphs of segments", Journal of Combinatorial
Theory, Series B 62 (1994), 289-315, doi:10.1006/jctb.1994.1071 (recognition of PURE-k-DIR is
in NP);
ISGCI, *Information System on Graph Classes and their Inclusions*, class PURE-3-DIR (gc_868),
problem Independent set: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PureKDirGraphRecognitionDefs
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetPureThreeDir

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)
open PureKDirGraphRecognition (IsPureKDirGraph)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is a PURE-3-DIR
graph, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsPureKDirGraph 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on PURE-3-DIR graphs as a decision problem over bitstrings. -/
noncomputable def independentSetPureThreeDirDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetPureThreeDir
