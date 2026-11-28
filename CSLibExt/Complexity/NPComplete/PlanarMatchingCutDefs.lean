/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING CUT on planar graphs: definitions

Source:
P. Bonsma, "The complexity of the matching-cut problem for planar graphs and other graph
classes", Journal of Graph Theory 62 (2009), 109-126, doi:10.1002/jgt.20390.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.MatchingCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarMatchingCut

open MetaMathlibExt.Complexity.NPComplete.MatchingCut

/-- Well-formedness of an instance: a well-formed MATCHING CUT instance whose graph is
planar. -/
def WellFormed (i : MatchingCutInstance) : Prop :=
  MatchingCut.WellFormed i ∧ (Graph i).IsPlanar

open Classical in
/-- MATCHING CUT on planar graphs as a decision problem over bitstrings. -/
noncomputable def planarMatchingCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatchingCutInstance) x with
  | some i => decide (WellFormed i ∧ MatchingCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarMatchingCut
