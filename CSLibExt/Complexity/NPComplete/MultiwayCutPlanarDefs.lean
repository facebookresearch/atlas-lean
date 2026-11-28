/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY CUT ON PLANAR GRAPHS: definitions

Source:
E. Dahlhaus, D. S. Johnson, C. H. Papadimitriou, P. D. Seymour and M. Yannakakis, "The
complexity of multiterminal cuts", SIAM Journal on Computing 23(4) (1994), 864-894,
doi:10.1137/S0097539792225297 (the planar problem is NP-hard when the number of terminals is not
fixed);
M. Johnson, B. Martin, S. Pandey, D. Paulusma, S. Smith and E. J. van Leeuwen, "Edge multiway cut
and node multiway cut are hard for planar subcubic graphs", 19th Scandinavian Symposium on
Algorithm Theory (SWAT 2024), LIPIcs 294 (2024), 29:1-29:17, doi:10.4230/LIPIcs.SWAT.2024.29
(Theorem 1.1: unweighted EDGE MULTIWAY CUT is NP-complete for planar subcubic graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiwayCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayCutPlanar

open MultiwayCut (MultiwayCutInstance MultiwayCutFeasible)

/-- Well-formedness of an instance: well formed for MULTIWAY CUT, the graph of the edge list is
planar, and the bound `B` is positive. -/
def WellFormed (i : MultiwayCutInstance) : Prop :=
  MultiwayCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar ∧
    0 < i.2.2.2

open Classical in
/-- MULTIWAY CUT ON PLANAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def multiwayCutPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MultiwayCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiwayCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiwayCutPlanar
