/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on co-bipartite graphs: definitions

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal
of Computing 7 (2000), 14-31 (STACS 1994, LNCS 775, 769-780, doi:10.1007/3-540-57785-8_189);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y (records
"Max Cut remains NP-hard even for ... co-bipartite graphs [Bodlaender and Jansen]");
ISGCI, class "co-bipartite" (gc_486), problem Maximum cut, NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is co-bipartite (its complement is bipartite), and
`0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1)ᶜ.IsBipartite ∧ 0 < i.2.2

/-- A partition `A = S`, `B = V - S` with at least `K` edges between the two sets (the MAXIMUM
CUT question). -/
def SimpleMaxCutCoBipartiteFeasible (i : MaxCutInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on co-bipartite graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCoBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutCoBipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite
