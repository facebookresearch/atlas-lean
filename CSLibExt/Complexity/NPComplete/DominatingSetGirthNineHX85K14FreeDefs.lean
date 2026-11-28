/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and O. I. Zverovich, "Independent domination in hereditary classes",
Theoretical Computer Science 352 (2006), 215-225, doi:10.1016/j.tcs.2005.10.049;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_529`
((C_4,C_5,C_6,C_7,C_8,H,X_85,triangle)-free ∩ K_1,4-free), problem Domination: NP-complete
(Zverovich and Zverovich 2006); small graphs `H` and `X_85` as defined at
https://www.graphclasses.org/smallgraphs.html.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetGirthNineHX85K14Free

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- ISGCI's small graph `H` (graph6 `EgSG`): two adjacent vertices `1` and `4` of degree `3`,
with further neighbours `0, 2` and `3, 5`. -/
def graphH : SimpleGraph (Fin 6) :=
  Cslib.Complexity.Karp.edgeGraph 6 [(0, 1), (1, 2), (1, 4), (3, 4), (4, 5)]

/-- ISGCI's small graph `X_85` (graph6 `FhD?_`): the path `0, 1, 2, 3, 4` with pendant
vertices `5` at `1` and `6` at `3`. -/
def graphX85 : SimpleGraph (Fin 7) :=
  Cslib.Complexity.Karp.edgeGraph 7 [(0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (3, 6)]

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph has no induced `C_3, …, C_8`, `H`, `X_85` or `K_1,4`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (∀ k, 3 ≤ k → k ≤ 8 → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)) ∧
    ¬ graphH.IsIndContained (Graph i) ∧ ¬ graphX85.IsIndContained (Graph i) ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 4)).IsIndContained (Graph i)

open Classical in
/-- DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs, as a
decision problem over bitstrings. -/
noncomputable def dominatingSetGirthNineHX85K14FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetGirthNineHX85K14Free
