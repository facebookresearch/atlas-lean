/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on domination perfect triangle-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313
(definition of domination perfect graphs; NP-completeness of DOMINATING SET on classes of them);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_553`
(domination perfect ∩ triangle-free), problem Domination: NP-complete (Zverovich and Zverovich
1995; and on its subclass `gc_529`, Zverovich and Zverovich 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetDominationPerfectTriangleFree

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- A graph on `Fin n` is domination perfect: every induced subgraph has equal domination
number and independent domination number (Zverovich and Zverovich 1995). -/
def IsDominationPerfect {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ U : Finset (Fin n),
    (G.induce (U : Set (Fin n))).dominationNumber =
      (G.induce (U : Set (Fin n))).indepDominationNumber

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is triangle-free and domination perfect. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).CliqueFree 3 ∧
    IsDominationPerfect (Graph i)

open Classical in
/-- DOMINATING SET on domination perfect triangle-free graphs as a decision problem over
bitstrings. -/
noncomputable def dominatingSetDominationPerfectTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetDominationPerfectTriangleFree
