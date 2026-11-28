/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on locally connected graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected, https://www.graphclasses.org/classes/gc_932.html), problem Domination: NP-complete,
with its note 1506 (communicated by A. Leitert): adding a true twin to every vertex gives a
locally connected graph with the same domination number.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetLocallyConnected

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is locally connected (every neighbourhood induces a connected graph). -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- DOMINATING SET on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetLocallyConnected
