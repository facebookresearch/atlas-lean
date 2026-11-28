/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on locally connected graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected), problem Clique: NP-complete, reference `ref_1506` (ISGCI note: adding a universal
vertex to a connected graph yields a locally connected graph and raises the size of a largest
clique by exactly one; communicated by P. Irzhavski). No published proof was found.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CliqueClawFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueLocallyConnected

open CliqueClawFree (CliqueClawFreeInstance Graph CliqueClawFreeFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is locally
connected (the neighbourhood of every vertex induces a connected graph), and `0 < K ≤ |V|`. -/
def WellFormed (i : CliqueClawFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CLIQUE on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def cliqueLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueClawFreeInstance) x with
  | some i => decide (WellFormed i ∧ CliqueClawFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueLocallyConnected
