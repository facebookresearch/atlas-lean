/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LEAF SPANNING TREE on 4-regular graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND2] MAXIMUM LEAF SPANNING TREE,
comment on p. 206 ("Remains NP-complete if G is regular of degree 4"; reference
[Garey and Johnson, ——], unpublished results);
A. Reich, "Complexity of the maximum leaf spanning tree problem on planar and regular graphs",
Theoretical Computer Science 626 (2016), 134-143, doi:10.1016/j.tcs.2016.02.011, Section 1
(records the 4-regular case with its attribution to Garey and Johnson).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumLeafSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreeFourRegular

open MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree
  (MaximumLeafSpanningTreeInstance MaximumLeafSpanningTreeFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed MAXIMUM LEAF SPANNING TREE instance whose
graph is regular of degree 4, with `0 < K ≤ |V|`. -/
def WellFormed (i : MaximumLeafSpanningTreeInstance) : Prop :=
  MaximumLeafSpanningTree.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsRegularOfDegree 4 ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- MAXIMUM LEAF SPANNING TREE on 4-regular graphs as a decision problem over bitstrings. -/
noncomputable def maximumLeafSpanningTreeFourRegularDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLeafSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLeafSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreeFourRegular
