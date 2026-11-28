/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET on 4-regular graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, p. 190, comment
("Variation in which the subgraph induced by V' is required to be connected is also
NP-complete", credited there to [Garey and Johnson, unpublished]);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(1)
(1984), 147-160, doi:10.1016/0196-6774(84)90045-2, Section 3 (records that the unpublished
1978 result of Garey and Johnson covers CONNECTED DOMINATING SET on "4-regular (not necessarily
planar) graphs"; the original proof was not available).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConnectedDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetFourRegular

open MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
  (ConnectedDominatingSetInstance Graph ConnectedDominatingSetFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed CONNECTED DOMINATING SET instance with
`0 < K ≤ |V|` whose graph is regular of degree 4. -/
def WellFormed (i : ConnectedDominatingSetInstance) : Prop :=
  ConnectedDominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (Graph i).IsRegularOfDegree 4

open Classical in
/-- CONNECTED DOMINATING SET on 4-regular graphs as a decision problem over bitstrings. -/
noncomputable def connectedDominatingSetFourRegularDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetFourRegular
