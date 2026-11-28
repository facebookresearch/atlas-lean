/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on partial grid graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics 86
(1990), 165-177, doi:10.1016/0012-365X(90)90358-O (DOMINATING SET on grid graphs);
M. de Berg, H. L. Bodlaender, S. Kisfaludi-Bak, D. Marx and T. C. van der Zanden, "A framework
for exponential-time-hypothesis-tight algorithms and lower bounds in geometric intersection
graphs", SIAM Journal on Computing 49 (2020), 1291-1331, doi:10.1137/20M1320870,
arXiv:1803.10633, Theorem 32 (a reduction from 3-SAT to DOMINATING SET on induced grid graphs);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_440` (partial
grid), problem Domination: NP-complete (on grid graphs, Clark, Colbourn and Johnson 1990).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPartialGrid

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is a subgraph of the grid `ℤ × ℤ` (a partial grid). -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (Graph i).IsContained (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ)

open Classical in
/-- DOMINATING SET on partial grid graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetPartialGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPartialGrid
