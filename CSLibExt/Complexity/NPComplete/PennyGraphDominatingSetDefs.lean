/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET IN PENNY GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics 86
(1990), 165-177, doi:10.1016/0012-365X(90)90358-O (DOMINATING SET on unit disk graphs and on
grid graphs);
M. de Berg, H. L. Bodlaender, S. Kisfaludi-Bak, D. Marx and T. C. van der Zanden, "A framework
for exponential-time-hypothesis-tight algorithms and lower bounds in geometric intersection
graphs", SIAM Journal on Computing 49 (2020), 1291-1331, doi:10.1137/20M1320870,
arXiv:1803.10633, Theorem 32 (a reduction from 3-SAT to DOMINATING SET on induced grid graphs);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1381` (penny),
problem Domination: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitDiskDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PennyGraphDominatingSet

open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (point)

/-- Well-formedness of an instance: a well-formed DOMINATING SET IN UNIT DISK GRAPHS instance
whose points are pairwise at distance at least `1`. -/
def WellFormed (i : UnitDiskDominatingSetInstance) : Prop :=
  UnitDiskDominatingSet.WellFormed i ∧
    ∀ a b : Fin i.1.length, a ≠ b → 1 ≤ dist (point i.1[a]) (point i.1[b])

open Classical in
/-- DOMINATING SET IN PENNY GRAPHS as a decision problem over bitstrings. -/
noncomputable def pennyGraphDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDiskDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitDiskDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PennyGraphDominatingSet
