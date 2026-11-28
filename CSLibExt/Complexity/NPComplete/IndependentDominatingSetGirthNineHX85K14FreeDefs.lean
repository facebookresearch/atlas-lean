/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET on the graph class gc_529: definitions

Source:
I. E. Zverovich and O. I. Zverovich, "Independent domination in hereditary classes",
Theoretical Computer Science 352(1-3) (2006), 215-225, doi:10.1016/j.tcs.2005.10.049;
ISGCI, Information System on Graph Classes and their Inclusions, class
(C_4,C_5,C_6,C_7,C_8,H,X_85,triangle)-free ∩ K_1,4-free (gc_529,
https://www.graphclasses.org/classes/gc_529.html), problem Independent dominating set; small
graphs `H` and `X_85` as defined at https://www.graphclasses.org/smallgraphs.html;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET, comment: "Also
NP-complete if V' is required to be both a dominating set and an independent set."
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetGirthNineHX85K14FreeDefs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetGirthNineHX85K14Free

/-- Well-formedness of an instance: the instance class of `DominatingSetGirthNineHX85K14Free` (a
simple edge list on `Fin n`, `0 < K ≤ n`, and no induced `C_3, …, C_8`, `H`, `X_85` or
`K_1,4`). -/
def WellFormed (i : IndependentDominatingSet.IndependentDominatingSetInstance) : Prop :=
  DominatingSetGirthNineHX85K14Free.WellFormed i

open Classical in
/-- INDEPENDENT DOMINATING SET on the graph class gc_529 as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetGirthNineHX85K14FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSet.IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSet.IndependentDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetGirthNineHX85K14Free
