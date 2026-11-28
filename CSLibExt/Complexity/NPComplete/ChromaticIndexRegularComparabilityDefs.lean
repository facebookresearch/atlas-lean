/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of k-regular comparability graphs (fixed k ≥ 3): definitions

Source:
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30(1) (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
restated in E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying k-Edge Colouring for
H-free graphs", Information Processing Letters 146 (2019), 39-43,
doi:10.1016/j.ipl.2019.02.006 (arXiv:1810.04379), Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChromaticIndexRegularDefs
public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegularComparability

open MetaMathlibExt.Complexity.NPComplete

/-- Well-formedness of an instance for the fixed degree `k`: the instance is a well-formed
instance of CHROMATIC INDEX of `k`-regular graphs (a simple edge list whose graph is
`k`-regular), and its graph is a comparability graph. -/
def WellFormed (k : ℕ) (i : ChromaticIndexRegular.ChromaticIndexRegularInstance) : Prop :=
  ChromaticIndexRegular.WellFormed k i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (ChromaticIndexRegular.Graph i)

open Classical in
/-- CHROMATIC INDEX of `k`-regular comparability graphs, for the fixed `k`, as a decision
problem over bitstrings. -/
noncomputable def chromaticIndexRegularComparabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChromaticIndexRegular.ChromaticIndexRegularInstance) x with
  | some i => decide (WellFormed k i ∧ ChromaticIndexRegular.ChromaticIndexRegularFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegularComparability
