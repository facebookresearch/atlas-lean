/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING for partial Steiner triple systems: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9 (recording the result of K. T. Phelps);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP4] SET SPLITTING.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Defs
public import CSLibExt.Complexity.NPComplete.SetSplittingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems



open MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
  (IsLinearTripleSystem)

/-- The members of `C` as a family of subsets of `Fin n`. -/
def tripleFamily (i : SetSplitting.SetSplittingInstance) : Finset (Finset (Fin i.1)) :=
  (i.2.map fun c => Finset.univ.filter fun v : Fin i.1 => (v : ℕ) ∈ c).toFinset

/-- Well-formedness of an instance: it is a well-formed SET SPLITTING instance (every member is
a duplicate-free list of elements of `V`), and the members form a partial Steiner triple system
(`IsLinearTripleSystem`). -/
def WellFormed (i : SetSplitting.SetSplittingInstance) : Prop :=
  SetSplitting.WellFormed i ∧ IsLinearTripleSystem (tripleFamily i)

open Classical in
/-- SET SPLITTING for partial Steiner triple systems as a decision problem over bitstrings. -/
noncomputable def setSplittingPartialSteinerTripleSystemsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplitting.SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplitting.SetSplittingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems
