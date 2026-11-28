/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIRST ORDER SUBSUMPTION with a fixed number `n ≥ 3` of target expressions: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO18] FIRST ORDER SUBSUMPTION, comment ("Remains
NP-complete for any fixed `n ≥ 3`"; reference: [Baxter, 1976], [Baxter, 1977]), p. 264;
L. D. Baxter, *The Complexity of Unification*, Doctoral Thesis, Department of Computer Science,
University of Waterloo (1976);
L. D. Baxter, "The NP-completeness of subsumption", unpublished manuscript (1977).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FirstOrderSubsumptionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets

open MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
  (FirstOrderSubsumptionInstance FirstOrderSubsumptionFeasible)

/-- Well-formedness of an instance for the fixed `n`: it is a well-formed FIRST ORDER
SUBSUMPTION instance, and `F` consists of exactly `n` distinct expressions. -/
def WellFormed (n : ℕ) (i : FirstOrderSubsumptionInstance) : Prop :=
  FirstOrderSubsumption.WellFormed i ∧ i.2.2.2.length = n ∧ i.2.2.2.Nodup

open Classical in
/-- FIRST ORDER SUBSUMPTION with exactly `n` target expressions, as a decision problem over
bitstrings. -/
noncomputable def firstOrderSubsumptionFixedTargetsDec (n : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FirstOrderSubsumptionInstance) x with
  | some i => decide (WellFormed n i ∧ FirstOrderSubsumptionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets
