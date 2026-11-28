/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITTING SET with subsets of size at most 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP8] HITTING SET, p. 222, comment:
"Remains NP-complete even if |c| ≤ 2 for all c ∈ C";
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (VERTEX COVER).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HittingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo

/-- Well-formedness of an instance: the instance is well-formed for HITTING SET, and every
subset in `C` has at most two elements. -/
def WellFormed (i : HittingSet.HittingSetInstance) : Prop :=
  HittingSet.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 2

open Classical in
/-- HITTING SET with subsets of size at most 2 as a decision problem over bitstrings. -/
noncomputable def hittingSetSizeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HittingSet.HittingSetInstance) x with
  | some i => decide (WellFormed i ∧ HittingSet.HittingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo
