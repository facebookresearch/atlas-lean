/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOTTLENECK TRAVELING SALESMAN with distances 1 and 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND24] BOTTLENECK TRAVELING SALESMAN,
comment;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo



open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

/-- Well-formedness of an instance: a well-formed BOTTLENECK TRAVELING SALESMAN instance in
which the distance between any two distinct cities is `1` or `2`. -/
def WellFormed (i : BottleneckTravelingSalesmanInstance) : Prop :=
  BottleneckTravelingSalesman.WellFormed i ∧
    ∀ a < i.1, ∀ b < i.1, a ≠ b → dist i.2.1 a b = 1 ∨ dist i.2.1 a b = 2

open Classical in
/-- BOTTLENECK TRAVELING SALESMAN with distances 1 and 2 as a decision problem over
bitstrings. -/
noncomputable def bottleneckTravelingSalesmanDistancesOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BottleneckTravelingSalesmanInstance) x with
  | some i =>
      decide (WellFormed i ∧ BottleneckTravelingSalesman.BottleneckTravelingSalesmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo
