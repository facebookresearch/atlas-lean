/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK PARTITION with coefficients bounded by a fixed K: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9, problem [9] WEAK PARTITION, comment ("This problem
remains NP-complete even if we allow solutions with |xᵢ| as large as K, for any fixed K");
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Department of Mathematics, University of Amsterdam (1981),
Theorem 1 (BOUNDED HOMOGENEOUS LINEAR EQUATION).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Order.Ring.Abs
public import CSLibExt.Complexity.NPComplete.WeakPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakPartitionBoundedCoefficients

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)
open MetaMathlibExt.Complexity.NPComplete.WeakPartition (WellFormed)

/-- Some nonzero integer vector `x` with `|xᵢ| ≤ K` for all `i` satisfies
`∑ᵢ xᵢ · s(aᵢ) = 0`. -/
def WeakPartitionBoundedCoefficientsFeasible (K : ℕ) (i : PartitionInstance) : Prop :=
  ∃ x : Fin i.length → ℤ, x ≠ 0 ∧ (∀ j, |x j| ≤ K) ∧ ∑ j, x j * (i.get j : ℤ) = 0

open Classical in
/-- WEAK PARTITION with coefficients bounded by `K` as a decision problem over bitstrings. -/
noncomputable def weakPartitionBoundedCoefficientsDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (WellFormed i ∧ WeakPartitionBoundedCoefficientsFeasible K i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeakPartitionBoundedCoefficients
