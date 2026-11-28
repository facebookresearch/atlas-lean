/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUILIBRIUM POINT with range-sets {0, 1}: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN15] EQUILIBRIUM POINT, p. 252
(comment: "Remains NP-complete even if M_i = {0,1} for 1 ≤ i ≤ n.");
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021, Section 2.4, Theorem 2.4.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EquilibriumPointDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary

open MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint (EquilibriumPointInstance rangeSet
  EquilibriumPointFeasible)

/-- Well-formedness of an instance: the [AN15] well-formedness, and every range-set is
`Mᵢ = {0, 1}`. -/
def WellFormed (inst : EquilibriumPointInstance) : Prop :=
  EquilibriumPoint.WellFormed inst ∧ ∀ i < inst.1, ∀ z : ℤ, z ∈ rangeSet inst i ↔ z = 0 ∨ z = 1

open Classical in
/-- EQUILIBRIUM POINT with range-sets `{0, 1}` as a decision problem over bitstrings. -/
noncomputable def equilibriumPointBinaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EquilibriumPointInstance) x with
  | some i => decide (WellFormed i ∧ EquilibriumPointFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary
