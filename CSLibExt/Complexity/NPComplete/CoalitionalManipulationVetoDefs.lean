/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates: definitions

Source:
V. Conitzer, T. Sandholm and J. Lang, "When are elections with few candidates hard to
manipulate?", Journal of the ACM 54(3) (2007), Article 14, doi:10.1145/1236457.1236461,
Definition 1, Theorem 6 and Corollary 1 (reduction from PARTITION).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CoalitionalManipulationBordaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto

open MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda

/-- The veto scoring vector for three candidates, `(1, 1, 0)`. -/
def vetoVector : List ℕ := [1, 1, 0]

/-- The manipulators can make `p` the unique veto winner. -/
def CoalitionalManipulationVetoFeasible (i : CoalitionalManipulationInstance) : Prop :=
  ManipulationFeasible vetoVector i

open Classical in
/-- CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates as a
decision problem over bitstrings. -/
noncomputable def coalitionalManipulationVetoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoalitionalManipulationInstance) x with
  | some i => decide (WellFormed i ∧ CoalitionalManipulationVetoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto
