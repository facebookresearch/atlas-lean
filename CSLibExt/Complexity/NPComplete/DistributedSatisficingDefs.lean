/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZERO-COMMUNICATION DISTRIBUTED PROTOCOL DESIGN (DISTRIBUTED SATISFICING): definitions

Source:
C. H. Papadimitriou and J. Tsitsiklis, "On the complexity of designing distributed protocols",
Information and Control 53 (1982), 211-218, doi:10.1016/S0019-9958(82)91034-8, Section 2
(DISTRIBUTED SATISFICING) and Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistributedSatisficing

/-- An instance: `|Y_I|`, `|Y_II|`, `|U_I|`, `|U_II|`, and the list of allowed quadruples
`(y_I, y_II, u_I, u_II)`. -/
abbrev DistributedSatisficingInstance := ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: every listed quadruple names an observation of agent I, an
observation of agent II, a decision of agent I and a decision of agent II. -/
def WellFormed (i : DistributedSatisficingInstance) : Prop :=
  ∀ q ∈ i.2.2.2.2, q.1 < i.1 ∧ q.2.1 < i.2.1 ∧ q.2.2.1 < i.2.2.1 ∧ q.2.2.2 < i.2.2.2.1

/-- There are decision rules `γ_I : Y_I → U_I` and `γ_II : Y_II → U_II` such that for every
pair of observations the pair of decisions is allowed. -/
def DistributedSatisficingFeasible (i : DistributedSatisficingInstance) : Prop :=
  ∃ (gI : Fin i.1 → Fin i.2.2.1) (gII : Fin i.2.1 → Fin i.2.2.2.1),
    ∀ (yI : Fin i.1) (yII : Fin i.2.1),
      ((yI : ℕ), (yII : ℕ), (gI yI : ℕ), (gII yII : ℕ)) ∈ i.2.2.2.2

open Classical in
/-- ZERO-COMMUNICATION DISTRIBUTED PROTOCOL DESIGN as a decision problem over bitstrings. -/
noncomputable def distributedSatisficingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DistributedSatisficingInstance) x with
  | some i => decide (WellFormed i ∧ DistributedSatisficingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DistributedSatisficing
