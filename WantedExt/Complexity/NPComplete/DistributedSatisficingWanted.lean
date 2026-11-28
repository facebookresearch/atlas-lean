/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZERO-COMMUNICATION DISTRIBUTED PROTOCOL DESIGN (DISTRIBUTED SATISFICING) is NP-complete

Source:
C. H. Papadimitriou and J. Tsitsiklis, "On the complexity of designing distributed protocols",
Information and Control 53 (1982), 211-218, doi:10.1016/S0019-9958(82)91034-8, Section 2
(DISTRIBUTED SATISFICING) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistributedSatisficing

/-!
# ZERO-COMMUNICATION DISTRIBUTED PROTOCOL DESIGN (DISTRIBUTED SATISFICING) is NP-complete

Two distant agents I and II observe `y_I ∈ Y_I` and `y_II ∈ Y_II` and must each decide,
without any communication, `u_I ∈ U_I` and `u_II ∈ U_II`; the pair of decisions must belong to a
prescribed set `S(y_I, y_II) ⊆ U_I × U_II`.

INSTANCE: finite sets `Y_I`, `U_I`, `Y_II`, `U_II` and a function
`S : Y_I × Y_II → 2^(U_I × U_II)`.
QUESTION: are there functions `γ_I : Y_I → U_I` and `γ_II : Y_II → U_II` such that
`(γ_I(y_I), γ_II(y_II)) ∈ S(y_I, y_II)` for all `y_I ∈ Y_I` and `y_II ∈ Y_II`?

This is Papadimitriou and Tsitsiklis's DISTRIBUTED SATISFICING problem (Section 2). Their
Theorem 1 proves it NP-complete when the decision sets have at least two and at least three
elements (it is polynomial when both have at most two), so the general problem is NP-complete.

Encoding: the four finite sets are `Fin a`, `Fin b`, `Fin c`, `Fin d` for `a = |Y_I|`,
`b = |Y_II|`, `c = |U_I|`, `d = |U_II|`, and `S` is the list of the allowed quadruples
`(y_I, y_II, u_I, u_II)`, that is, `(u_I, u_II) ∈ S(y_I, y_II)` exactly when the quadruple is
listed (repetitions are harmless). Well-formedness asks that every listed entry is in range.
The instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **ZERO-COMMUNICATION DISTRIBUTED PROTOCOL DESIGN is NP-complete.** Source: Papadimitriou and
Tsitsiklis (1982), Theorem 1. -/
public theorem_wanted distributedSatisficing_npComplete :
    distributedSatisficingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L distributedSatisficingDec

end MetaMathlibExt.Complexity.NPComplete.DistributedSatisficing
