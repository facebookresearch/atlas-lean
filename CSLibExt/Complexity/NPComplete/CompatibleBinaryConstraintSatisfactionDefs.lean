/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPATIBLE BINARY CONSTRAINT SATISFACTION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMPATIBLE BINARY CONSTRAINT SATISFACTION, which records it as equivalent to
MAXIMUM CLIQUE under PTAS-reduction following A. Jagota, "Constraint satisfaction and maximum
clique", Working Notes, AAAI Spring Symposium on AI and NP-hard Problems, Stanford University
(1993), 92-97 (not available to us);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (CLIQUE, the special case with one-value domains).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BinaryCspDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CompatibleBinaryConstraintSatisfaction

open BinaryCsp (BinaryCspInstance)

/-- An instance: the domains and constraints (`BinaryCspWanted`'s instance) and the bound
`K`. -/
abbrev CompatibleBinaryConstraintSatisfactionInstance := BinaryCspInstance × ℕ

/-- Well-formedness of an instance: every constraint `(i, j, C)` has `i < j < n` and
`C ⊆ Dᵢ × Dⱼ`, every pair `i < j < n` has exactly one constraint, and `K` is positive. -/
def WellFormed (i : CompatibleBinaryConstraintSatisfactionInstance) : Prop :=
  (∀ c ∈ i.1.2, c.1 < c.2.1 ∧ c.2.1 < i.1.1.length ∧
    ∀ p ∈ c.2.2, p.1 ∈ i.1.1.getD c.1 [] ∧ p.2 ∈ i.1.1.getD c.2.1 []) ∧
    (i.1.2.map fun c => (c.1, c.2.1)).Nodup ∧
    (∀ j < i.1.1.length, ∀ k < j, ∃ c ∈ i.1.2, c.1 = k ∧ c.2.1 = j) ∧
    0 < i.2

/-- Some set `U` of at least `K` variables has an assignment giving each variable of `U` a value
of its domain and satisfying the constraint of every pair of variables of `U`. -/
def CompatibleBinaryConstraintSatisfactionFeasible
    (i : CompatibleBinaryConstraintSatisfactionInstance) : Prop :=
  ∃ U : Finset ℕ, ∃ assign : ℕ → ℕ, U ⊆ Finset.range i.1.1.length ∧ i.2 ≤ U.card ∧
    (∀ x ∈ U, assign x ∈ i.1.1.getD x []) ∧
    ∀ c ∈ i.1.2, c.1 ∈ U → c.2.1 ∈ U → (assign c.1, assign c.2.1) ∈ c.2.2

open Classical in
/-- COMPATIBLE BINARY CONSTRAINT SATISFACTION as a decision problem over bitstrings. -/
noncomputable def compatibleBinaryConstraintSatisfactionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CompatibleBinaryConstraintSatisfactionInstance) x with
  | some i => decide (WellFormed i ∧ CompatibleBinaryConstraintSatisfactionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CompatibleBinaryConstraintSatisfaction
