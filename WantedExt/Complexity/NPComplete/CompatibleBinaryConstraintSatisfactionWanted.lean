/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPATIBLE BINARY CONSTRAINT SATISFACTION is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BinaryCspWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CompatibleBinaryConstraintSatisfaction

open BinaryCsp (BinaryCspInstance)

/-!
# COMPATIBLE BINARY CONSTRAINT SATISFACTION is NP-complete

INSTANCE: variables `x₁, …, x_n` taking values in the sets `D₁, …, D_n`, binary compatibility
constraints `C(xᵢ, xⱼ) ⊆ Dᵢ × Dⱼ` for `1 ≤ i < j ≤ n`, and a positive integer `K`. QUESTION: is
there an assignment of values to a subset `U` of at least `K` variables such that every
variable of `U` gets a value of its domain and, for all pairs `xᵢ, xⱼ` in `U` with `i < j`,
the values `(dᵢ, dⱼ)` lie in `C(xᵢ, xⱼ)`?

This is the decision version of MAXIMUM COMPATIBLE BINARY CONSTRAINT SATISFACTION in the
compendium of Crescenzi and Kann, whose measure is the number of variables assigned. With
one-value domains it is CLIQUE: `Dᵢ = {0}` and `C(xᵢ, xⱼ) = {(0, 0)}` exactly when `ij` is an
edge.

The instance reuses the type of `BinaryCspWanted` (variables are `0, …, n - 1`, domains are
lists of values, a constraint is a triple `(i, j, C)` with `C` the list of allowed pairs) and
adds `K`. As in the source, every pair `i < j` has exactly one constraint: `WellFormed` asks
for one triple per pair, with `i < j < n` and `C ⊆ Dᵢ × Dⱼ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COMPATIBLE BINARY CONSTRAINT SATISFACTION is NP-complete.** Source: Crescenzi and Kann,
MAXIMUM COMPATIBLE BINARY CONSTRAINT SATISFACTION; Karp (1972), CLIQUE. -/
public theorem_wanted compatibleBinaryConstraintSatisfaction_npComplete :
    compatibleBinaryConstraintSatisfactionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L compatibleBinaryConstraintSatisfactionDec

end MetaMathlibExt.Complexity.NPComplete.CompatibleBinaryConstraintSatisfaction
