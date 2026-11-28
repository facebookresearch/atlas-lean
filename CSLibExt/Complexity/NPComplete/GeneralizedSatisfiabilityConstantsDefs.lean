/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY WITH CONSTANTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED SATISFIABILITY, comment
("formulas with constants");
T. J. Schaefer, "The complexity of satisfiability problems", Proc. 10th Annual ACM Symposium on
Theory of Computing (1978), 216-226, doi:10.1145/800133.804350, Lemma 4.1 (Dichotomy Theorem for
Satisfiability-with-Constants).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityConstants

open MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed
  (Relation RelationsWellFormed IsEquivalentCNF IsAffine)

/-- One of the alternatives (3)-(6) holds for `S`: every relation is equivalent to a CNF
expression with at most one negated literal per clause, or every relation to one with at most
one un-negated literal per clause, or every relation to one with at most two literals per
clause, or every relation is the solution set of a linear system over `GF[2]`. -/
def ConstantsTractable (S : List Relation) : Prop :=
  (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.countP (fun l => !l.2) ≤ 1) ∨
    (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.countP (fun l => l.2) ≤ 1) ∨
    (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.length ≤ 2) ∨
    ∀ r ∈ S, IsAffine r

/-- An entry of a tuple: `(0, x)` is the variable `x`, `(1, 1)` the constant `T` and `(1, 0)`
the constant `F`. -/
abbrev Entry := ℕ × ℕ

/-- The truth value of an entry under the truth assignment `t`: `t x` for the variable `x`, and
the constant's own value for `T` and `F`. -/
def entryValue (t : ℕ → Bool) (e : Entry) : Bool :=
  if e.1 = 0 then t e.2 else decide (e.2 = 1)

/-- An instance for the fixed sequence `S`: the number `n` of variables and the collections
`C₁, ..., Cₘ`, each a list of tuples of entries. -/
abbrev GeneralizedSatisfiabilityConstantsInstance := ℕ × List (List (List Entry))

/-- Well-formedness of an instance: there is one collection per relation of `S`, every tuple of
`Cᵢ` has the arity `kᵢ` of `Rᵢ`, and every entry is a variable `< n` or one of the constants
`T`, `F`. -/
def WellFormed (S : List Relation) (j : GeneralizedSatisfiabilityConstantsInstance) : Prop :=
  j.2.length = S.length ∧
    ∀ p ∈ S.zip j.2, ∀ u ∈ p.2, u.length = p.1.1 ∧
      ∀ e ∈ u, (e.1 = 0 ∧ e.2 < j.1) ∨ (e.1 = 1 ∧ e.2 ≤ 1)

/-- A truth assignment `t` such that, for every `i` and every tuple `u ∈ Cᵢ`, the tuple of
values of the entries of `u` belongs to `Rᵢ`. -/
def GeneralizedSatisfiabilityConstantsFeasible (S : List Relation)
    (j : GeneralizedSatisfiabilityConstantsInstance) : Prop :=
  ∃ t : ℕ → Bool, ∀ p ∈ S.zip j.2, ∀ u ∈ p.2, u.map (entryValue t) ∈ p.1.2

open Classical in
/-- GENERALIZED SATISFIABILITY WITH CONSTANTS for the fixed sequence `S`, as a decision problem
over bitstrings. -/
noncomputable def generalizedSatisfiabilityConstantsDec (S : List Relation) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedSatisfiabilityConstantsInstance) x with
  | some j => decide (WellFormed S j ∧ GeneralizedSatisfiabilityConstantsFeasible S j)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityConstants
