/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM 3DNF SATISFIABILITY is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems* (2000), problem
MINIMUM 3DNF SATISFIABILITY ("Instance: Set U of variables, collection C of conjunctive clauses
of at most three literals ... Measure: Number of clauses satisfied by the truth assignment"),
which the compendium relates to Garey and Johnson's [LO8];
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY, comment: remains
NP-complete for expressions in disjunctive normal form with three literals per disjunct
(the case "no clause satisfied" of this problem);
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Minimum3DnfSatisfiability

/-!
# MINIMUM 3DNF SATISFIABILITY is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of conjunctive clauses of at most three
literals over `U` (a literal is a variable or a negated variable), and a positive integer `K`.
QUESTION: is there a truth assignment for `U` that satisfies at most `K` clauses of `C`?

This is the decision version of the compendium's MINIMUM 3DNF SATISFIABILITY. A conjunctive
clause is satisfied when all its literals hold, as a disjunct of a DNF expression in
`MetaMathlibExt.Complexity.KeyTheorems.KarpLuby.dnfSat` (used by `NonTautology3DnfWanted`); the
encoding is that module's: `U = {u₀, …, u_{n-1}}`, a clause is a list of literals `(x, b)` (`uₓ`
if `b = true`, `¬uₓ` if `b = false`), assignments are functions `ℕ → Bool` (only their values on
`0, …, n - 1` matter), and `C` is listed with multiplicity.

Hardness: NON-TAUTOLOGY OF 3DNF ([LO8], comment) asks for an assignment satisfying no clause of
a 3DNF expression; adding the two clauses `u_n` and `¬u_n` over a fresh variable (exactly one of
them holds under every assignment) and taking `K = 1` reduces it to this problem. Membership in
NP: an assignment is a certificate. Negating every clause turns the question into whether some
assignment satisfies at least `|C| - K` disjunctive clauses of at most three literals (MAXIMUM
3-SATISFIABILITY).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, the clauses (each a list of
literals `(x, b)`), and the bound `K`. -/
abbrev Minimum3DnfSatisfiabilityInstance := ℕ × List (List (ℕ × Bool)) × ℕ

/-- The number of clauses of `C` (with multiplicity) all of whose literals hold under `σ`. -/
def satisfiedCount (σ : ℕ → Bool) (C : List (List (ℕ × Bool))) : ℕ :=
  (C.filter fun t => decide (∀ p ∈ t, σ p.1 = p.2)).length

/-- Well-formedness of an instance: every clause has at most three literals, every literal names
one of `u₀, …, u_{n-1}`, and `K` is positive. -/
def WellFormed (i : Minimum3DnfSatisfiabilityInstance) : Prop :=
  (∀ t ∈ i.2.1, t.length ≤ 3 ∧ ∀ l ∈ t, l.1 < i.1) ∧ 0 < i.2.2

/-- Some truth assignment satisfies at most `K` clauses. -/
def Minimum3DnfSatisfiabilityFeasible (i : Minimum3DnfSatisfiabilityInstance) : Prop :=
  ∃ σ : ℕ → Bool, satisfiedCount σ i.2.1 ≤ i.2.2

open Classical in
/-- MINIMUM 3DNF SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def minimum3DnfSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Minimum3DnfSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ Minimum3DnfSatisfiabilityFeasible i)
  | none => false

/-- **MINIMUM 3DNF SATISFIABILITY is NP-complete.** Source: Crescenzi and Kann, MINIMUM 3DNF
SATISFIABILITY; Garey and Johnson (1979), [LO8] (the case of no satisfied clause); Cook (1971). -/
public theorem_wanted minimum3DnfSatisfiability_npComplete :
    minimum3DnfSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimum3DnfSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.Minimum3DnfSatisfiability
