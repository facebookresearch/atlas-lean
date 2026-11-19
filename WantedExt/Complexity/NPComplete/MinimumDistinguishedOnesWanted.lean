/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISTINGUISHED ONES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM DISTINGUISHED ONES (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (satisfiability with at most three literals per clause is
NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes

/-!
# MINIMUM DISTINGUISHED ONES is NP-complete

INSTANCE: disjoint sets `X`, `Z` of variables, a collection `C` of disjunctive clauses of at
most 3 literals over `X ∪ Z` (a literal is a variable or a negated variable), and a bound `K`.
QUESTION: is there a truth assignment for `X` and `Z` that satisfies every clause of `C` and
sets at most `K` variables of `Z` to true?

This is the decision version of the compendium's MINIMUM DISTINGUISHED ONES (measure: the
number of `Z` variables set to true), shown NPO PB-complete by Kann. NP-hardness of the decision
version is immediate: with `Z = ∅` and `K = 0` it asks whether a formula with at most three
literals per clause is satisfiable, which Karp (1972) proved NP-complete.

The variables are `0, …, n - 1`; `Z` is listed (without repetition) and `X` is the rest. The
formula uses the repository's `Cslib.Logic.PL.CNF` (a clause is a list of literals
`(variable, polarity)`) with its semantics `Cslib.Logic.PL.CNF.Satisfies`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, the list of distinguished variables `Z`, the
clauses, and the bound `K`. -/
abbrev MinimumDistinguishedOnesInstance := ℕ × List ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance: `Z` lists distinct variables below `n`, and every clause
has at most 3 literals, all over variables below `n`. -/
def WellFormed (i : MinimumDistinguishedOnesInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ z ∈ i.2.1, z < i.1) ∧
    ∀ clause ∈ i.2.2.1, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1

/-- Some assignment of the `n` variables satisfies every clause and sets at most `K` variables
of `Z` to true. -/
def MinimumDistinguishedOnesFeasible (i : MinimumDistinguishedOnesInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2.2.1 ∧
    (i.2.1.filter fun z => assign.getD z false).length ≤ i.2.2.2

open Classical in
/-- MINIMUM DISTINGUISHED ONES as a decision problem over bitstrings. -/
noncomputable def minimumDistinguishedOnesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumDistinguishedOnesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumDistinguishedOnesFeasible i)
  | none => false

/-- **MINIMUM DISTINGUISHED ONES is NP-complete.** Source: Crescenzi and Kann, MINIMUM DISTINGUISHED
ONES; Kann (1993); Karp (1972). -/
public theorem_wanted minimumDistinguishedOnes_npComplete :
    minimumDistinguishedOnesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumDistinguishedOnesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes
