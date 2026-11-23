/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM DISTINGUISHED ONES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM DISTINGUISHED ONES;
V. Kann, *On the Approximability of NP-complete Optimization Problems*, PhD thesis, Royal
Institute of Technology, Stockholm (1992), problem [7.13] Max distinguished ones;
A. Panconesi and D. Ranjan, "Quantifiers and approximation", Theoretical Computer Science 107
(1993), 145-163, doi:10.1016/0304-3975(93)90259-V;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO2] 3-SATISFIABILITY (the special case described
below), from S. A. Cook, "The complexity of theorem-proving procedures", Proc. 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes

/-!
# MAXIMUM DISTINGUISHED ONES is NP-complete

INSTANCE: disjoint sets `X`, `Z` of variables, a collection `C` of disjunctive clauses of at
most 3 literals over `X ∪ Z`, and a positive integer `K`. QUESTION: is there a truth assignment
for `X` and `Z` that satisfies every clause of `C` and sets at least `K` variables of `Z` to
true?

This is the decision version of MAXIMUM DISTINGUISHED ONES in the compendium of Crescenzi and
Kann (Kann's Max Dones), whose measure is the number of variables of `Z` set to true. When `Z`
is a single variable that occurs in no clause and `K = 1`, the question is whether `C` is
satisfiable, i.e. 3-SATISFIABILITY with clauses of at most three literals.

The variables are `0, …, |X| + |Z| - 1`: `X` is `0, …, |X| - 1` and `Z` is
`|X|, …, |X| + |Z| - 1`. The clauses are a `Cslib.Logic.PL.CNF` (a literal is a variable with
its polarity), each with at most three literals over these variables, and an assignment is a
list of `|X| + |Z|` truth values.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: `|X|`, `|Z|`, the clauses `C`, and the bound `K`. -/
abbrev MaximumDistinguishedOnesInstance := ℕ × ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance: every clause has at most three literals, all over the
variables `0, …, |X| + |Z| - 1`, and `K` is positive. -/
def WellFormed (i : MaximumDistinguishedOnesInstance) : Prop :=
  (∀ clause ∈ i.2.2.1, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1 + i.2.1) ∧ 0 < i.2.2.2

/-- Some assignment satisfies every clause and sets at least `K` variables of `Z` to true. -/
def MaximumDistinguishedOnesFeasible (i : MaximumDistinguishedOnesInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 + i.2.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2.2.1 ∧
    i.2.2.2 ≤ ((List.range i.2.1).filter fun j => assign.getD (i.1 + j) false).length

open Classical in
/-- MAXIMUM DISTINGUISHED ONES as a decision problem over bitstrings. -/
noncomputable def maximumDistinguishedOnesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumDistinguishedOnesInstance) x with
  | some i => decide (WellFormed i ∧ MaximumDistinguishedOnesFeasible i)
  | none => false

/-- **MAXIMUM DISTINGUISHED ONES is NP-complete.** Source: Crescenzi and Kann, MAXIMUM
DISTINGUISHED ONES; Kann (1992), [7.13]. -/
public theorem_wanted maximumDistinguishedOnes_npComplete :
    maximumDistinguishedOnesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumDistinguishedOnesDec

end MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes
