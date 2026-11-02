/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM 2-SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MAXIMUM 2-SATISFIABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxTwoSat

/-!
# MAXIMUM 2-SATISFIABILITY is NP-complete

A 2-CNF formula (every clause has at most two literals) and a bound `K`. The question is
whether some assignment satisfies at least `K` clauses.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAX-2SAT instances.** A MAX-2SAT instance is a triple $(n, \varphi, K)$ of a natural number
$n$ (the number of variables), a CNF formula $\varphi$ and a natural number $K$ (the bound). The
type does not restrict clause lengths; that clauses have at most two literals is part of
well-formedness. -/
abbrev MaxTwoSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- **Well-formed MAX-2SAT instances.** A MAX-2SAT instance $(n, \varphi, K)$ is well formed when
every clause of $\varphi$ has at most two literals and every literal $(x, b)$ in it has variable
index $x < n$. -/
def WellFormed (i : MaxTwoSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length ≤ 2 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Feasible MAX-2SAT instances.** A MAX-2SAT instance $(n, \varphi, K)$ is feasible when there
are truth values $a_0, \dots, a_{n-1}$ such that at least $K$ of the clauses in the list $\varphi$,
counted with multiplicity, are satisfied by the assignment $v$ with $v(x) = a_x$ for $x < n$ and
$v(x) = \mathrm{false}$ for $x \ge n$. -/
def MaxTwoSatFeasible
    (i : MaxTwoSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ sub : Cslib.Logic.PL.CNF, sub.Sublist i.2.1 ∧ i.2.2 ≤ sub.length ∧
      ∀ clause ∈ sub, Cslib.Logic.PL.CNFClause.Satisfies
        (fun x => assign.getD x false) clause

open Classical in
/-- **MAXIMUM 2-SATISFIABILITY as a decision problem.** The decision problem MAXIMUM
2-SATISFIABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of MAX-2SAT instances, to an instance $(n, \varphi, K)$ that is well formed (every clause
of $\varphi$ has at most two literals, and every literal has variable index less than $n$) and
feasible (some assignment of truth values to the $n$ variables satisfies at least $K$ of the
clauses of $\varphi$, counted with multiplicity). Bitstrings that do not decode, and bitstrings
that decode to instances that are not well formed, are rejected. -/
noncomputable def maxTwoSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxTwoSatInstance) x with
  | some i => decide (WellFormed i ∧ MaxTwoSatFeasible i)
  | none => false

/-- **MAXIMUM 2-SATISFIABILITY is NP-complete.** The decision problem MAXIMUM 2-SATISFIABILITY
over bitstrings lies in NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), MAXIMUM
2-SATISFIABILITY. -/
public theorem_wanted maxTwoSat_npComplete :
    maxTwoSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxTwoSatDec

end MetaMathlibExt.Complexity.NPComplete.MaxTwoSat
