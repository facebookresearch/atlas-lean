/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM 2-SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MINIMUM 2-SATISFIABILITY; R. Kohli, R. Krishnamurti, and P. Mirchandani,
"The minimum satisfiability problem" (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinTwoSat

/-!
# MINIMUM 2-SATISFIABILITY is NP-complete

A 2-CNF formula (every clause has at most two literals) and a bound `K`. The question is
whether some assignment satisfies at most `K` clauses.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM 2-SATISFIABILITY instances.** An instance of MINIMUM 2-SATISFIABILITY is a triple
$(n, \varphi, K)$ of a natural number $n$ (the number of variables), a CNF formula $\varphi$ and a
natural number $K$ (the bound). No condition is placed on $\varphi$ here; clauses of at most two
literals are required separately, by well-formedness. -/
abbrev MinTwoSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- **Well-formed MINIMUM 2-SATISFIABILITY instances.** A triple $(n, \varphi, K)$ of a natural
number $n$, a CNF formula $\varphi$ and a natural number $K$ is well formed when every clause of
$\varphi$ has at most two literals and every literal of every clause has variable index less than
$n$. -/
def WellFormed (i : MinTwoSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length ≤ 2 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Feasible MINIMUM 2-SATISFIABILITY instances.** A triple $(n, \varphi, K)$ of a natural number
$n$, a CNF formula $\varphi$ with clauses $C_0, \dots, C_{m-1}$ and a natural number $K$ is
feasible when there is an assignment of truth values to the variables $0, \dots, n-1$ that, with
every variable $x \ge n$ set to false, satisfies $C_j$ for at most $K$ indices $j < m$. -/
def MinTwoSatFeasible
    (i : MinTwoSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ S : Finset ℕ, S ⊆ Finset.range i.2.1.length ∧ S.card ≤ i.2.2 ∧
      ∀ j < i.2.1.length,
        Cslib.Logic.PL.CNFClause.Satisfies (fun x => assign.getD x false)
          (i.2.1.getD j []) ↔ j ∈ S

open Classical in
/-- **The MINIMUM 2-SATISFIABILITY decision problem.** MINIMUM 2-SATISFIABILITY is the decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ with
clauses $C_0, \dots, C_{m-1}$ and a natural number $K$ such that every clause has at most two
literals, all with variables less than $n$, and some assignment of truth values to the variables
$0, \dots, n-1$ satisfies $C_j$ for at most $K$ indices $j < m$. Every other bitstring is
rejected. -/
noncomputable def minTwoSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinTwoSatInstance) x with
  | some i => decide (WellFormed i ∧ MinTwoSatFeasible i)
  | none => false

/-- **MINIMUM 2-SATISFIABILITY is NP-complete.** Let MINIMUM 2-SATISFIABILITY be the decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ with
clauses $C_0, \dots, C_{m-1}$ and a natural number $K$ such that every clause has at most two
literals, all with variables less than $n$, and some assignment of truth values to the variables
$0, \dots, n-1$ satisfies $C_j$ for at most $K$ indices $j < m$. Then MINIMUM 2-SATISFIABILITY
belongs to NP, and every decision problem $L$ in NP reduces to it by a polynomial-time many-one
reduction: there is a polynomial-time computable map $f$ on bitstrings such that, for every
bitstring $x$, $L$ accepts $x$ exactly when MINIMUM 2-SATISFIABILITY accepts $f(x)$.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), MINIMUM
2-SATISFIABILITY; R. Kohli, R. Krishnamurti, and P. Mirchandani, "The minimum
satisfiability problem" (1994). -/
public theorem_wanted minTwoSat_npComplete :
    minTwoSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minTwoSatDec

end MetaMathlibExt.Complexity.NPComplete.MinTwoSat
