/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ONES 3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MINIMUM ONES 3-SAT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat

/-!
# MINIMUM ONES 3-SAT is NP-complete

A 3-CNF formula and a bound `K`. The question is whether some satisfying assignment sets at
most `K` variables to true.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM ONES 3-SAT instances.** An instance of MINIMUM ONES 3-SAT is a triple
$(n, \varphi, K)$ of a natural number $n$ (the number of variables), a CNF formula $\varphi$ and a
natural number $K$ (the bound). No condition is placed on $\varphi$ here; clauses of exactly three
literals are required separately, by well-formedness. -/
abbrev MinOnesThreeSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- **Well-formed MINIMUM ONES 3-SAT instances.** A triple $(n, \varphi, K)$ of a natural number
$n$, a CNF formula $\varphi$ and a natural number $K$ is well formed when every clause of $\varphi$
is a list of exactly three literals and every literal of every clause has variable index less
than $n$. -/
def WellFormed (i : MinOnesThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Feasible MINIMUM ONES 3-SAT instances.** A triple $(n, \varphi, K)$ of a natural number $n$,
a CNF formula $\varphi$ and a natural number $K$ is feasible when there is an assignment of truth
values to the variables $0, \dots, n-1$ that, with every variable $x \ge n$ set to false,
satisfies $\varphi$ and sets at most $K$ of the variables $0, \dots, n-1$ to true. -/
def MinOnesThreeSatFeasible
    (i : MinOnesThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2.1) ∧
    (assign.filter (fun b => b)).length ≤ i.2.2

open Classical in
/-- **The MINIMUM ONES 3-SAT decision problem.** MINIMUM ONES 3-SAT is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ and a natural number $K$
such that every clause of $\varphi$ is a list of exactly three literals whose variables are all
less than $n$, and some assignment of truth values to the variables $0, \dots, n-1$ satisfies
$\varphi$ and sets at most $K$ of them to true. Every other bitstring is rejected. -/
noncomputable def minOnesThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinOnesThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ MinOnesThreeSatFeasible i)
  | none => false

/-- **MINIMUM ONES 3-SAT is NP-complete.** Let MINIMUM ONES 3-SAT be the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ and a natural number $K$
such that every clause of $\varphi$ is a list of exactly three literals whose variables are all
less than $n$, and some assignment of truth values to the variables $0, \dots, n-1$ satisfies
$\varphi$ and sets at most $K$ of them to true. Then MINIMUM ONES 3-SAT belongs to NP, and every
decision problem $L$ in NP reduces to it by a polynomial-time many-one reduction: there is a
polynomial-time computable map $f$ on bitstrings such that, for every bitstring $x$, $L$ accepts
$x$ exactly when MINIMUM ONES 3-SAT accepts $f(x)$.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability: A Guide to the Theory of NP-Completeness* (1979), MINIMUM ONES 3-SAT. -/
public theorem_wanted minOnesThreeSat_npComplete :
    minOnesThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minOnesThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat
