/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 1-IN-3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), ONE-IN-THREE 3-SAT; T. J. Schaefer, "The complexity of satisfiability
problems" (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneInThreeSat

/-!
# 1-IN-3-SAT is NP-complete

A 3-CNF formula: every clause has exactly three literals. The question is whether some
assignment makes exactly one literal true in every clause.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **1-in-3-SAT instances.** A 1-in-3-SAT instance is a pair $(n, \varphi)$ of a natural number
$n$, the number of variables, and a CNF formula $\varphi$.

Any CNF formula is allowed here; that $\varphi$ has three literals per clause, all over the
variables below $n$, is required separately by well-formedness. -/
abbrev OneInThreeSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- **Well-formed 1-in-3-SAT instances.** A 1-in-3-SAT instance $(n, \varphi)$ is well formed
when every clause of $\varphi$ has exactly three literals and every literal $(x, b)$ in it has
variable index $x < n$. -/
def WellFormed (i : OneInThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Feasible 1-in-3-SAT instances.** A 1-in-3-SAT instance $(n, \varphi)$ is feasible when
there is an assignment $v$ of truth values to the variables $0, \dots, n - 1$, with variables
$y \ge n$ read as false, such that every clause of $\varphi$ has exactly one position holding a
literal $(y, b)$ with $v(y) = b$. -/
def OneInThreeSatFeasible
    (i : OneInThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∀ clause ∈ i.2, ∃ k < clause.length,
      Cslib.Logic.PL.CNFLiteral.Satisfies (fun x => assign.getD x false)
        (clause.getD k (0, false)) ∧
        ∀ j < clause.length,
          Cslib.Logic.PL.CNFLiteral.Satisfies (fun x => assign.getD x false)
            (clause.getD j (0, false)) → j = k

open Classical in
/-- **The 1-in-3-SAT decision problem.** The 1-in-3-SAT decision problem accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a
natural number $n$ and a CNF formula $\varphi$ such that every clause of $\varphi$ has exactly
three literals, every literal $(y, b)$ of $\varphi$ has variable index $y < n$, and some
assignment $v$ of truth values to the variables $0, \dots, n - 1$ makes exactly one position
of every clause hold a literal $(y, b)$ with $v(y) = b$. It rejects every bitstring that does
not decode. -/
noncomputable def oneInThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneInThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ OneInThreeSatFeasible i)
  | none => false

/-- **1-IN-3-SAT is NP-complete.** The 1-in-3-SAT decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), ONE-IN-THREE 3-SAT; T.
J. Schaefer, "The complexity of satisfiability problems" (1978). -/
public theorem_wanted oneInThreeSat_npComplete :
    oneInThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oneInThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.OneInThreeSat
