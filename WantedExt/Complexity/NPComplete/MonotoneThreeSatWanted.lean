/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOTONE 3-SAT is NP-complete

Source:
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the Tenth Annual
ACM Symposium on Theory of Computing (STOC 1978), ACM, 1978, 216-226 (dichotomy theorem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

/-!
# MONOTONE 3-SAT is NP-complete

A 3-CNF formula in which every clause is monotone, that is, all-positive or all-negative. The
question is whether the formula is satisfiable.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Monotone 3-SAT instances.** A monotone 3-SAT instance is a pair $(n, \varphi)$ of a
natural number $n$, the number of variables, and a CNF formula $\varphi$. -/
abbrev MonotoneThreeSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- **Well-formed monotone 3-SAT instances.** A monotone 3-SAT instance $(n, \varphi)$ is well
formed when every clause of the CNF formula $\varphi$ is a list of exactly three literals
(repetitions allowed), each with a variable below $n$, and the literals of each clause are all
positive or all negative. -/
def WellFormed (i : MonotoneThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ (∀ l ∈ clause, l.1 < i.1) ∧
    ((∀ l ∈ clause, l.2 = true) ∨ (∀ l ∈ clause, l.2 = false)))

/-- **Satisfiable monotone 3-SAT instances.** A monotone 3-SAT instance $(n, \varphi)$ is
feasible when there is a list of $n$ truth values $a_0, \dots, a_{n-1}$ such that the assignment
sending each variable $x < n$ to $a_x$ and every variable $x \ge n$ to false satisfies the CNF
formula $\varphi$. -/
def MonotoneThreeSatFeasible
    (i : MonotoneThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- **MONOTONE 3-SAT as a decision problem.** The decision problem MONOTONE 3-SAT accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a pair
$(n, \varphi)$ of a natural number $n$ and a CNF formula $\varphi$ such that every clause of
$\varphi$ is a list of exactly three literals (repetitions allowed), every literal of $\varphi$
has a variable below $n$, the literals of each clause are all positive or all negative, and
some assignment of truth values to the variables $0, \dots, n-1$, with every other variable
false, satisfies $\varphi$. Bitstrings that do not decode are rejected. -/
noncomputable def monotoneThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonotoneThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ MonotoneThreeSatFeasible i)
  | none => false

/-- **MONOTONE 3-SAT is NP-complete.** The decision problem MONOTONE 3-SAT belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to MONOTONE 3-SAT.

Source: T. J. Schaefer, "The complexity of
satisfiability problems", Proceedings of the Tenth Annual ACM Symposium on Theory of
Computing (STOC 1978), ACM, 1978, 216-226 (dichotomy theorem). -/
public theorem_wanted monotoneThreeSat_npComplete :
    monotoneThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monotoneThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat
