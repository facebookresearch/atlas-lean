/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-SAT WITH BOUNDED OCCURRENCES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), 3-SAT with bounded occurrences; C. A. Tovey, "A simplified NP-complete
satisfiability problem" (1984).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedOccurrenceThreeSat

/-- **Bounded-occurrence 3-SAT instances.** A bounded-occurrence 3-SAT instance is a pair
$(n, \varphi)$ of a natural number $n$, the number of variables, and a CNF formula $\varphi$. -/
abbrev BoundedOccurrenceThreeSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- **Well-formed bounded-occurrence 3-SAT instances.** A bounded-occurrence 3-SAT instance
$(n, \varphi)$ is well formed when every clause of $\varphi$ is a list of exactly three literals,
not necessarily distinct, every literal of $\varphi$ has a variable less than $n$, and for every
variable $v < n$ at most four of the literals in the clauses of $\varphi$, counted with
multiplicity and with either polarity, have variable $v$. -/
def WellFormed (i : BoundedOccurrenceThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    ∀ v < i.1, (i.2.flatten.filter (fun l => l.1 == v)).length ≤ 4

/-- **Satisfiable bounded-occurrence 3-SAT instances.** A bounded-occurrence 3-SAT instance
$(n, \varphi)$ is satisfiable when there is a list $(a_0, \dots, a_{n-1})$ of booleans such that
$\varphi$ is satisfied by the assignment sending each variable $x < n$ to $a_x$ and every
variable $x \ge n$ to false. -/
def BoundedOccurrenceThreeSatFeasible
    (i : BoundedOccurrenceThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- **3-SAT with bounded occurrences as a decision problem.** The decision problem 3-SAT WITH
BOUNDED OCCURRENCES accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of bounded-occurrence 3-SAT instances, to an instance that is well formed and
satisfiable; it rejects every other bitstring, including every bitstring that does not decode. -/
noncomputable def boundedOccurrenceThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedOccurrenceThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ BoundedOccurrenceThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedOccurrenceThreeSat
