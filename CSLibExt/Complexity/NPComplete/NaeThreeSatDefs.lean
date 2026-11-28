/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NOT-ALL-EQUAL 3-SAT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), NOT-ALL-EQUAL 3-SAT; T. J. Schaefer, "The complexity of satisfiability
problems" (1978).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NaeThreeSat

/-- **NOT-ALL-EQUAL 3-SAT instances.** A NOT-ALL-EQUAL 3-SAT instance is a pair $(n, \varphi)$ of
a natural number $n$, the number of variables, and a CNF formula $\varphi$. The formula is not
required to have three literals per clause; that is part of well-formedness. -/
abbrev NaeThreeSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- **Well-formed NOT-ALL-EQUAL 3-SAT instances.** A NOT-ALL-EQUAL 3-SAT instance $(n, \varphi)$
is well-formed when every clause of $\varphi$ is a list of exactly three literals, repetitions
allowed, and every literal $(x, b)$ in it has variable index $x < n$. -/
def WellFormed (i : NaeThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Not-all-equal satisfiability of an instance.** A NOT-ALL-EQUAL 3-SAT instance
$(n, \varphi)$, with $n \in \mathbb{N}$ and $\varphi$ a CNF formula, is not-all-equal satisfiable
when there are truth values $a_0, \dots, a_{n-1}$ such that, for the assignment $v$ with
$v(x) = a_x$ for $x < n$ and $v(x) = \mathrm{false}$ for $x \ge n$, every clause of $\varphi$
contains a literal satisfied by $v$ and a literal not satisfied by $v$. -/
def NaeThreeSatFeasible
    (i : NaeThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∀ clause ∈ i.2, Cslib.Logic.LegacyPL.CNFClause.Satisfies (fun x => assign.getD x false) clause ∧
      ∃ l ∈ clause, ¬ Cslib.Logic.LegacyPL.CNFLiteral.Satisfies (fun x => assign.getD x false) l

open Classical in
/-- **NOT-ALL-EQUAL 3-SAT as a decision problem.** The decision problem NOT-ALL-EQUAL 3-SAT
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
NOT-ALL-EQUAL 3-SAT instance $(n, \varphi)$ that is well-formed and not-all-equal satisfiable.
Every bitstring that decodes to no instance is rejected. -/
noncomputable def naeThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NaeThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ NaeThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NaeThreeSat
