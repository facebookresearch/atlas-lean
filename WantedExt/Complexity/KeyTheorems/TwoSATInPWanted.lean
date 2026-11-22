/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-SAT is in P

Source:
M. Davis, G. Logemann, and D. Loveland, "A machine program for theorem-proving", Communications
of the ACM 5 (1962), 394-397; B. Aspvall, M. F. Plass, and R. E. Tarjan, "A linear-time
algorithm for testing the truth of certain quantified Boolean formulas", Information Processing
Letters 8 (1979), 121-123.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.TwoSATInP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# 2-SAT is in P

2-SAT is in `P`, by the implication-graph / strongly connected components algorithm. The
instance is `(n, clauses)` with every clause of length at most 2; the question is whether some
assignment satisfies every clause. The matrix is the canonical `Cslib.Logic.PL.CNF`.
-/

open Classical in
/-- **2-SAT as a decision problem.** The 2-SAT decision problem accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a natural
number $n$ and a CNF formula $\varphi$ such that every clause of $\varphi$ has at most two
literals, every variable occurring in $\varphi$ is less than $n$, and there is a list
$(a_0, \dots, a_{n-1})$ of booleans such that $\varphi$ is satisfied by the assignment that
sends each variable $v < n$ to $a_v$ and every other variable to false. -/
noncomputable def twoSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × Cslib.Logic.PL.CNF) x with
  | some i => decide (
      (∀ clause ∈ i.2, clause.length ≤ 2 ∧ ∀ l ∈ clause, l.1 < i.1) ∧
      ∃ assign : List Bool, assign.length = i.1 ∧
        Cslib.Logic.PL.CNF.Satisfies (fun v => assign.getD v false) i.2)
  | none => false

/-- **2-SAT is in P.** The 2-SAT decision problem lies in the complexity class P.

Source: M. Davis, G. Logemann, and D. Loveland, "A machine program for
theorem-proving", Communications of the ACM 5 (1962), 394-397; B. Aspvall, M. F. Plass,
and R. E. Tarjan, "A linear-time algorithm for testing the truth of certain quantified
Boolean formulas", Information Processing Letters 8 (1979), 121-123. -/
public theorem_wanted two_sat_in_p :
    twoSatDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.TwoSATInP
