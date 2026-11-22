/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling

/-!
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Jobs with processing times and precedence constraints, `m` identical machines, and a deadline
`D`. The question is whether there are start times and a machine assignment meeting all
precedence constraints and the deadline, with no machine running two jobs at once (same-machine
non-overlap).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A precedence-multiprocessor instance: job durations, precedence pairs, machine count,
deadline. -/
abbrev PrecedenceMultiprocessorSchedulingInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : PrecedenceMultiprocessorSchedulingInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2 ∧
    ∃ ord : List ℕ, ord.Perm (List.range i.1.length) ∧
      ∀ p ∈ i.2.1, ord.idxOf p.1 < ord.idxOf p.2

/-- Start times and a machine assignment meeting precedence, deadline, and same-machine non-
overlap. -/
def PrecedenceMultiprocessorSchedulingFeasible
    (i : PrecedenceMultiprocessorSchedulingInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.1.length ∧
    ∃ machine : List ℕ, machine.length = i.1.length ∧
      (∀ j < i.1.length, machine.getD j 0 < i.2.2.1) ∧
      (∀ j < i.1.length, start.getD j 0 + i.1.getD j 0 ≤ i.2.2.2) ∧
      (∀ p ∈ i.2.1, start.getD p.1 0 + i.1.getD p.1 0 ≤ start.getD p.2 0) ∧
      ∀ a < i.1.length, ∀ b < i.1.length, a < b → machine.getD a 0 = machine.getD b 0 →
        start.getD a 0 + i.1.getD a 0 ≤ start.getD b 0 ∨
        start.getD b 0 + i.1.getD b 0 ≤ start.getD a 0

open Classical in
/-- PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING as a decision problem over bitstrings. -/
noncomputable def precedenceMultiprocessorSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceMultiprocessorSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceMultiprocessorSchedulingFeasible i)
  | none => false

/-- **PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete.** Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975). -/
public theorem_wanted precedenceMultiprocessorScheduling_npComplete :
    precedenceMultiprocessorSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceMultiprocessorSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling
