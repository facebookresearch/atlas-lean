/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research 26
(1978), 22-35.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion

/-!
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Jobs with processing times and weights, precedence constraints, and a bound `K`. The question
is whether some ordering respecting the precedence constraints has weighted sum of completion
times at most `K`, computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A 1|prec|sum wC instance: jobs (processing time, weight), precedence pairs, bound. -/
abbrev PrecedenceWeightedCompletionInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ


/-- One job's effect on (elapsed time, weighted completion sum). -/
def WeightedCompletionStep (jobs : List (ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0)).1
  (t, state.2 + (jobs.getD j (0, 0)).2 * t)

/-- Weighted sum of completion times for a job order (job indices). -/
def WeightedCompletion (jobs : List (ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (WeightedCompletionStep jobs) (0, 0)).2


/-- Well-formedness of an instance. -/
def WellFormed (i : PrecedenceWeightedCompletionInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2

/-- A precedence-respecting ordering of weighted completion sum at most `K`. -/
def PrecedenceWeightedCompletionFeasible
    (i : PrecedenceWeightedCompletionInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    (∀ p ∈ i.2.1, order.idxOf p.1 < order.idxOf p.2) ∧
    WeightedCompletion i.1 order ≤ i.2.2

open Classical in
/-- SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE as a decision problem over bitstrings. -/
noncomputable def precedenceWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceWeightedCompletionFeasible i)
  | none => false

/-- **SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete.** Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research
26 (1978), 22-35. -/
public theorem_wanted precedenceWeightedCompletion_npComplete :
    precedenceWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion
