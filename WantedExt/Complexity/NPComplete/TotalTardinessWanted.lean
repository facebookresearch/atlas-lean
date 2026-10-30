/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL TARDINESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TOTAL TARDINESS (1||sum
T_j); J. Du and J. Y.-T. Leung, "Minimizing total tardiness on one machine is NP-hard" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalTardiness

/-!
# TOTAL TARDINESS is NP-complete

Jobs with processing times and due dates, and a bound `K`. The question is whether some
ordering has total tardiness at most `K`, where a job's tardiness is the excess of its
completion time over its due date (zero if on time), computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A total-tardiness instance: jobs (processing time, due date), bound. -/
abbrev TotalTardinessInstance := List (ℕ × ℕ) × ℕ


/-- One job's effect on (elapsed time, accumulated tardiness). -/
def TardinessStep (jobs : List (ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0)).1
  (t, state.2 + (t - (jobs.getD j (0, 0)).2))

/-- Total tardiness of running the jobs in the given order (job indices). -/
def TotalTardinessValue (jobs : List (ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (TardinessStep jobs) (0, 0)).2


/-- An ordering of total tardiness at most `K`. -/
def TotalTardinessFeasible
    (i : TotalTardinessInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    TotalTardinessValue i.1 order ≤ i.2

open Classical in
/-- TOTAL TARDINESS as a decision problem over bitstrings. -/
noncomputable def totalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalTardinessInstance) x with
  | some i => decide (TotalTardinessFeasible i)
  | none => false

/-- **TOTAL TARDINESS is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), TOTAL TARDINESS (1||sum T_j); J. Du and J. Y.-T. Leung,
"Minimizing total tardiness on one machine is NP-hard" (1990). -/
public theorem_wanted totalTardiness_npComplete :
    totalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TotalTardiness
