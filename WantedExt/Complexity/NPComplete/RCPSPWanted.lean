/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; J.
Blazewicz, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24
(classification).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RCPSP

/-!
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Jobs with durations and resource demands, precedence constraints, a single renewable resource
capacity, and a deadline `D`. The question is whether there are start times meeting all
precedence constraints and the deadline, with the total resource demand of simultaneously
active jobs never exceeding the capacity (checked by forbidding an active subset of demand
exceeding capacity at each time). NP-hardness follows from bin packing: items become unit-
duration jobs with demand equal to item size, no precedence, resource capacity equal to bin
capacity, and makespan bound equal to the number of bins.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An RCPSP instance: jobs (duration, demand), precedence pairs, resource capacity, deadline. -/
abbrev RCPSPInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : RCPSPInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2 ∧
    ∃ ord : List ℕ, ord.Perm (List.range i.1.length) ∧
      ∀ p ∈ i.2.1, ord.idxOf p.1 < ord.idxOf p.2

/-- Start times meeting precedence, deadline, and resource capacity. -/
def RCPSPFeasible
    (i : RCPSPInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.1.length ∧
    (∀ j < i.1.length, start.getD j 0 + (i.1.getD j (0, 0)).1 ≤ i.2.2.2) ∧
    (∀ p ∈ i.2.1, start.getD p.1 0 + (i.1.getD p.1 0).1 ≤ start.getD p.2 0) ∧
    ∀ t < i.2.2.2, ¬ ∃ active : List ℕ, active.Nodup ∧
      (∀ j ∈ active, j < i.1.length ∧ start.getD j 0 ≤ t ∧
        t < start.getD j 0 + (i.1.getD j (0, 0)).1) ∧
      i.2.2.1 < (active.map (fun j => (i.1.getD j (0, 0)).2)).sum

open Classical in
/-- RESOURCE-CONSTRAINED PROJECT SCHEDULING as a decision problem over bitstrings. -/
noncomputable def rcpspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RCPSPInstance) x with
  | some i => decide (WellFormed i ∧ RCPSPFeasible i)
  | none => false

/-- **RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), BIN PACKING; J. Blazewicz, J. K. Lenstra,
and A. H. G. Rinnooy Kan, "Scheduling subject to resource constraints: classification and
complexity", Discrete Applied Mathematics 5 (1983), 11-24 (classification). -/
public theorem_wanted rcpsp_npComplete :
    rcpspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rcpspDec

end MetaMathlibExt.Complexity.NPComplete.RCPSP
