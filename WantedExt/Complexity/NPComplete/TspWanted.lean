/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESPERSON (SYMMETRIC) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON
PROBLEM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tsp

/-!
# TRAVELING SALESPERSON (SYMMETRIC) is NP-complete

A symmetric integer-weighted complete graph, given by a symmetric weight matrix with zero
diagonal, and a bound `B`. The question is whether there is a tour visiting every vertex
exactly once whose total weight, including the return to the start, is at most `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A symmetric TSP instance: number of cities, symmetric weight matrix, bound. -/
abbrev TspInstance := ℕ × List (List ℕ) × ℕ


/-- Tour length: sum of weights along the cycle, including the return edge. -/
def TourLength (w : List (List ℕ)) (tour : List ℕ) : ℕ :=
  ((List.range tour.length).map (fun j =>
    (w.getD (tour.getD j 0) []).getD (tour.getD ((j + 1) % tour.length) 0) 0)).sum


/-- Well-formedness of an instance. -/
def WellFormed (i : TspInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ a < i.1, ∀ b < i.1, (i.2.1.getD a []).getD b 0 = (i.2.1.getD b []).getD a 0) ∧
    ∀ a < i.1, (i.2.1.getD a []).getD a 0 = 0

/-- A tour of total weight at most `B`. -/
def TspFeasible
    (i : TspInstance) : Prop :=
  ∃ tour : List ℕ, tour.Nodup ∧ tour.length = i.1 ∧ (∀ v < i.1, v ∈ tour) ∧
    TourLength i.2.1 tour ≤ i.2.2

open Classical in
/-- TRAVELING SALESPERSON (SYMMETRIC) as a decision problem over bitstrings. -/
noncomputable def tspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspInstance) x with
  | some i => decide (WellFormed i ∧ TspFeasible i)
  | none => false

/-- **TRAVELING SALESPERSON (SYMMETRIC) is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON PROBLEM. -/
public theorem_wanted tsp_npComplete :
    tspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tspDec

end MetaMathlibExt.Complexity.NPComplete.Tsp
