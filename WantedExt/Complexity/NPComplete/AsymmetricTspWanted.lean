/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON
PROBLEM (asymmetric).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp

/-!
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

An integer-weighted complete directed graph, given by a weight matrix with zero diagonal (not
assumed symmetric), and a bound `B`. The question is whether there is a directed tour visiting
every vertex exactly once whose total weight, including the return to the start, is at most
`B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An asymmetric TSP instance: number of cities, weight matrix, bound. -/
abbrev AsymmetricTspInstance := ℕ × List (List ℕ) × ℕ


/-- Tour length: sum of weights along the cycle, including the return edge. -/
def TourLength (w : List (List ℕ)) (tour : List ℕ) : ℕ :=
  ((List.range tour.length).map (fun j =>
    (w.getD (tour.getD j 0) []).getD (tour.getD ((j + 1) % tour.length) 0) 0)).sum


/-- Well-formedness of an instance. -/
def WellFormed (i : AsymmetricTspInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    ∀ a < i.1, (i.2.1.getD a []).getD a 0 = 0

/-- A directed tour of total weight at most `B`. -/
def AsymmetricTspFeasible
    (i : AsymmetricTspInstance) : Prop :=
  ∃ tour : List ℕ, tour.Nodup ∧ tour.length = i.1 ∧ (∀ v < i.1, v ∈ tour) ∧
    TourLength i.2.1 tour ≤ i.2.2

open Classical in
/-- TRAVELING SALESPERSON (ASYMMETRIC) as a decision problem over bitstrings. -/
noncomputable def asymmetricTspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AsymmetricTspInstance) x with
  | some i => decide (WellFormed i ∧ AsymmetricTspFeasible i)
  | none => false

/-- **TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON PROBLEM
(asymmetric). -/
public theorem_wanted asymmetricTsp_npComplete :
    asymmetricTspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L asymmetricTspDec

end MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp
