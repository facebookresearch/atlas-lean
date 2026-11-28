/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTEERING: definitions

Source:
B. L. Golden, L. Levy and R. Vohra, "The orienteering problem", Naval Research Logistics 34
(1987), 307-318, doi:10.1002/1520-6750(198706)34:3<307::AID-NAV3220340302>3.0.CO;2-D (the problem
and the NP-hardness of its optimization version);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, pp. 199-200 (comment: the
variants in which the starting point or the ending point or both are specified are also
NP-complete), for the reduction to this decision version given in the module docstring.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Orienteering

/-- An instance: the number `n` of vertices, the travel-time matrix (row `u`, column `v`), the
start `s`, the end `t`, the scores, the time limit `T` and the target score `S`. -/
abbrev OrienteeringInstance := ℕ × List (List ℕ) × ℕ × ℕ × List ℕ × ℕ × ℕ

/-- The travel time between `u` and `v`. -/
def travelTime (i : OrienteeringInstance) (u v : ℕ) : ℕ :=
  (i.2.1.getD u []).getD v 0

/-- The score of vertex `v`. -/
def score (i : OrienteeringInstance) (v : ℕ) : ℕ :=
  i.2.2.2.2.1.getD v 0

/-- Well-formedness of an instance: the travel-time matrix is `n × n` and symmetric, `s` and
`t` are different vertices, there is one score per vertex, and `s` and `t` have score `0`. -/
def WellFormed (i : OrienteeringInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1, travelTime i u v = travelTime i v u) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧ i.2.2.2.2.1.length = i.1 ∧
    score i i.2.2.1 = 0 ∧ score i i.2.2.2.1 = 0

/-- There is a path from `s` to `t` in the complete graph whose total travel time is at most
`T` and whose visited vertices have total score at least `S`. -/
def OrienteeringFeasible (i : OrienteeringInstance) : Prop :=
  ∃ (u v : Fin i.1) (W : (⊤ : SimpleGraph (Fin i.1)).Walk u v),
    (u : ℕ) = i.2.2.1 ∧ (v : ℕ) = i.2.2.2.1 ∧ W.IsPath ∧
      (W.darts.map fun d => travelTime i d.fst d.snd).sum ≤ i.2.2.2.2.2.1 ∧
      i.2.2.2.2.2.2 ≤ (W.support.map fun w : Fin i.1 => score i w).sum

open Classical in
/-- ORIENTEERING as a decision problem over bitstrings. -/
noncomputable def orienteeringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrienteeringInstance) x with
  | some i => decide (WellFormed i ∧ OrienteeringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Orienteering
