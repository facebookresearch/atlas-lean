/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR SAT: definitions

Source:
S. Porschen, E. Speckenmeyer and X. Zhao, "Linear CNF formulas and satisfiability", Discrete
Applied Mathematics 157 (2009), 1046-1068, doi:10.1016/j.dam.2008.03.031 (SAT is NP-complete for
the unrestricted linear formula class);
S. Porschen, E. Speckenmeyer and B. Randerath, "On linear CNF formulas", in *Theory and
Applications of Satisfiability Testing (SAT 2006)*, Lecture Notes in Computer Science 4121
(2006), 212-225, doi:10.1007/11814948_22.
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearSat

/-- An instance: the number `n` of variables and the CNF formula (its clauses). -/
abbrev LinearSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- The variables of a clause. -/
def vars (c : List (ℕ × Bool)) : List ℕ := c.map Prod.fst

/-- Well-formedness of an instance: every clause lists literals on variables `< n` with strictly
increasing variables, no clause is listed twice, and any two clauses share at most one
variable. -/
def WellFormed (i : LinearSatInstance) : Prop :=
  (∀ c ∈ i.2, (vars c).Pairwise (· < ·) ∧ ∀ v ∈ vars c, v < i.1) ∧ i.2.Nodup ∧
    i.2.Pairwise fun c d => ((vars c).filter fun v => v ∈ vars d).length ≤ 1

/-- A satisfying truth assignment. -/
def LinearSatFeasible (i : LinearSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- LINEAR SAT as a decision problem over bitstrings. -/
noncomputable def linearSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearSatInstance) x with
  | some i => decide (WellFormed i ∧ LinearSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LinearSat
