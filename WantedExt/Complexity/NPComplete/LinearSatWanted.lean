/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR SAT is NP-complete

Source:
S. Porschen, E. Speckenmeyer and X. Zhao, "Linear CNF formulas and satisfiability", Discrete
Applied Mathematics 157 (2009), 1046-1068, doi:10.1016/j.dam.2008.03.031 (SAT is NP-complete for
the unrestricted linear formula class);
S. Porschen, E. Speckenmeyer and B. Randerath, "On linear CNF formulas", in *Theory and
Applications of Satisfiability Testing (SAT 2006)*, Lecture Notes in Computer Science 4121
(2006), 212-225, doi:10.1007/11814948_22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearSat

/-!
# LINEAR SAT is NP-complete

INSTANCE: a CNF formula `C` that is linear: any two distinct clauses of `C` have at most one
variable in common (`|V(c₁) ∩ V(c₂)| ≤ 1` for `c₁ ≠ c₂`).
QUESTION: is `C` satisfiable?

The formula is a `Cslib.Logic.PL.CNF` (a list of clauses, each a list of literals `(v, b)`, the
literal `v` when `b = true` and `¬v` when `b = false`) over the variables `0, …, n - 1`. The
formula is a set of clauses and each clause a set of literals on distinct variables: the literals
of a clause are listed with strictly increasing variables (so no literal repeats and no
complementary pair occurs), and no clause is listed twice. A clause with a complementary pair is
always satisfied and can be dropped without affecting linearity or satisfiability, so this
convention does not change the problem. Linearity compares the variable lists of any two clauses
at distinct positions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables and the CNF formula (its clauses). -/
abbrev LinearSatInstance := ℕ × Cslib.Logic.PL.CNF

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
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- LINEAR SAT as a decision problem over bitstrings. -/
noncomputable def linearSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearSatInstance) x with
  | some i => decide (WellFormed i ∧ LinearSatFeasible i)
  | none => false

/-- **LINEAR SAT is NP-complete.** Source: Porschen, Speckenmeyer and Zhao (2009). -/
public theorem_wanted linearSat_npComplete :
    linearSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearSatDec

end MetaMathlibExt.Complexity.NPComplete.LinearSat
