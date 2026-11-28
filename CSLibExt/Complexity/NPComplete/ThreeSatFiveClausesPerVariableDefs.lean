/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-SATISFIABILITY with at most five clauses per variable: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO2] 3-SATISFIABILITY (3SAT), comment (no
attribution given);
C. A. Tovey, "A simplified NP-complete satisfiability problem", Discrete Applied Mathematics 8
(1984), 85-89, doi:10.1016/0166-218X(84)90081-7 (3SAT stays NP-complete when every variable
occurs in at most four clauses);
P. Berman, M. Karpinski and A. D. Scott, "Computational complexity of some restricted instances
of 3-SAT", Discrete Applied Mathematics 155 (2007), 649-653, doi:10.1016/j.dam.2006.07.009
(records Tovey's result);
J. Kratochvíl, P. Savický and Z. Tuza, "One more occurrence of variables makes satisfiability
jump from trivial to NP-complete", SIAM J. Comput. 22 (1993), 203-210, doi:10.1137/0222015.
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable

/-- An instance: the number `n` of variables and the CNF formula (its clauses). -/
abbrev ThreeSatFiveClausesPerVariableInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- Well-formedness of an instance: every clause consists of three distinct literals on
variables `< n`, and every variable `u < n` lies in at most five clauses. -/
def WellFormed (i : ThreeSatFiveClausesPerVariableInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ clause.Nodup ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    ∀ u < i.1, i.2.countP (fun clause => clause.any (fun l => l.1 == u)) ≤ 5

/-- A satisfying truth assignment for the variables `0, …, n - 1`. -/
def ThreeSatFiveClausesPerVariableFeasible (i : ThreeSatFiveClausesPerVariableInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- 3-SATISFIABILITY with at most five clauses per variable as a decision problem over
bitstrings. -/
noncomputable def threeSatFiveClausesPerVariableDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeSatFiveClausesPerVariableInstance) x with
  | some i => decide (WellFormed i ∧ ThreeSatFiveClausesPerVariableFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable
