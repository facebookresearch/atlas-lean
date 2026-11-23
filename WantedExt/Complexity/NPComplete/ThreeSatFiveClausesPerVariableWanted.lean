/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-SATISFIABILITY with at most five clauses per variable is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable

/-!
# 3-SATISFIABILITY with at most five clauses per variable is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U` such that each clause
`c ∈ C` has `|c| = 3`, and for each `u ∈ U` there are at most `5` clauses in `C` that contain
either `u` or `ū`.
QUESTION: is there a satisfying truth assignment for `C`?

Formulas are CSLib's `Cslib.Logic.PL.CNF` (a clause is a list of literals `(variable, sign)`, a
formula a list of clauses) with satisfaction `Cslib.Logic.PL.CNF.Satisfies`, in the encoding of
`WantedExt.Complexity.NPComplete.BoundedOccurrenceThreeSatWanted`: the variables are
`0, …, n - 1` and a truth assignment is a list of `n` truth values. A clause is a set of
literals, so `|c| = 3` says that the clause lists three distinct literals. A clause contains `u`
or `ū` when one of its literals is on `u`; clauses are counted along the list `C`.

This is the variant recorded in the comment to [LO2]. It differs from
`BoundedOccurrenceThreeSatWanted`, which bounds the number of literal occurrences of a variable by
four, and from `ThreeOccurrenceSatWanted`, whose clauses have at most three literals and whose
variables lie in at most three clauses.

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
abbrev ThreeSatFiveClausesPerVariableInstance := ℕ × Cslib.Logic.PL.CNF

/-- Well-formedness of an instance: every clause consists of three distinct literals on
variables `< n`, and every variable `u < n` lies in at most five clauses. -/
def WellFormed (i : ThreeSatFiveClausesPerVariableInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ clause.Nodup ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    ∀ u < i.1, i.2.countP (fun clause => clause.any (fun l => l.1 == u)) ≤ 5

/-- A satisfying truth assignment for the variables `0, …, n - 1`. -/
def ThreeSatFiveClausesPerVariableFeasible (i : ThreeSatFiveClausesPerVariableInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- 3-SATISFIABILITY with at most five clauses per variable as a decision problem over
bitstrings. -/
noncomputable def threeSatFiveClausesPerVariableDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeSatFiveClausesPerVariableInstance) x with
  | some i => decide (WellFormed i ∧ ThreeSatFiveClausesPerVariableFeasible i)
  | none => false

/-- **3-SATISFIABILITY with at most five clauses per variable is NP-complete.** Source: Garey and
Johnson (1979), [LO2]; Tovey (1984); Kratochvíl, Savický and Tuza (1993). -/
public theorem_wanted threeSatFiveClausesPerVariable_npComplete :
    threeSatFiveClausesPerVariableDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeSatFiveClausesPerVariableDec

end MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable
