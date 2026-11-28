/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISTINGUISHED ONES: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM DISTINGUISHED ONES (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (satisfiability with at most three literals per clause is
NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes

/-- An instance: the number `n` of variables, the list of distinguished variables `Z`, the
clauses, and the bound `K`. -/
abbrev MinimumDistinguishedOnesInstance := ℕ × List ℕ × Cslib.Logic.LegacyPL.CNF × ℕ

/-- Well-formedness of an instance: `Z` lists distinct variables below `n`, and every clause
has at most 3 literals, all over variables below `n`. -/
def WellFormed (i : MinimumDistinguishedOnesInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ z ∈ i.2.1, z < i.1) ∧
    ∀ clause ∈ i.2.2.1, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1

/-- Some assignment of the `n` variables satisfies every clause and sets at most `K` variables
of `Z` to true. -/
def MinimumDistinguishedOnesFeasible (i : MinimumDistinguishedOnesInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2.2.1 ∧
    (i.2.1.filter fun z => assign.getD z false).length ≤ i.2.2.2

open Classical in
/-- MINIMUM DISTINGUISHED ONES as a decision problem over bitstrings. -/
noncomputable def minimumDistinguishedOnesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumDistinguishedOnesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumDistinguishedOnesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes
