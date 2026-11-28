/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUIVALENCE DELETION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM EQUIVALENCE DELETION;
N. Garg, V. V. Vazirani and M. Yannakakis, "Approximate max-flow min-(multi)cut theorems and
their applications", SIAM J. Comput. 25 (1996), 235-251, doi:10.1137/S0097539793243016 (the
problem as 2CNF≡ clause deletion);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoret. Comput. Sci. 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1 (SIMPLE MAX CUT,
Garey and Johnson (1979), [ND16]).
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquivalenceDeletion

/-- An instance: the number `n` of variables, the equivalences (pairs of literals) and the
bound `K`. -/
abbrev EquivalenceDeletionInstance := ℕ × List ((ℕ × Bool) × (ℕ × Bool)) × ℕ

/-- Well-formedness of an instance: every literal is over a variable below `n`, and `0 < K`. -/
def WellFormed (i : EquivalenceDeletionInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.1 < i.1 ∧ e.2.1 < i.1) ∧ 0 < i.2.2

/-- The equivalence `l₁ ≡ l₂` is satisfied: both literals have the same truth value. -/
def EquivSatisfied (assignment : ℕ → Bool) (e : (ℕ × Bool) × (ℕ × Bool)) : Prop :=
  (Cslib.Logic.LegacyPL.CNFLiteral.Satisfies assignment e.1 ↔
    Cslib.Logic.LegacyPL.CNFLiteral.Satisfies assignment e.2)

/-- Some truth assignment leaves at most `K` equivalences unsatisfied. -/
def EquivalenceDeletionFeasible (i : EquivalenceDeletionInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ kept : List ((ℕ × Bool) × (ℕ × Bool)), kept.Sublist i.2.1 ∧
      i.2.1.length ≤ kept.length + i.2.2 ∧
        ∀ e ∈ kept, EquivSatisfied (fun x => assign.getD x false) e

open Classical in
/-- EQUIVALENCE DELETION as a decision problem over bitstrings. -/
noncomputable def equivalenceDeletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EquivalenceDeletionInstance) x with
  | some i => decide (WellFormed i ∧ EquivalenceDeletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EquivalenceDeletion
