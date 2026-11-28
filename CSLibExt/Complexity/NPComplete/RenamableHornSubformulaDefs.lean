/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RENAMABLE HORN SUBFORMULA: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM RENAMABLE HORN SUBFORMULA (decision version);
E. Boros, "Maximum renamable Horn sub-CNFs", Discrete Appl. Math. 96-97 (1999), 29-40,
doi:10.1016/S0166-218X(99)00031-1, Sections 1-2 (definitions; NP-hard because on CNFs whose
clauses all have two literals the problem is equivalent to MAX-2-SAT).
-/
module

public import CSLibExt.Algorithms.SAT.Horn.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RenamableHornSubformula

open Cslib.Logic.LegacyPL Cslib.Algorithms.SAT.Horn

/-- An instance: the number `n` of variables (`U = {0, …, n - 1}`), the clauses `C`, and the
bound `K`. -/
abbrev RenamableHornSubformulaInstance := ℕ × CNF × ℕ

/-- Well-formedness of an instance: every clause is a duplicate-free list of at most `3`
literals over the variables `0, …, n - 1`, no two clauses have the same set of literals, and
`K` is positive. -/
def WellFormed (i : RenamableHornSubformulaInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Nodup ∧ c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < i.1) ∧
    (i.2.1.map List.toFinset).Nodup ∧ 0 < i.2.2

/-- The formula obtained from `φ` by switching the literals of the variables in `S`: the
polarity of every literal whose variable `x` has `S x = true` is flipped. -/
def switch (S : ℕ → Bool) (φ : CNF) : CNF :=
  φ.map fun c => c.map fun l => (l.1, xor l.2 (S l.1))

/-- There is a renamable Horn subformula `C' ⊆ C` with `|C'| ≥ K`: a sublist `C'` of `C` of
length at least `K` and a switching set `S` that makes `C'` a Horn formula. -/
def RenamableHornSubformulaFeasible (i : RenamableHornSubformulaInstance) : Prop :=
  ∃ C' : CNF, C'.Sublist i.2.1 ∧ i.2.2 ≤ C'.length ∧ ∃ S : ℕ → Bool, IsHorn (switch S C')

open Classical in
/-- RENAMABLE HORN SUBFORMULA as a decision problem over bitstrings. -/
noncomputable def renamableHornSubformulaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RenamableHornSubformulaInstance) x with
  | some i => decide (WellFormed i ∧ RenamableHornSubformulaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RenamableHornSubformula
