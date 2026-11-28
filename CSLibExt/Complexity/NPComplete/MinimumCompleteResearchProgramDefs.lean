/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COMPLETE RESEARCH PROGRAM: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 189-203,
doi:10.1016/0196-6774(83)90045-7, problem [4] MINIMUM COMPLETE RESEARCH PROGRAM (the problem,
credited to Lageweg, Lawler, Lenstra and Rinnooy Kan, transformation from VERTEX COVER);
B. J. Lageweg, E. L. Lawler, J. K. Lenstra and A. H. G. Rinnooy Kan, "Computer-aided complexity
classification of combinatorial problems", Comm. ACM 25 (1982), 817-822,
doi:10.1145/358690.363066.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCompleteResearchProgram

/-- An instance: the number `n` of open problems (problems `0, ..., n - 1`), the list of pairs
`(x, y)` with `x < y`, and the bound `B`. -/
abbrev MinimumCompleteResearchProgramInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The order of the instance: `x < y` when the pair `(x, y)` is listed. -/
def Lt (i : MinimumCompleteResearchProgramInstance) (x y : Fin i.1) : Prop :=
  ((x : ℕ), (y : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the pairs name problems and the relation they list is a
strict partial order. -/
def WellFormed (i : MinimumCompleteResearchProgramInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1 ∧ p.2 < i.1) ∧ IsStrictOrder (Fin i.1) (Lt i)

/-- `y` is classified HARD by the rules from the classification `c` on `X'`: some `x ∈ X'` with
`c x = true` (HARD) has `x = y` or `x < y`. -/
def ForcedHard (i : MinimumCompleteResearchProgramInstance) (X' : Finset (Fin i.1))
    (c : Fin i.1 → Bool) (y : Fin i.1) : Prop :=
  ∃ x ∈ X', c x = true ∧ (x = y ∨ Lt i x y)

/-- `y` is classified EASY by the rules from the classification `c` on `X'`: some `x ∈ X'` with
`c x = false` (EASY) has `y = x` or `y < x`. -/
def ForcedEasy (i : MinimumCompleteResearchProgramInstance) (X' : Finset (Fin i.1))
    (c : Fin i.1 → Bool) (y : Fin i.1) : Prop :=
  ∃ x ∈ X', c x = false ∧ (y = x ∨ Lt i y x)

/-- Some `X'` with `|X'| ≤ B` and classification `c` on it extend, by the rules, to a total and
well-defined classification of all problems. -/
def MinimumCompleteResearchProgramFeasible (i : MinimumCompleteResearchProgramInstance) : Prop :=
  ∃ X' : Finset (Fin i.1), X'.card ≤ i.2.2 ∧ ∃ c : Fin i.1 → Bool,
    ∀ y : Fin i.1, (ForcedHard i X' c y ∨ ForcedEasy i X' c y) ∧
      ¬ (ForcedHard i X' c y ∧ ForcedEasy i X' c y)

open Classical in
/-- MINIMUM COMPLETE RESEARCH PROGRAM as a decision problem over bitstrings. -/
noncomputable def minimumCompleteResearchProgramDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCompleteResearchProgramInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCompleteResearchProgramFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCompleteResearchProgram
