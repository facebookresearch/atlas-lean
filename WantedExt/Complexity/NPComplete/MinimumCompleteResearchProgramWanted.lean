/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COMPLETE RESEARCH PROGRAM is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 189-203,
doi:10.1016/0196-6774(83)90045-7, problem [4] MINIMUM COMPLETE RESEARCH PROGRAM (the problem,
credited to Lageweg, Lawler, Lenstra and Rinnooy Kan, transformation from VERTEX COVER);
B. J. Lageweg, E. L. Lawler, J. K. Lenstra and A. H. G. Rinnooy Kan, "Computer-aided complexity
classification of combinatorial problems", Comm. ACM 25 (1982), 817-822,
doi:10.1145/358690.363066.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCompleteResearchProgram

/-!
# MINIMUM COMPLETE RESEARCH PROGRAM is NP-complete

INSTANCE: a set `X` of open problems, a partial order `<` on `X`, and a bound `B`.
QUESTION: is there a subset `X' ⊆ X` with `|X'| ≤ B` and a complexity classification function
`c : X' → {EASY, HARD}` that would resolve all the open problems, i.e., such that `c` can be
extended to a well-defined total function on `X` by applying the rules
(a) `x < y` and `c(x) = HARD` implies `c(y) = HARD`, and
(b) `x < y` and `c(y) = EASY` implies `c(x) = EASY`?

The problems are `Fin n`. The order is given as the list of its pairs `(x, y)`, meaning `x < y`;
`WellFormed` requires the relation it lists to be a strict partial order, Mathlib's
`IsStrictOrder` (irreflexive and transitive), as in `PartiallyOrderedKnapsackWanted`. The
classification is a function `c : Fin n → Bool` read on `X'` only, `true` for HARD and `false`
for EASY.

Applying the rules: rule (a) only produces HARD values and rule (b) only EASY values, and the
order is transitive, so the problems that the rules classify HARD are exactly those `y` with
`x = y` or `x < y` for some `x ∈ X'` with `c(x) = HARD`, and those classified EASY are exactly
those `y` with `y = x` or `y < x` for some `x ∈ X'` with `c(x) = EASY`. The extension is total
when every problem is classified, and well-defined when no problem is classified both HARD and
EASY (this also covers a rule overriding `c` on `X'` itself).

The number `n` is encoded in binary, so the instance does not list the problems one by one.
NP membership is unaffected: a problem that occurs in no listed pair is classified only when it
lies in `X'` (no rule reaches it from another problem, and it never causes a conflict), so it
costs exactly one unit of `B`. An instance is therefore a yes-instance iff the at most
`2 |pairs|` problems occurring in pairs can be resolved by a program of size at most `B` minus the
number of problems occurring in no pair; that program and its classification are a certificate
polynomial in the encoding, and the count of the other problems is arithmetic on `n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMUM COMPLETE RESEARCH PROGRAM is NP-complete.** Source: Johnson (1983), problem [4];
Lageweg, Lawler, Lenstra and Rinnooy Kan (1982). -/
public theorem_wanted minimumCompleteResearchProgram_npComplete :
    minimumCompleteResearchProgramDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCompleteResearchProgramDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCompleteResearchProgram
