/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The universal theory of soluble groups (Kourovka Notebook Problem 1.30)

Kourovka Notebook, Archive of Solved Problems, Problem 1.30 (M. I. Kargapolov): is the universal
theory of the class of soluble groups decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.UniversalTheorySolubleGroupsKourovka1Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.30 (M. I.
Kargapolov). UnsolvedMath record UM-00700025 (`KOU-1.30`), dataset ulamai/UnsolvedMath v1.8.0.

Universal sentences are coded in conjunctive normal form over literals `w = 1` and `w ≠ 1`;
decidability does not depend on the coding. Soluble means finite derived length
(`Group.IsSolvable`); groups are taken in `Type`, since a universal sentence failing in a soluble
group fails in a countable subgroup.
-/

/-- A group word in the variables `x₀, x₁, …`, as a list of letters `(i, b)` read through
`FreeGroup.mk` (the letter `(i, true)` is `xᵢ`, the letter `(i, false)` is `xᵢ⁻¹`). -/
abbrev Word := List (ℕ × Bool)

/-- The value of a word in a group `G` under the assignment `x : ℕ → G`. -/
def evalWord {G : Type} [Group G] (x : ℕ → G) (w : Word) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

/-- A universal sentence of the language of groups in conjunctive normal form: the universal
closure of a conjunction of clauses, each a disjunction of literals `(true, w)` (`w = 1`) or
`(false, w)` (`w ≠ 1`). Every universal sentence is equivalent to such a code, effectively. -/
abbrev UniversalSentence := List (List (Bool × Word))

/-- A universal sentence holds in the group `G`. -/
def UniversalSentence.HoldsIn (φ : UniversalSentence) (G : Type) [Group G] : Prop :=
  ∀ x : ℕ → G, ∀ c ∈ φ, ∃ l ∈ c, (evalWord x l.2 = 1 ↔ l.1 = true)

/-- The universal theory of the class of soluble groups: the universal sentences that hold in every
soluble group. -/
def solubleGroupsUniversalTheory (φ : UniversalSentence) : Prop :=
  ∀ (G : Type) [Group G], Group.IsSolvable G → φ.HoldsIn G

/-- Kourovka 1.30 (M. I. Kargapolov): the universal theory of the class of soluble groups is
decidable. -/
def solubleGroupsUniversalTheoryDecidable : Prop :=
  ComputablePred solubleGroupsUniversalTheory

/--
Resolved false: the Kourovka Archive answers 1.30 "No", citing Kharlampovich's finitely presented
soluble group `⟨x | r₁, …, rₘ⟩` with unsolvable word problem: the universal sentences `∀ x (r₁ = 1 ∧
⋯ ∧ rₘ = 1 → w = 1)` that hold in all soluble groups are exactly those with `w = 1` in that group.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.30 (M. I.
Kargapolov); resolution: O. G. Kharlampovich, A finitely presented solvable group with unsolvable
word problem, Math. USSR-Izv. 19 (1982), 151-169, Kourovka Archive, Problem 1.30 (No).
-/
public theorem_wanted solubleGroupsUniversalTheoryDecidable_refuted :
    ¬ solubleGroupsUniversalTheoryDecidable

end MathlibExt.GroupTheory.UniversalTheorySolubleGroupsKourovka1Problem30Wanted
