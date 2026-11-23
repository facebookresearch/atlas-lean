/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Universal theories of finite and finite nilpotent groups (Kourovka Notebook Problem 1.25)

Kourovka Notebook, Archive of Solved Problems, Problem 1.25 (M. I. Kargapolov): a) is the universal
theory of the class of finite groups decidable? b) is the universal theory of the class of finite
nilpotent groups decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.UniversalTheoryFiniteGroupsKourovka1Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.25 (M. I.
Kargapolov). UnsolvedMath record UM-00700020 (`KOU-1.25`), dataset ulamai/UnsolvedMath v1.8.0.

Universal sentences are coded in conjunctive normal form over literals `w = 1` and `w ≠ 1`; every
quantifier-free formula of the language of groups is effectively equivalent to such a code and
conversely, so decidability does not depend on the coding. Finite groups are taken in `Type`, which
loses nothing.
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

/-- The universal theory of the class of finite groups: the universal sentences that hold in every
finite group. -/
def finiteGroupsUniversalTheory (φ : UniversalSentence) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], φ.HoldsIn G

/-- The universal theory of the class of finite nilpotent groups. -/
def finiteNilpotentGroupsUniversalTheory (φ : UniversalSentence) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsNilpotent G → φ.HoldsIn G

/-- Kourovka 1.25(a) (M. I. Kargapolov): the universal theory of the class of finite groups is
decidable. -/
def finiteGroupsUniversalTheoryDecidable : Prop :=
  ComputablePred finiteGroupsUniversalTheory

/-- Kourovka 1.25(b) (M. I. Kargapolov): the universal theory of the class of finite nilpotent
groups is decidable. -/
def finiteNilpotentGroupsUniversalTheoryDecidable : Prop :=
  ComputablePred finiteNilpotentGroupsUniversalTheory

/--
Resolved false: the Kourovka Archive answers 1.25(a) "No" (Slobodskoĭ 1981): the universal theory of
the class of finite groups is undecidable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 1.25 (M. I. Kargapolov); resolution: (a) A. M. Slobodskoĭ, Undecidability
of the universal theory of finite groups, Algebra and Logic 20 (1981), 139-156; (b) O. G.
Kharlampovich, The universal theory of the class of finite nilpotent groups is undecidable, Math.
Notes 33 (1983), 254-263, Kourovka Archive, Problem 1.25 (a) No; (b) No.
-/
public theorem_wanted finiteGroupsUniversalTheoryDecidable_refuted :
    ¬ finiteGroupsUniversalTheoryDecidable

/--
Resolved false: the Kourovka Archive answers 1.25(b) "No" (Kharlampovich 1983): the universal theory
of the class of finite nilpotent groups is undecidable. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 1.25 (M. I. Kargapolov); resolution: (a) A. M.
Slobodskoĭ, Undecidability of the universal theory of finite groups, Algebra and Logic 20 (1981),
139-156; (b) O. G. Kharlampovich, The universal theory of the class of finite nilpotent groups is
undecidable, Math. Notes 33 (1983), 254-263, Kourovka Archive, Problem 1.25 (a) No; (b) No.
-/
public theorem_wanted finiteNilpotentGroupsUniversalTheoryDecidable_refuted :
    ¬ finiteNilpotentGroupsUniversalTheoryDecidable

end MathlibExt.GroupTheory.UniversalTheoryFiniteGroupsKourovka1Problem25Wanted
