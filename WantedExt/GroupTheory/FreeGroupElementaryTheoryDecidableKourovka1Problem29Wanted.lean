/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of the elementary theory of a free group (Kourovka Notebook Problem 1.29)

Kourovka Notebook, Archive of Solved Problems, Problem 1.29 (A. Tarski; M. I. Kargapolov): is the
elementary theory of a free group decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupElementaryTheoryDecidableKourovka1Problem29Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.29 (A.
Tarski; M. I. Kargapolov). UnsolvedMath record UM-00700024 (`KOU-1.29`), dataset ulamai/UnsolvedMath
v1.8.0.

Sentences of the language of groups are coded in prenex form, a quantifier prefix over `x₀, x₁, …`
followed by a conjunctive normal form over literals `w = 1` and `w ≠ 1`, so that codes form a
`Primcodable` type; variables not bound by the prefix are read as `1`. Every first-order sentence of
the language of groups is effectively equivalent to such a code and conversely, so decidability does
not depend on the coding. Free groups of rank `r ≥ 2` (the non-abelian ones the resolution treats);
the target is stated for every such rank.
-/

/-- A group word in the variables `x₀, x₁, …`, as a list of letters `(i, b)` read through
`FreeGroup.mk` (the letter `(i, true)` is `xᵢ`, the letter `(i, false)` is `xᵢ⁻¹`). -/
abbrev Word := List (ℕ × Bool)

/-- The value of a word in a group `G` under the assignment `x : ℕ → G`. -/
def evalWord {G : Type} [Group G] (x : ℕ → G) (w : Word) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

/-- A quantifier-free formula of the language of groups in conjunctive normal form: a conjunction
of clauses, each a disjunction of literals `(true, w)` (`w = 1`) or `(false, w)` (`w ≠ 1`). -/
abbrev CNF := List (List (Bool × Word))

/-- The CNF formula holds in `G` under the assignment `x`. -/
def CNF.HoldsAt {G : Type} [Group G] (φ : CNF) (x : ℕ → G) : Prop :=
  ∀ c ∈ φ, ∃ l ∈ c, (evalWord x l.2 = 1 ↔ l.1 = true)

/-- Truth in `G` of the prenex formula whose quantifier prefix is `qs` (`true` is `∀`, `false` is
`∃`) and whose matrix is `φ`, under the assignment `x`; the `j`-th quantifier of `qs` binds the
variable `x_(i+j)`. -/
def realizePrenex {G : Type} [Group G] (φ : CNF) : List Bool → ℕ → (ℕ → G) → Prop
  | [], _, x => φ.HoldsAt x
  | true :: qs, i, x => ∀ g : G, realizePrenex φ qs (i + 1) (Function.update x i g)
  | false :: qs, i, x => ∃ g : G, realizePrenex φ qs (i + 1) (Function.update x i g)

/-- A sentence of the language of groups in prenex form with a CNF matrix: the quantifier prefix
binds `x₀, x₁, …` in order, and variables not bound by the prefix are read as `1`. Every first-order
sentence of the language of groups is effectively equivalent to such a code, and conversely. -/
abbrev PrenexSentence := List Bool × CNF

/-- The prenex sentence `s` holds in the group `G`. -/
def PrenexSentence.HoldsIn (s : PrenexSentence) (G : Type) [Group G] : Prop :=
  realizePrenex (G := G) s.2 s.1 0 (fun _ => 1)

/-- Kourovka 1.29 (A. Tarski): for every rank `r ≥ 2`, the elementary theory of the free group
`F_r` is decidable. -/
def freeGroupElementaryTheoryDecidable : Prop :=
  ∀ r : ℕ, 2 ≤ r → ComputablePred fun s : PrenexSentence => s.HoldsIn (FreeGroup (Fin r))

/--
Resolved true: the Kourovka Archive answers 1.29 "Yes, it is", citing Kharlampovich and Myasnikov,
who prove that the elementary theory of a free non-abelian group is decidable. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.29 (A. Tarski; M. I. Kargapolov);
resolution: O. Kharlampovich and A. Myasnikov, Elementary theory of free non-abelian groups, J.
Algebra 302 (2006), no. 2, 451-552, Kourovka Archive, Problem 1.29 (Yes, it is).
-/
public theorem_wanted freeGroupElementaryTheoryDecidable_holds : freeGroupElementaryTheoryDecidable

end MathlibExt.GroupTheory.FreeGroupElementaryTheoryDecidableKourovka1Problem29Wanted
