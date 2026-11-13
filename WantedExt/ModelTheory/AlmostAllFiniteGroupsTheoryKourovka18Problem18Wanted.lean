/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The theory of almost all finite groups (Kourovka Notebook Problem 18.18)

Kourovka Notebook, Problem 18.18 (O. V. Belegradek), marked solved in the 21st issue: Mal'cev proved
that the set of sentences that hold in all finite groups is not computably enumerable, although its
complement is. Is it true that both the set of sentences that hold in almost all finite groups and
its complement are not computably enumerable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.ModelTheory.AlmostAllFiniteGroupsTheoryKourovka18Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.18 (O. V. Belegradek). UnsolvedMath
record UM-00701447 (`KOU-18.18`), dataset ulamai/UnsolvedMath v1.8.0.

Sentences of the language of groups are coded in prenex conjunctive normal form: a quantifier prefix
binding `x₀, x₁, …` and a matrix of clauses of literals `w = 1`, `w ≠ 1` for group words `w`. Every
sentence is effectively equivalent in all groups to such a code and conversely, so computable
enumerability does not depend on the coding. "Almost all" means all but finitely many isomorphism
types; since there are finitely many groups of each order this is truth in every finite group of
sufficiently large order (the equivalence is stated in the resolving preprint, whose scope is this
reading; it asserts nothing for an asymptotic-density reading of "almost all"). The resolution is an
AI-generated solution confirmed by H. D. Macpherson and B. I. Zilber and accepted by the editors.
-/

/-- A group word in the variables `x₀, x₁, …`, as a list of letters `(i, b)` read through
`FreeGroup.mk` (`(i, true)` is `xᵢ`, `(i, false)` is `xᵢ⁻¹`). -/
abbrev Word := List (ℕ × Bool)

/-- The value of a word in `G` under the assignment `x : ℕ → G`. -/
def evalWord {G : Type} [Group G] (x : ℕ → G) (w : Word) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

/-- A first-order sentence of the language of groups in prenex conjunctive normal form: a
quantifier prefix (`true` for `∀`, `false` for `∃`) binding `x₀, x₁, …` in order, and a matrix
that is a conjunction of clauses, each a disjunction of literals `(true, w)` (`w = 1`) or
`(false, w)` (`w ≠ 1`). -/
abbrev SentenceCode := List Bool × List (List (Bool × Word))

/-- The matrix holds under the assignment `x`. -/
def MatrixHolds {G : Type} [Group G] (x : ℕ → G) (m : List (List (Bool × Word))) : Prop :=
  ∀ c ∈ m, ∃ l ∈ c, (evalWord x l.2 = 1 ↔ l.1 = true)

/-- Truth of the prefix `q`, whose first quantifier binds `x_d`, followed by the matrix `m`. -/
def HoldsFrom (G : Type) [Group G] (m : List (List (Bool × Word))) :
    ℕ → List Bool → (ℕ → G) → Prop
  | _, [], x => MatrixHolds x m
  | d, true :: q, x => ∀ g : G, HoldsFrom G m (d + 1) q (Function.update x d g)
  | d, false :: q, x => ∃ g : G, HoldsFrom G m (d + 1) q (Function.update x d g)

/-- The sentence `φ` holds in `G` (variables not bound by the prefix are read as `1`). -/
def SentenceCode.HoldsIn (φ : SentenceCode) (G : Type) [Group G] : Prop :=
  HoldsFrom G φ.2 0 φ.1 fun _ => 1

/-- `φ` holds in almost all finite groups: in every finite group of sufficiently large order
(equivalently, in all but finitely many finite groups up to isomorphism). -/
def HoldsInAlmostAllFiniteGroups (φ : SentenceCode) : Prop :=
  ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], N ≤ Nat.card G → φ.HoldsIn G

/-- Kourovka 18.18 (O. V. Belegradek): neither the set of first-order sentences of the language of
groups that hold in almost all finite groups nor its complement is computably enumerable. -/
def almostAllFiniteGroupsTheoryNotCE : Prop :=
  ¬ REPred HoldsInAlmostAllFiniteGroups ∧ ¬ REPred fun φ => ¬ HoldsInAlmostAllFiniteGroups φ

/--
Resolved true: the Kourovka Notebook (21st issue) answers 18.18 "Yes, it is true", by an
AI-generated solution confirmed by H. D. Macpherson and B. I. Zilber (Kinyon-Urban, 2026). Writing
`T_cof` for the sentences true in all but finitely many finite groups, the preprint reduces
Mal'cev's non-enumerable set `T_fin` to `T_cof` and to its complement by effective syntactic maps,
so neither is computably enumerable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
18.18 (O. V. Belegradek); resolution: M. Kinyon and J. Urban, Results on problems from the Kourovka
Notebook, preprint, version 4, 19 September 2026, Section 3.27 (Problem 18.18): both T_cof and its
complement fail to be computably enumerable, by reductions from Mal'cev's theorem; an AI solution
(GPT-6 Astra via Codex) confirmed by H. D. Macpherson and B. I. Zilber, which the Kourovka Notebook
(21st issue) accepts as solving 18.18,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted almostAllFiniteGroupsTheoryNotCE_holds : almostAllFiniteGroupsTheoryNotCE

end MathlibExt.ModelTheory.AlmostAllFiniteGroupsTheoryKourovka18Problem18Wanted
