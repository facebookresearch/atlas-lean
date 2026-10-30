/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elementary theory of torsion-free hyperbolic groups (Kourovka Notebook Problem 16.71)

Kourovka Notebook, Archive of Solved Problems, Problem 16.71 (A. G. Myasnikov, O. G. Kharlampovich):
is the elementary theory of a torsion-free hyperbolic group decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.GroupTheory.HyperbolicGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeHyperbolicElementaryTheoryKourovka16Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.71 (A. G.
Myasnikov, O. G. Kharlampovich). UnsolvedMath record UM-00701263 (`KOU-16.71`), dataset
ulamai/UnsolvedMath v1.8.0.

Sentences of the language of groups are coded in prenex form, a quantifier prefix over `x₀, x₁, …`
followed by a conjunctive normal form over literals `w = 1` and `w ≠ 1`, so that codes form a
`Primcodable` type; every first-order sentence is effectively equivalent to such a code and
conversely. Hyperbolic is `Group.IsHyperbolic` (`MathlibExt.GroupTheory.HyperbolicGroup`: some
finite generating set has a Gromov-hyperbolic word metric) and torsion-free means no nontrivial
element of finite order. Decidability is per group.
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

/-- Kourovka 16.71 (A. G. Myasnikov, O. G. Kharlampovich): the elementary theory of every
torsion-free hyperbolic group is decidable. -/
def torsionFreeHyperbolicTheoryDecidable : Prop :=
  ∀ (G : Type) [Group G], Group.IsHyperbolic G → (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    ComputablePred fun s : PrenexSentence => s.HoldsIn G

/--
Resolved true: Kharlampovich and Myasnikov (Theorem 3) prove that the elementary theory of a
torsion-free hyperbolic group is decidable; the Kourovka Archive answers 16.71 "Yes, it is". Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.71 (A. G. Myasnikov,
O. G. Kharlampovich); resolution: O. Kharlampovich and A. Myasnikov, Decidability of the elementary
theory of a torsion-free hyperbolic group, arXiv:1303.0760, Theorem 3 (the elementary theory of a
torsion-free hyperbolic group is decidable); Kourovka Archive, Problem 16.71 (Yes, it is),
https://arxiv.org/abs/1303.0760.
-/
public theorem_wanted torsionFreeHyperbolicTheoryDecidable_holds :
    torsionFreeHyperbolicTheoryDecidable

end MathlibExt.GroupTheory.TorsionFreeHyperbolicElementaryTheoryKourovka16Problem71Wanted
