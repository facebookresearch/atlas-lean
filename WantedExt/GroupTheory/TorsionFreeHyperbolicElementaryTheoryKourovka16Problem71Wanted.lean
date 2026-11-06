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

/-- **Group words in countably many variables.** A group word in the variables $x_0, x_1, \dots$ is
coded as a finite list of letters $(i, b)$, where $i$ is a natural number and $b$ is a Boolean: the
letter $(i, \mathrm{true})$ stands for $x_i$ and the letter $(i, \mathrm{false})$ for $x_i^{-1}$.
The word is read as the product of its letters in order, an element of the free group on
$x_0, x_1, \dots$. -/
abbrev Word := List (ℕ × Bool)

/-- **Value of a group word.** Let $G$ be a group and $a \colon \mathbb{N} \to G$ an assignment of
values to the variables $x_0, x_1, \dots$. The value of a group word $w$ under $a$ is the product in
$G$, in the order of the letters of $w$, of $a(i)$ for each letter $x_i$ and of $a(i)^{-1}$ for
each letter $x_i^{-1}$; equivalently, it is the image of $w$ under the homomorphism from the free
group on $x_0, x_1, \dots$ to $G$ that sends $x_i$ to $a(i)$. -/
def evalWord {G : Type} [Group G] (x : ℕ → G) (w : Word) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

/-- **Quantifier-free formulas in conjunctive normal form.** A quantifier-free formula of the
language of groups in conjunctive normal form is coded as a finite list of clauses, each clause a
finite list of literals. A literal is a pair $(b, w)$ of a Boolean $b$ and a group word $w$; it
stands for the equation $w = 1$ when $b$ is true and for the inequation $w \ne 1$ when $b$ is
false. The formula is the conjunction of its clauses, and each clause is the disjunction of its
literals. -/
abbrev CNF := List (List (Bool × Word))

/-- **Truth of a formula in conjunctive normal form.** Let $G$ be a group, let
$a \colon \mathbb{N} \to G$ assign values to the variables $x_0, x_1, \dots$, and let $\varphi$ be
a quantifier-free formula in conjunctive normal form. Then $\varphi$ holds in $G$ under $a$ when
every clause of $\varphi$ contains a literal $(b, w)$ such that the value of $w$ under $a$ equals
$1$ if and only if $b$ is true, that is, a literal $w = 1$ whose word has value $1$ or a literal
$w \ne 1$ whose word does not. -/
def CNF.HoldsAt {G : Type} [Group G] (φ : CNF) (x : ℕ → G) : Prop :=
  ∀ c ∈ φ, ∃ l ∈ c, (evalWord x l.2 = 1 ↔ l.1 = true)

/-- **Truth of a prenex formula.** Let $G$ be a group, $\varphi$ a quantifier-free formula in
conjunctive normal form, $q$ a finite list of Booleans read as a quantifier prefix ($\mathrm{true}$
for $\forall$, $\mathrm{false}$ for $\exists$), $i$ a natural number and $a \colon \mathbb{N} \to G$
an assignment of values to the variables $x_0, x_1, \dots$. Truth in $G$ under $a$ of the formula
with prefix $q$, whose first quantifier binds $x_i$, and matrix $\varphi$ is defined by recursion
on $q$. For the empty prefix it is truth of $\varphi$ in $G$ under $a$. For a prefix $\forall$
followed by $q'$, it holds when for every $g \in G$ the formula with prefix $q'$, whose first
quantifier binds $x_{i+1}$, holds under the assignment that agrees with $a$ except that $x_i$ takes
the value $g$; for a prefix $\exists$ followed by $q'$, the same holds for some $g \in G$. Thus the
quantifiers of $q$ bind $x_i, x_{i+1}, \dots$ in order, and the other variables keep their values
under $a$. -/
def realizePrenex {G : Type} [Group G] (φ : CNF) : List Bool → ℕ → (ℕ → G) → Prop
  | [], _, x => φ.HoldsAt x
  | true :: qs, i, x => ∀ g : G, realizePrenex φ qs (i + 1) (Function.update x i g)
  | false :: qs, i, x => ∃ g : G, realizePrenex φ qs (i + 1) (Function.update x i g)

/-- **Prenex sentences of the language of groups.** A sentence of the language of groups in prenex
form with matrix in conjunctive normal form is coded as a pair $(q, \varphi)$ of a finite list $q$
of Booleans, the quantifier prefix ($\mathrm{true}$ for $\forall$, $\mathrm{false}$ for $\exists$),
and a quantifier-free formula $\varphi$ in conjunctive normal form. The quantifiers of $q$ bind the
variables $x_0, x_1, \dots$ in order, and variables of $\varphi$ not bound by the prefix are read
as $1$.

Every first-order sentence of the language of groups is effectively equivalent to such a code, and
conversely. -/
abbrev PrenexSentence := List Bool × CNF

/-- **Truth of a prenex sentence in a group.** A prenex sentence $(q, \varphi)$ holds in a group $G$
when the formula with quantifier prefix $q$ and matrix $\varphi$, whose quantifiers bind the
variables $x_0, x_1, \dots$ in order, is true in $G$ under the assignment that gives every variable
the value $1$; thus the variables not bound by $q$ are read as $1$. -/
def PrenexSentence.HoldsIn (s : PrenexSentence) (G : Type) [Group G] : Prop :=
  realizePrenex (G := G) s.2 s.1 0 (fun _ => 1)

/-- **Decidability of the elementary theory of torsion-free hyperbolic groups.** The proposition
stating Kourovka Problem 16.71 (A. G. Myasnikov, O. G. Kharlampovich): for every torsion-free
word-hyperbolic group $G$ (every element $g \ne 1$ of $G$ has infinite order), the set of prenex
sentences of the language of groups that hold in $G$ is computable, that is, some algorithm
decides for each prenex sentence whether it holds in $G$. -/
def torsionFreeHyperbolicTheoryDecidable : Prop :=
  ∀ (G : Type) [Group G], Group.IsHyperbolic G → (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    ComputablePred fun s : PrenexSentence => s.HoldsIn G

/--
**Torsion-free hyperbolic groups have decidable elementary theory.** For every torsion-free
word-hyperbolic group $G$ (every element $g \ne 1$ of $G$ has infinite order), the set of prenex
sentences of the language of groups that hold in $G$ is computable, that is, some algorithm decides
for each prenex sentence whether it holds in $G$.

This answers Kourovka Problem 16.71 affirmatively (the Kourovka Archive answers "Yes, it is"); it
is Theorem 3 of Kharlampovich and Myasnikov.

Source:
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
