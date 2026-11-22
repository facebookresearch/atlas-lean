/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal commutators of basic commutators in free groups (Kourovka Notebook Problem 11.20)

Kourovka Notebook, Archive of Solved Problems, Problem 11.20 (A. Gaglione, D. Spellman): suppose
`[a, b] = [c, d]` in an absolutely free group, where `a`, `b`, `[a, b]` are basic commutators (in
some fixed free generators). If `c` and `d` are arbitrary (proper) commutators, does it follow that
`a = c` and `b = d`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.BasicCommutatorEqualityKourovka11Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.20 (A.
Gaglione, D. Spellman). UnsolvedMath record UM-00700713 (`KOU-11.20`), dataset ulamai/UnsolvedMath
v1.8.0.

Commutators follow the source (and Hall) convention `[x, y] = x⁻¹ y⁻¹ x y`. Basic commutators are
Hall's: formal commutators are bracket arrangements of the letters, ordered by a linear order that
extends the order of the free generators and puts smaller weight first, arbitrary within a weight;
letters are basic, and `[u, v]` is basic iff `u`, `v` are basic, `v < u`, and `z ≤ v` whenever `u =
[y, z]`. The claim quantifies over every such ordering. "`a`, `b`, `[a, b]` basic" is the formal
commutator `[a, b]` being basic, which includes `a` and `b`. "Arbitrary (proper) commutators" are
elements of the form `[x, y]`.
-/

/-- Formal commutators (bracket arrangements) in the letters `α`. -/
inductive Bracket (α : Type*)
  /-- A letter, a formal commutator of weight 1. -/
  | letter : α → Bracket α
  /-- The formal commutator `[u, v]`. -/
  | comm : Bracket α → Bracket α → Bracket α

/-- The weight of a formal commutator: the number of letters it contains. -/
def Bracket.weight {α : Type*} : Bracket α → ℕ
  | letter _ => 1
  | comm u v => u.weight + v.weight

/-- The commutator `[x, y] = x⁻¹ y⁻¹ x y` (the convention of the Kourovka Notebook and of Hall). -/
def kcomm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- The value of a formal commutator in the free group on `α`. -/
def Bracket.eval {α : Type*} : Bracket α → FreeGroup α
  | letter a => FreeGroup.of a
  | comm u v => kcomm u.eval v.eval

/-- Basic commutators (M. Hall) for an ordering `lt` of the formal commutators: letters are basic,
and `[u, v]` is basic iff `u` and `v` are basic, `v < u`, and `z ≤ v` whenever `u = [y, z]`. -/
def Bracket.IsBasic {α : Type*} (lt : Bracket α → Bracket α → Prop) : Bracket α → Prop
  | letter _ => True
  | comm u v => u.IsBasic lt ∧ v.IsBasic lt ∧ lt v u ∧
      match u with
      | letter _ => True
      | comm _ z => ¬ lt v z

/-- Kourovka 11.20 (A. Gaglione, D. Spellman): in an absolutely free group with linearly ordered
free generators, if `[a, b] = [c, d]` where `a`, `b` and `[a, b]` are basic commutators and `c`,
`d` are arbitrary commutators, then `a = c` and `b = d`. The basic commutators are those of every
ordering admitted by Hall's definition: a linear order of the formal commutators that extends the
order of the generators and puts commutators of smaller weight first (within one weight it is
arbitrary). -/
def basicCommutatorEqualityDetermines : Prop :=
  ∀ (α : Type) [LinearOrder α] (o : LinearOrder (Bracket α)),
    (∀ u v : Bracket α, u.weight < v.weight → o.lt u v) →
    (∀ a b : α, a < b → o.lt (.letter a) (.letter b)) →
    ∀ ta tb : Bracket α, (Bracket.comm ta tb).IsBasic o.lt →
    ∀ c d : FreeGroup α, (∃ x y : FreeGroup α, c = kcomm x y) →
      (∃ x y : FreeGroup α, d = kcomm x y) →
      kcomm ta.eval tb.eval = kcomm c d → ta.eval = c ∧ tb.eval = d

/--
Resolved false: the Kourovka Archive records Bardakov's example. For free generators `x₁ < x₂ < x₃`
put `b = [x₂, x₁]`, `a = [b, x₃]`, `c = b⁻¹ = [x₁, x₂]` and `d = b^{x₃ b} = [x₂^{x₃ b}, x₁^{x₃ b}]`;
for every admissible ordering `a`, `b` and `[a, b]` are basic (weights 3, 2 and 5), and `[a, b] =
[c, d]` (both equal `x₃⁻¹ b⁻¹ x₃ b⁻¹ x₃⁻¹ b x₃ b`), while `a ≠ c`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.20 (A. Gaglione, D. Spellman);
resolution: V. G. Bardakov, Abstracts of the IIIrd Intern. Conf. on Algebra, Krasnoyarsk, 1993, p.
33 (Russian), Kourovka Archive, Problem 11.20: "No, not always"; for free generators `x₁ < x₂ < x₃`,
`a = [[x₂, x₁], x₃]`, `b = [x₂, x₁]`, `c = b⁻¹`, `d = b^{x₃ b}`, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted basicCommutatorEqualityDetermines_refuted :
    ¬ basicCommutatorEqualityDetermines

end MathlibExt.GroupTheory.BasicCommutatorEqualityKourovka11Problem20Wanted
