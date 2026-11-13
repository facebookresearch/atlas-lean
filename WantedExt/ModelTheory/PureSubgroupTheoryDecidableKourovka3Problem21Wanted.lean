/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Element-pure-subgroup theories of abelian groups (Kourovka Notebook Problem 3.21)

Kourovka Notebook, Archive of Solved Problems, Problem 3.21 (A. I. Kokorin): let `𝔎` be the class of
one-based models of signature `σ`, `ϑ` a property that makes sense for models in `𝔎`, and `𝔎₀` the
class of two-based models whose first base is a set `M` taken from `𝔎` and whose second base
consists of all submodels of `M` with property `ϑ` and whose signature consists of the symbols in
`σ` together with `∈` and `⊆`. The elementary theory of `𝔎₀` is called the element-`ϑ`-submodel
theory of `𝔎`. Are either of the following theories decidable: (a) the element-pure-subgroup theory
of abelian groups? (b) the element-pure-subgroup theory of abelian torsion-free groups? (c) the
element-`ϑ`-subgroup theory of abelian groups, when the set of `ϑ`-subgroups is linearly ordered by
inclusion?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Computability.RE
public import WantedExt.GroupTheory.PureSubgroupShared

@[expose] public section

namespace MathlibExt.ModelTheory.PureSubgroupTheoryDecidableKourovka3Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.21 (A. I.
Kokorin). UnsolvedMath record UM-00700175 (`KOU-3.21`), dataset ulamai/UnsolvedMath v1.8.0.

Two-sorted sentences (elements, pure subgroups) are coded in prenex form, each quantifier tagged
with its sort, with a CNF matrix over the atoms `t = 0`, `t ∈ X` and `X ⊆ Y`, where `t` is a term of
`{+, -, 0}` (an integer combination of element variables); every atomic formula of the two-sorted
signature reduces effectively to these (`t = s` as `t - s = 0`, `X = Y` as two inclusions), so
decidability does not depend on the coding. Pure subgroups: `nA ∩ B = nB` (shared `IsPureSubgroup`).
Part (c) does not fix the property `ϑ` and is not formalized.
-/

open MathlibExt.GroupTheory.PureSubgroupShared

/-- A term of the language `{+, -, 0}` of abelian groups in the element variables `x₀, x₁, …`,
written as a list of pairs `(c, i)` read as `∑ c • xᵢ`. -/
abbrev LinearTerm := List (ℤ × ℕ)

/-- Atomic formulas of the two-sorted language of an abelian group and its pure subgroups:
`t = 0` (`inl t`), `t ∈ Xⱼ` (`inr (inl (t, j))`) and `Xᵢ ⊆ Xⱼ` (`inr (inr (i, j))`). -/
abbrev PureAtom := LinearTerm ⊕ (LinearTerm × ℕ) ⊕ (ℕ × ℕ)

/-- A two-sorted sentence in prenex form: a prefix of pairs (quantifier, sort), with `true` for
`∀` and for the element sort (the `j`-th quantifier binds `xⱼ` or `Xⱼ`), and a matrix in
conjunctive normal form over literals `(b, atom)` (the atom, or its negation when `b = false`). -/
abbrev PureSentence := List (Bool × Bool) × List (List (Bool × PureAtom))

/-- Value of a linear term under the element assignment `x`. -/
def LinearTerm.eval {A : Type} [AddCommGroup A] (x : ℕ → A) (t : LinearTerm) : A :=
  (t.map fun p => p.1 • x p.2).sum

/-- Truth of an atom under the element assignment `x` and the subgroup assignment `X`. -/
def PureAtom.HoldsAt {A : Type} [AddCommGroup A] (x : ℕ → A) (X : ℕ → AddSubgroup A) :
    PureAtom → Prop
  | .inl t => t.eval x = 0
  | .inr (.inl (t, j)) => t.eval x ∈ X j
  | .inr (.inr (i, j)) => X i ≤ X j

/-- Truth of a prenex formula in the two-sorted structure `(A, pure subgroups of A)`; subgroup
quantifiers range over the pure subgroups. -/
def realizePureSentence {A : Type} [AddCommGroup A] (φ : List (List (Bool × PureAtom))) :
    List (Bool × Bool) → ℕ → (ℕ → A) → (ℕ → AddSubgroup A) → Prop
  | [], _, x, X => ∀ c ∈ φ, ∃ l ∈ c, (l.2.HoldsAt x X ↔ l.1 = true)
  | (true, true) :: qs, i, x, X => ∀ a : A,
      realizePureSentence φ qs (i + 1) (Function.update x i a) X
  | (false, true) :: qs, i, x, X => ∃ a : A,
      realizePureSentence φ qs (i + 1) (Function.update x i a) X
  | (true, false) :: qs, i, x, X => ∀ B : AddSubgroup A, IsPureSubgroup B →
      realizePureSentence φ qs (i + 1) x (Function.update X i B)
  | (false, false) :: qs, i, x, X => ∃ B : AddSubgroup A, IsPureSubgroup B ∧
      realizePureSentence φ qs (i + 1) x (Function.update X i B)

/-- The sentence `s` holds in `(A, pure subgroups of A)`; unbound variables are read as `0` and as
the zero subgroup. -/
def PureSentence.HoldsIn (s : PureSentence) (A : Type) [AddCommGroup A] : Prop :=
  realizePureSentence (A := A) s.2 s.1 0 (fun _ => 0) fun _ => ⊥

/-- Kourovka 3.21(a) (A. I. Kokorin): the element-pure-subgroup theory of abelian groups is
decidable. -/
def elementPureSubgroupTheoryDecidable : Prop :=
  ComputablePred fun s : PureSentence => ∀ (A : Type) [AddCommGroup A], s.HoldsIn A

/-- Kourovka 3.21(b) (A. I. Kokorin): the element-pure-subgroup theory of torsion-free abelian
groups is decidable. -/
def torsionFreeElementPureSubgroupTheoryDecidable : Prop :=
  ComputablePred fun s : PureSentence =>
    ∀ (A : Type) [AddCommGroup A], (∀ (n : ℕ) (a : A), n ≠ 0 → n • a = 0 → a = 0) → s.HoldsIn A

/--
Resolved false: the Kourovka Archive answers 3.21 "No, in all cases", citing Kozlov (Algebra and
Logic 9 (1970); Algebra, Irkutsk, 1972) for part (a): the element-pure-subgroup theory of abelian
groups is undecidable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 3.21 (A. I. Kokorin); resolution: G. T. Kozlov, Algebra and Logic 9 (1970), 104-107, and
Algebra, no. 1, Irkutsk Univ., 1972, 21-23 (Russian) (parts a, c); É. I. Fridman, Algebra, no. 1,
Irkutsk Univ., 1972, 97-100 (Russian) (part b), Kourovka Archive, Problem 3.21: No, in all cases,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted elementPureSubgroupTheoryDecidable_refuted :
    ¬ elementPureSubgroupTheoryDecidable

/--
Resolved false: the Kourovka Archive answers 3.21 "No, in all cases", citing Fridman (Algebra,
Irkutsk, 1972) for part (b): the element-pure-subgroup theory of torsion-free abelian groups is
undecidable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.21
(A. I. Kokorin); resolution: G. T. Kozlov, Algebra and Logic 9 (1970), 104-107, and Algebra, no. 1,
Irkutsk Univ., 1972, 21-23 (Russian) (parts a, c); É. I. Fridman, Algebra, no. 1, Irkutsk Univ.,
1972, 97-100 (Russian) (part b), Kourovka Archive, Problem 3.21: No, in all cases,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted torsionFreeElementPureSubgroupTheoryDecidable_refuted :
    ¬ torsionFreeElementPureSubgroupTheoryDecidable

end MathlibExt.ModelTheory.PureSubgroupTheoryDecidableKourovka3Problem21Wanted
