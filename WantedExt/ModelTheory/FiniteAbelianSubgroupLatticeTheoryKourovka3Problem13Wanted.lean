/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Theory of subgroup lattices of finite abelian groups (Kourovka Notebook Problem 3.13)

Kourovka Notebook, Archive of Solved Problems, Problem 3.13 (Yu. L. Ershov, A. I. Kokorin): is the
elementary theory of subgroup lattices of finite abelian groups decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Computability.RE
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.ModelTheory.FiniteAbelianSubgroupLatticeTheoryKourovka3Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.13 (Yu. L.
Ershov, A. I. Kokorin). UnsolvedMath record UM-00700167 (`KOU-3.13`), dataset ulamai/UnsolvedMath
v1.8.0.

The elementary theory of a class is the set of first-order sentences true in all its members.
Sentences of the lattice language are coded in prenex form over the order relation (`x ≤ y`, which
defines `⊓` and `⊔`, and conversely `x ≤ y ↔ x ⊓ y = x`), with a CNF matrix, so that codes form a
`Primcodable` type; every sentence is effectively equivalent to such a code, so decidability does
not depend on the coding. Finite abelian groups are written additively, in `Type`.
-/

/-- A sentence of the first-order language `{≤}` of lattices in prenex form: a quantifier prefix
(`true` is `∀`, `false` is `∃`; the `j`-th quantifier binds `xⱼ`) and a matrix in conjunctive
normal form over literals `(b, (i, j))`, read as `xᵢ ≤ xⱼ` when `b = true` and as its negation
when `b = false`. -/
abbrev LatticeSentence := List Bool × List (List (Bool × (ℕ × ℕ)))

/-- Truth in the lattice `L` of the prenex formula with matrix `φ` and quantifier prefix `qs`,
whose first quantifier binds `xᵢ`, under the assignment `x`. -/
def realizeLatticeSentence {L : Type} [Lattice L] (φ : List (List (Bool × (ℕ × ℕ)))) :
    List Bool → ℕ → (ℕ → L) → Prop
  | [], _, x => ∀ c ∈ φ, ∃ l ∈ c, (x l.2.1 ≤ x l.2.2 ↔ l.1 = true)
  | true :: qs, i, x => ∀ a : L, realizeLatticeSentence φ qs (i + 1) (Function.update x i a)
  | false :: qs, i, x => ∃ a : L, realizeLatticeSentence φ qs (i + 1) (Function.update x i a)

/-- The sentence `s` holds in the subgroup lattice of the abelian group `A`; variables not bound
by the prefix are read as the trivial subgroup. -/
def LatticeSentence.HoldsInSubgroupLattice (s : LatticeSentence) (A : Type) [AddCommGroup A] :
    Prop :=
  realizeLatticeSentence (L := AddSubgroup A) s.2 s.1 0 fun _ => ⊥

/-- Kourovka 3.13 (Yu. L. Ershov, A. I. Kokorin): the elementary theory of the subgroup lattices
of finite abelian groups (the sentences true in all of them) is decidable. -/
def subgroupLatticeTheoryDecidable : Prop :=
  ComputablePred fun s : LatticeSentence =>
    ∀ (A : Type) [AddCommGroup A] [Finite A], s.HoldsInSubgroupLattice A

/--
Resolved false: the Kourovka Archive answers 3.13 "No", citing Kozlov (Algebra and Logic 9 (1970)):
the elementary theory of the class of subgroup lattices of finite abelian groups is undecidable.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.13 (Yu. L.
Ershov, A. I. Kokorin); resolution: G. T. Kozlov, Algebra and Logic 9 (1970), 104-107, Kourovka
Archive, Problem 3.13: No, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted subgroupLatticeTheoryDecidable_refuted : ¬ subgroupLatticeTheoryDecidable

end MathlibExt.ModelTheory.FiniteAbelianSubgroupLatticeTheoryKourovka3Problem13Wanted
