/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elementary theory of l-ideal lattices of abelian l-groups (Kourovka Notebook Problem 5.20)

Kourovka Notebook, Archive of Solved Problems, Problem 5.20 (A. I. Kokorin): is the elementary
theory of lattices of l-ideals of lattice-ordered abelian groups decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Computability.RE

@[expose] public section

namespace MathlibExt.GroupTheory.LIdealLatticeTheoryKourovka5Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.20 (A. I.
Kokorin). UnsolvedMath record UM-00700304 (`KOU-5.20`), dataset ulamai/UnsolvedMath v1.8.0.

A lattice-ordered abelian group is a commutative group with a lattice order invariant under
multiplication (`CommGroup`, `Lattice`, `IsOrderedMonoid`). Its `l`-ideals are the solid subgroups
(`|b| ≤ |a|` and `a ∈ H` imply `b ∈ H`, with `|a| = mabs a`), which in the abelian case are exactly
the convex `l`-subgroups; they form a lattice under inclusion. The theory is the set of first-order
sentences of the language of lattices true in every such lattice; sentences use the order `≤` only,
since `⊔` and `⊓` are definable from it. Decidability is `ComputablePred` on codes of sentences in
prenex normal form with a matrix in conjunctive normal form; every first-order sentence is
effectively equivalent to such a code and every code is a sentence, so decidability does not depend
on the coding. Variables not bound by the prefix are read as the least `l`-ideal `{1}`.
-/

/-- `H` is an `l`-ideal of the lattice-ordered abelian group `G`: a subgroup that is solid
(`|b| ≤ |a|` and `a ∈ H` imply `b ∈ H`). In an abelian `l`-group these are exactly the convex
`l`-subgroups. -/
def IsLIdeal {G : Type} [CommGroup G] [Lattice G] (H : Subgroup G) : Prop :=
  ∀ a ∈ H, ∀ b : G, mabs b ≤ mabs a → b ∈ H

/-- A quantifier-free formula of the language of lattices (with the order `≤`; the operations `⊔`
and `⊓` are definable) in conjunctive normal form: clauses of literals `(true, (i, j))` (meaning
`xᵢ ≤ xⱼ`) or `(false, (i, j))` (meaning `¬ xᵢ ≤ xⱼ`). -/
abbrev CNF := List (List (Bool × (ℕ × ℕ)))

/-- `realizeFrom M qs k x`: the formula with quantifier prefix `qs` (`true` for `∀`, `false` for
`∃`), binding `x_k, x_(k+1), …` in order and ranging over the `l`-ideals of `G` ordered by
inclusion, followed by the matrix `M`, holds under the assignment `x`. -/
def realizeFrom {G : Type} [CommGroup G] [Lattice G] (M : CNF) :
    List Bool → ℕ → (ℕ → Subgroup G) → Prop
  | [], _, x => ∀ c ∈ M, ∃ l ∈ c, (x l.2.1 ≤ x l.2.2 ↔ l.1 = true)
  | true :: qs, k, x =>
      ∀ H : Subgroup G, IsLIdeal H → realizeFrom M qs (k + 1) (Function.update x k H)
  | false :: qs, k, x =>
      ∃ H : Subgroup G, IsLIdeal H ∧ realizeFrom M qs (k + 1) (Function.update x k H)

/-- A first-order sentence of the language of lattices, coded in prenex normal form (a quantifier
prefix binding `x₀, x₁, …` in order and a matrix in conjunctive normal form); variables not bound
by the prefix are read as the least `l`-ideal `{1}`. -/
abbrev LatticeSentence := List Bool × CNF

/-- The sentence `φ` holds in the lattice of `l`-ideals of `G`. -/
def LatticeSentence.HoldsIn (φ : LatticeSentence) (G : Type) [CommGroup G] [Lattice G] : Prop :=
  realizeFrom (G := G) φ.2 φ.1 0 (fun _ => ⊥)

/-- Kourovka 5.20 (A. I. Kokorin): the elementary theory of the class of lattices of `l`-ideals of
lattice-ordered abelian groups is decidable. -/
def lIdealLatticeTheoryDecidable : Prop :=
  ComputablePred fun φ : LatticeSentence =>
    ∀ (G : Type) [CommGroup G] [Lattice G] [IsOrderedMonoid G], φ.HoldsIn G

/--
Resolved false: Medvedev (Algebra and Logic 44 (2005), 302-312, abstract) proves that the elementary
theory of the lattices of `l`-ideals of abelian lattice-ordered groups is undecidable, a negative
solution to Problem 5.20; the Kourovka Archive answers "No, it is undecidable". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.20 (A. I. Kokorin);
resolution: N. Ya. Medvedev, Elementary theory for l-ideal lattices of abelian l-groups, Algebra and
Logic 44 (2005), 302-312, abstract: it is proved that the elementary theory for l-ideal lattices of
abelian lattice-ordered groups is undecidable, which gives a negative solution to Problem 5.20;
Kourovka Archive, Problem 5.20: No, it is undecidable, https://doi.org/10.1007/s10469-005-0029-5.
-/
public theorem_wanted lIdealLatticeTheoryDecidable_refuted : ¬ lIdealLatticeTheoryDecidable

end MathlibExt.GroupTheory.LIdealLatticeTheoryKourovka5Problem20Wanted
