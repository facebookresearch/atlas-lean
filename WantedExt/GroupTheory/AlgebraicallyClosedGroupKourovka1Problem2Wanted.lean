/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Algebraically closed groups (Kourovka Notebook Problem 1.2)

Kourovka Notebook, Archive of Solved Problems, Problem 1.2 (L. A. Bokut'): an equation over a group
`G` in the unknowns `x₁, …, xₙ` is `v(x₁, …, xₙ) = 1`, where `v` is an element of the free product
`R = G * F` with the free group `F` on `x₁, …, xₙ`, not conjugate in `R` to any element of `G`. `G`
is algebraically closed if every equation over `G` has a solution in `G`. Do there exist
algebraically closed groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AlgebraicallyClosedGroupKourovka1Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.2 (L. A.
Bokut'). UnsolvedMath record UM-00700002 (`KOU-1.2`), dataset ulamai/UnsolvedMath v1.8.0.

The free product is `Monoid.Coprod G (FreeGroup (Fin n))` and a solution `x : Fin n → G` is
evaluated by the homomorphism that is the identity on `G`; the definition quantifies over every
number `n` of unknowns. `G` is required to be nontrivial: the trivial group satisfies the
definition, since every equation over it has the solution `x = 1`.
-/

/-- `G` is algebraically closed in the sense of Kourovka 1.2: every equation `v(x₁, …, xₙ) = 1` over
`G`, where `v` is an element of the free product `G * F_n` not conjugate in `G * F_n` to an element
of `G`, has a solution in `G`. -/
def IsAlgebraicallyClosedGroup (G : Type) [Group G] : Prop :=
  ∀ (n : ℕ) (v : Monoid.Coprod G (FreeGroup (Fin n))),
    (∀ g : G, ¬ IsConj v (Monoid.Coprod.inl g)) →
      ∃ x : Fin n → G, Monoid.Coprod.lift (MonoidHom.id G) (FreeGroup.lift x) v = 1

/-- Kourovka 1.2 (L. A. Bokut'): there is a nontrivial algebraically closed group. -/
def existsAlgebraicallyClosedGroup : Prop :=
  ∃ (G : Type) (_ : Group G), Nontrivial G ∧ IsAlgebraicallyClosedGroup G

/--
Resolved true: the Kourovka Archive answers 1.2 "Yes, such groups do exist", citing Brodskiĭ
(deposited manuscript, VINITI, 1980). In the published account (Sib. Math. J. 1984) Brodskiĭ
constructs a nontrivial class of locally indicable groups in which every equation over a group of
the class has a solution in a larger group of the class, from which an affirmative answer to Bokut's
question follows (zbMATH review, Zbl 0579.20020). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 1.2 (L. A. Bokut'); resolution: S. D. Brodskiĭ, Dep. no.
2214-80, VINITI, Moscow, 1980 (Russian); S. D. Brodskiĭ, Equations over groups, and groups with one
defining relation, Sib. Math. J. 25 (1984), 235-251 (Zbl 0579.20020), Kourovka Archive, Problem 1.2
(Yes, such groups do exist).
-/
public theorem_wanted existsAlgebraicallyClosedGroup_holds : existsAlgebraicallyClosedGroup

end MathlibExt.GroupTheory.AlgebraicallyClosedGroupKourovka1Problem2Wanted
