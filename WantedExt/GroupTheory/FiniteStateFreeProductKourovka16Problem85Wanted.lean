/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-state actions of free products (Kourovka Notebook Problem 16.85)

Kourovka Notebook, Archive of Solved Problems, Problem 16.85 (V. I. Sushchanskiĭ): suppose that
groups `G`, `H` act faithfully on a regular rooted tree by finite-state automorphisms. Can their
free product `G ∗ H` act faithfully on a regular rooted tree by finite state automorphisms?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Coprod.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteStateFreeProductKourovka16Problem85Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.85 (V. I.
Sushchanskiĭ). UnsolvedMath record UM-00701276 (`KOU-16.85`), dataset ulamai/UnsolvedMath v1.8.0.

Trees, tree automorphisms and finite-state automorphisms are as in Problem 16.34. A group acts
faithfully by finite-state automorphisms if it embeds in the finite-state automorphisms of the
`d`-regular rooted tree for some `d ≥ 2`; `G` and `H` may act on trees of different degrees, as in
the resolution. The free product is `Monoid.Coprod G H`.
-/

/-- `f` is an automorphism of the `d`-regular rooted tree, whose vertices are the words over
`Fin d`: it preserves the length of words and the prefix relation. -/
def IsTreeAut {d : ℕ} (f : Equiv.Perm (List (Fin d))) : Prop :=
  ∀ u v : List (Fin d), (f u).length = u.length ∧ (f (u ++ v)).take u.length = f u

/-- The section (state) of `f` at the vertex `u`: the map `w ↦ f (u ++ w)` with the prefix of
length `|u|` removed. -/
def treeSection {d : ℕ} (f : Equiv.Perm (List (Fin d))) (u : List (Fin d)) :
    List (Fin d) → List (Fin d) :=
  fun w => (f (u ++ w)).drop u.length

/-- `f` is a finite-state automorphism of the `d`-regular rooted tree: a tree automorphism with
finitely many distinct sections. -/
def IsFiniteStateAut {d : ℕ} (f : Equiv.Perm (List (Fin d))) : Prop :=
  IsTreeAut f ∧ (Set.range (treeSection f)).Finite

/-- `G` acts faithfully on a regular rooted tree by finite-state automorphisms: for some `d ≥ 2`
there is an injective homomorphism from `G` to the permutations of the words over `Fin d` whose
values are finite-state tree automorphisms. -/
def ActsFaithfullyByFiniteStateAuts (G : Type) [Group G] : Prop :=
  ∃ (d : ℕ) (f : G →* Equiv.Perm (List (Fin d))), 2 ≤ d ∧ Function.Injective f ∧
    ∀ g : G, IsFiniteStateAut (f g)

/-- Kourovka 16.85 (V. I. Sushchanskiĭ): if `G` and `H` act faithfully on regular rooted trees by
finite-state automorphisms, then so does the free product `G ∗ H`. -/
def finiteStateFreeProduct : Prop :=
  ∀ (G H : Type) [Group G] [Group H], ActsFaithfullyByFiniteStateAuts G →
    ActsFaithfullyByFiniteStateAuts H → ActsFaithfullyByFiniteStateAuts (Monoid.Coprod G H)

/--
Resolved true: Fedorova and Oliynyk prove that for groups `G` and `H` that act faithfully by
finite-state automorphisms on regular rooted trees, the free product `G ∗ H` acts faithfully by
finite-state automorphisms on some regular rooted tree (abstract; the main step is Theorem 1, `FAut
Tₙ ∗ FAut Tₙ` embeds in `FAut T₃ₙ`), solving Problem 16.85; the Kourovka Archive answers 16.85 "Yes,
it can". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.85
(V. I. Sushchanskiĭ); resolution: M. Fedorova and A. Oliynyk, Finite automaton actions of free
products of groups, Algebra Discrete Math. 23 (2017), no. 2, 230-236, abstract (for groups G and H
that act faithfully by finite state automorphisms on regular rooted trees, G ∗ H admits a faithful
action by finite state automorphisms on some regular rooted tree) and Theorem 1 (FAut T_n ∗ FAut T_n
is isomorphic to a subgroup of FAut T_3n); Kourovka Archive, Problem 16.85 (Yes, it can),
https://admjournal.luguniv.edu.ua/index.php/adm/article/view/477.
-/
public theorem_wanted finiteStateFreeProduct_holds : finiteStateFreeProduct

end MathlibExt.GroupTheory.FiniteStateFreeProductKourovka16Problem85Wanted
