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

/-- **Automorphisms of the regular rooted tree (Kourovka 16.85).** Let $d$ be a natural number and
let $X^*$ be the set of finite words over the alphabet $X = \{0, \dots, d-1\}$, the vertices of the
$d$-regular rooted tree. A permutation $f$ of $X^*$ is a tree automorphism when, for all words $u$
and $v$, the word $f(u)$ has the same length $|u|$ as $u$ and the first $|u|$ letters of $f(uv)$
form the word $f(u)$, where $uv$ denotes concatenation. -/
def IsTreeAut {d : ℕ} (f : Equiv.Perm (List (Fin d))) : Prop :=
  ∀ u v : List (Fin d), (f u).length = u.length ∧ (f (u ++ v)).take u.length = f u

/-- **Section of a permutation of the tree at a vertex (Kourovka 16.85).** For a natural number
$d$, let $X^*$ be the set of finite words over $X = \{0, \dots, d-1\}$, let $f$ be a permutation of
$X^*$ and let $u \in X^*$, of length $|u|$. The section (state) of $f$ at $u$ is the map
$X^* \to X^*$ sending a word $w$ to the word obtained from $f(uw)$ by deleting its first $|u|$
letters (all of them if it has fewer), where $uw$ denotes concatenation. -/
def treeSection {d : ℕ} (f : Equiv.Perm (List (Fin d))) (u : List (Fin d)) :
    List (Fin d) → List (Fin d) :=
  fun w => (f (u ++ w)).drop u.length

/-- **Finite-state automorphisms of the regular rooted tree (Kourovka 16.85).** For a natural
number $d$, let $X^*$ be the set of finite words over $X = \{0, \dots, d-1\}$. A permutation $f$
of $X^*$ is a finite-state automorphism when it is an automorphism of the $d$-regular rooted tree
and its sections at the vertices $u \in X^*$ form a finite set of maps $X^* \to X^*$. -/
def IsFiniteStateAut {d : ℕ} (f : Equiv.Perm (List (Fin d))) : Prop :=
  IsTreeAut f ∧ (Set.range (treeSection f)).Finite

/-- **Faithful actions by finite-state tree automorphisms.** A group $G$ acts faithfully on a
regular rooted tree by finite-state automorphisms when there are a natural number $d \ge 2$ and an
injective group homomorphism $\varphi$ from $G$ to the group of permutations of the set of finite
words over $\{0, \dots, d-1\}$ such that $\varphi(g)$ is a finite-state automorphism of the
$d$-regular rooted tree for every $g \in G$. -/
def ActsFaithfullyByFiniteStateAuts (G : Type) [Group G] : Prop :=
  ∃ (d : ℕ) (f : G →* Equiv.Perm (List (Fin d))), 2 ≤ d ∧ Function.Injective f ∧
    ∀ g : G, IsFiniteStateAut (f g)

/-- **Finite-state actions of free products (Kourovka Problem 16.85).** The statement that for all
groups $G$ and $H$, if $G$ and $H$ each act faithfully on a regular rooted tree by finite-state
automorphisms (the two trees may have different degrees), then so does their free product
$G \ast H$. -/
def finiteStateFreeProduct : Prop :=
  ∀ (G H : Type) [Group G] [Group H], ActsFaithfullyByFiniteStateAuts G →
    ActsFaithfullyByFiniteStateAuts H → ActsFaithfullyByFiniteStateAuts (Monoid.Coprod G H)

/--
**Fedorova–Oliynyk theorem (Kourovka Problem 16.85).** For all groups $G$ and $H$, if $G$ and $H$
each act faithfully on a regular rooted tree by finite-state automorphisms, then their free product
$G \ast H$ acts faithfully on some regular rooted tree by finite-state automorphisms.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
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
