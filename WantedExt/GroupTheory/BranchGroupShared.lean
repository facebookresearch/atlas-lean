/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Branch groups

Shared definition of branch groups for the Kourovka Notebook entries (Problem 20.101): a group
acting faithfully and level-transitively on a locally finite rooted tree in which every vertex has
at least two children, with every rigid level stabilizer of finite index (Garciarena-Petschick,
Maximal subgroups in torsion branch groups, arXiv:2410.06783, Section 2, for subgroups of
`Aut(X*)`). The definitions repeat, with the same names and field docstrings added, those of the
OpenConjectures entry `OpenConjectures.GroupTheory.BranchGroupsBoundedlyAcyclic` (Kourovka 21.116),
which `WantedExt` cannot import.
-/

module

public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.BranchGroupShared

/-- **Rooted tree given by levels.** A locally finite rooted tree is given by finite sets $V_n$ for
$n \ge 0$, the vertices at level $n$, where $V_0$ consists of the root alone, together with parent
maps $V_{n+1} \to V_n$, such that every vertex has at least two children: for every $v \in V_n$
there are distinct $x, y \in V_{n+1}$ whose parent is $v$. -/
structure RootedTree where
  /-- The vertices at level `n`. -/
  Vertex : ℕ → Type
  /-- Every level is finite. -/
  levelFinite : ∀ n, Finite (Vertex n)
  /-- Level `0` is the root alone. -/
  rootUnique : Unique (Vertex 0)
  /-- The parent of a vertex at level `n + 1`. -/
  parent : ∀ n, Vertex (n + 1) → Vertex n
  /-- Every vertex has at least two children. -/
  twoChildren : ∀ n (v : Vertex n), ∃ x y : Vertex (n + 1), parent n x = v ∧ parent n y = v ∧ x ≠ y

/-- **Descendants in a rooted tree.** For vertices $v$ at level $n$ and $w$ at level $m$ of a
rooted tree $T$, $w$ is a descendant of $v$ when $w$ is reached from $v$ by moving from a vertex
to one of its children zero or more times: $v$ is a descendant of itself, and a vertex at level
$k + 1$ is a descendant of $v$ whenever its parent is. -/
inductive RootedTree.IsDescendant (T : RootedTree) : {n m : ℕ} → T.Vertex n → T.Vertex m → Prop
  | refl {n} (v : T.Vertex n) : RootedTree.IsDescendant T v v
  | child {n m} {v : T.Vertex n} (w : T.Vertex (m + 1))
      (h : RootedTree.IsDescendant T v (T.parent m w)) : RootedTree.IsDescendant T v w

/-- **Faithful level-transitive action on a rooted tree.** Let $T$ be a rooted tree with vertex
sets $V_n$ at the levels $n \ge 0$ and parent maps $V_{n+1} \to V_n$, and let $G$ be a group. A
faithful level-transitive action of $G$ on $T$ consists of an action of $G$ on each level $V_n$ by
permutations, that is, a homomorphism $G \to \mathrm{Sym}(V_n)$ for every $n$, such that the
actions commute with the parent maps (so $G$ acts by tree automorphisms), only the identity of $G$
fixes every vertex of $T$, and $G$ acts transitively on every level $V_n$. -/
structure LevelTransitiveFaithfulAction (T : RootedTree) (G : Type) [Group G] where
  /-- The action on level `n`. -/
  levelAction : ∀ n, G →* Equiv.Perm (T.Vertex n)
  /-- The level actions commute with the parent maps, so `G` acts by tree automorphisms. -/
  parent_equivariant : ∀ (g : G) (n : ℕ) (w : T.Vertex (n + 1)),
    T.parent n (levelAction (n + 1) g w) = levelAction n g (T.parent n w)
  /-- Only `1` fixes every vertex. -/
  faithful : ∀ g : G, (∀ n (v : T.Vertex n), levelAction n g v = v) → g = 1
  /-- `G` is transitive on every level. -/
  level_transitive : ∀ n (v w : T.Vertex n), ∃ g : G, levelAction n g v = w

/-- **Rigid vertex stabilizer.** Given a faithful level-transitive action of a group $G$ on a
rooted tree $T$ and a vertex $v$ of $T$, an element $g \in G$ lies in the rigid stabilizer of $v$
when $g$ fixes every vertex of $T$ that is not a descendant of $v$. -/
def LevelTransitiveFaithfulAction.IsRigidAt {T : RootedTree} {G : Type} [Group G]
    (A : LevelTransitiveFaithfulAction T G) {n : ℕ} (v : T.Vertex n) (g : G) : Prop :=
  ∀ {m : ℕ} (w : T.Vertex m), ¬ T.IsDescendant v w → A.levelAction m g w = w

/-- **Rigid stabilizer of a level.** Given a faithful level-transitive action of a group $G$ on a
rooted tree $T$ and a level $n$, the rigid stabilizer of level $n$ is the subgroup of $G$ generated
by the rigid stabilizers of all vertices of $T$ at level $n$. -/
def LevelTransitiveFaithfulAction.rigidLevelStabilizer {T : RootedTree} {G : Type} [Group G]
    (A : LevelTransitiveFaithfulAction T G) (n : ℕ) : Subgroup G :=
  Subgroup.closure {g : G | ∃ v : T.Vertex n, A.IsRigidAt v g}

/-- **Branch action.** A faithful level-transitive action of a group $G$ on a rooted tree $T$ is a
branch action when, for every level $n$, the rigid stabilizer of level $n$ has finite index in
$G$. -/
def LevelTransitiveFaithfulAction.IsBranchAction {T : RootedTree} {G : Type} [Group G]
    (A : LevelTransitiveFaithfulAction T G) : Prop :=
  ∀ n : ℕ, (A.rigidLevelStabilizer n).FiniteIndex

/-- **Branch group.** A group $G$ is a branch group when there exist a rooted tree $T$ (locally
finite, with every vertex having at least two children) and a faithful level-transitive action of
$G$ on $T$ by tree automorphisms that is a branch action. -/
def IsBranchGroup (G : Type) [Group G] : Prop :=
  ∃ (T : RootedTree) (A : LevelTransitiveFaithfulAction T G), A.IsBranchAction

end MathlibExt.GroupTheory.BranchGroupShared
