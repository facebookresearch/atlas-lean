/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/

set_option autoImplicit false

open BigOperators

@[expose] public section

/-- **Multigraph.** A multigraph on a vertex set $V$ is given by an edge multiplicity function $m$
that assigns to every two vertices $v, w \in V$ a natural number $m(v, w)$ and is symmetric:
$m(v, w) = m(w, v)$ for all $v, w \in V$. Loops are permitted: $m(v, v)$ may be positive. -/
structure Multigraph (V : Type*) where
  /-- The multiplicity of edges between two vertices. -/
  edgeMult : V → V → ℕ
  /-- Edge multiplicity is symmetric. -/
  symm : ∀ v w, edgeMult v w = edgeMult w v

namespace Multigraph

variable {V : Type*}

/-- **Adjacency in a multigraph.** Two vertices $v$ and $w$ of a multigraph $G$ are adjacent when
the edge multiplicity between $v$ and $w$ is positive. -/
def Adj (G : Multigraph V) (v w : V) : Prop :=
  0 < G.edgeMult v w

/--
**Degree of a vertex in a multigraph.** For a multigraph $G$ on a finite vertex set $V$ with edge
multiplicity $m$, the degree of a vertex $v$ is $\sum_{w \in V} m(v, w)$. A loop at $v$
contributes its multiplicity once, matching the outgoing-isogeny convention.
-/
def degree (G : Multigraph V) [Fintype V] (v : V) : ℕ :=
  ∑ w : V, G.edgeMult v w

/-- **Degree restricted to a predicate.** Let $G$ be a multigraph on a finite vertex set $V$ with
edge multiplicity $m$, let $v \in V$ and let $P$ be a decidable predicate on $V$. The degree of
$v$ restricted to $P$ is $\sum_{w \in V,\, P(w)} m(v, w)$. -/
def degreeOn (G : Multigraph V) [Fintype V] (v : V)
    (P : V → Prop) [DecidablePred P] : ℕ :=
  ∑ w ∈ Finset.univ.filter P, G.edgeMult v w

/-- **Connectivity of vertices in a multigraph.** Two vertices $v$ and $w$ of a multigraph $G$ are
connected when they are related by the reflexive-transitive closure of adjacency, that is, when
there is a finite sequence of vertices $v = u_0, u_1, \dots, u_k = w$ with $k \ge 0$ and $u_i$
adjacent to $u_{i+1}$ for each $i < k$. -/
def Connected (G : Multigraph V) (v w : V) : Prop :=
  Relation.ReflTransGen G.Adj v w

/-- **Connected multigraph.** A multigraph $G$ is connected when every two vertices $v$ and $w$
of $G$ are joined by a walk, that is, $w$ is reachable from $v$ by a finite (possibly empty)
sequence of steps along edges of positive multiplicity. -/
def IsConnected (G : Multigraph V) : Prop :=
  ∀ v w, G.Connected v w

/-- **Symmetry of adjacency in a multigraph.** In a multigraph $G$, a vertex $v$ is adjacent to a
vertex $w$ if and only if $w$ is adjacent to $v$. -/
theorem adj_comm (G : Multigraph V) (v w : V) :
    G.Adj v w ↔ G.Adj w v := by
  unfold Adj
  rw [G.symm v w]

/-- **Every vertex is connected to itself.** In a multigraph $G$, every vertex $v$ is connected to
$v$. -/
theorem connected_refl (G : Multigraph V) (v : V) :
    G.Connected v v :=
  Relation.ReflTransGen.refl

/-- **Degree splits over a predicate and its complement.** Let $G$ be a multigraph on a finite
vertex set $V$, let $v \in V$ and let $P$ be a decidable predicate on $V$. Then the degree of $v$
equals the degree of $v$ restricted to $P$ plus the degree of $v$ restricted to $\neg P$. -/
theorem degreeOn_compl (G : Multigraph V) [Fintype V]
    (v : V) (P : V → Prop) [DecidablePred P] :
    G.degree v = G.degreeOn v P + G.degreeOn v (fun w => ¬ P w) := by
  unfold degree degreeOn
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ P _).symm

/-- **Restricted degree depends only on the neighbours.** Let $G$ be a multigraph on a finite
vertex set $V$, let $v \in V$ and let $P$ and $Q$ be decidable predicates on $V$. If
$P(w) \iff Q(w)$ for every vertex $w$ whose edge multiplicity with $v$ is positive, then the
degree of $v$ restricted to $P$ equals the degree of $v$ restricted to $Q$. -/
theorem degreeOn_congr (G : Multigraph V) [Fintype V]
    (v : V) {P Q : V → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ w, G.edgeMult v w > 0 → (P w ↔ Q w)) :
    G.degreeOn v P = G.degreeOn v Q := by
  unfold degreeOn
  have hsubP :
      Finset.univ.filter (fun w => P w ∧ Q w) ⊆
        Finset.univ.filter P := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.1
  have hsubQ :
      Finset.univ.filter (fun w => P w ∧ Q w) ⊆
        Finset.univ.filter Q := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.2
  have hzP : ∀ x ∈ Finset.univ.filter P,
      x ∉ Finset.univ.filter (fun w => P w ∧ Q w) →
        G.edgeMult v x = 0 := by
    intro x hxP hxN
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hxP hxN
    have hNQ : ¬ Q x := fun hQx => hxN ⟨hxP, hQx⟩
    by_contra hne
    have hpos : G.edgeMult v x > 0 :=
      Nat.pos_of_ne_zero hne
    exact hNQ ((h x hpos).mp hxP)
  have hzQ : ∀ x ∈ Finset.univ.filter Q,
      x ∉ Finset.univ.filter (fun w => P w ∧ Q w) →
        G.edgeMult v x = 0 := by
    intro x hxQ hxN
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hxQ hxN
    have hNP : ¬ P x := fun hPx => hxN ⟨hPx, hxQ⟩
    by_contra hne
    have hpos : G.edgeMult v x > 0 :=
      Nat.pos_of_ne_zero hne
    exact hNP ((h x hpos).mpr hxQ)
  have eP := Finset.sum_subset hsubP hzP
  have eQ := Finset.sum_subset hsubQ hzQ
  rw [← eP, ← eQ]

end Multigraph

/-- **Isogeny volcano.** Let $\ell$ be a prime. An $\ell$-isogeny volcano consists of a finite
vertex set $V$, a multigraph on $V$ with edge multiplicities $m(v, w)$, a depth $d \in \mathbb{N}$,
a surjective level map $\mathrm{lev} : V \to \{0, 1, \dots, d\}$ and a surface degree
$s \in \mathbb{N}$ with $s \le 2$, subject to the following conditions, where the surface is the
set of vertices of level $0$. Every surface vertex $v$ satisfies
$\sum_{w \in V,\ \mathrm{lev}(w) = 0} m(v, w) = s$. Every vertex $v$ of positive level has a
unique parent: $\sum_{w \in V,\ \mathrm{lev}(w) + 1 = \mathrm{lev}(v)} m(v, w) = 1$. Whenever
$m(v, w) > 0$, either $v$ and $w$ both lie on the surface or their levels differ by exactly one.
Every vertex $v$ with $\mathrm{lev}(v) < d$ has degree $\sum_{w \in V} m(v, w) = \ell + 1$, where a
loop at $v$ contributes its multiplicity once. Finally, the multigraph is connected: any two
vertices are joined by a path along which consecutive vertices have positive edge multiplicity. -/
structure IsogenyVolcano (ℓ : ℕ) where
  /-- The isogeny degree is prime. -/
  prime : Nat.Prime ℓ
  /-- Vertex type. -/
  V : Type*
  /-- Finite vertices. -/
  instFintype : Fintype V
  /-- Decidable equality on vertices. -/
  instDecEq : DecidableEq V
  /-- Underlying multigraph. -/
  graph : Multigraph V
  /-- Depth of the volcano. -/
  depth : ℕ
  /-- Level of each vertex. -/
  level : V → Fin (depth + 1)
  /-- Every level is inhabited. -/
  level_surj : Function.Surjective level
  /-- Surface degree. -/
  surfaceDegree : ℕ
  /-- Surface degree is at most two. -/
  surfaceDegree_le : surfaceDegree ≤ 2
  /-- Surface regularity. -/
  surface_regular : ∀ v,
    level v = ⟨0, Nat.zero_lt_succ _⟩ →
      graph.degreeOn v
        (fun w => level w = ⟨0, Nat.zero_lt_succ _⟩) =
        surfaceDegree
  /-- Every nonsurface vertex has a unique parent. -/
  unique_parent : ∀ v, (level v : ℕ) > 0 →
    graph.degreeOn v
      (fun w => (level w : ℕ) + 1 = (level v : ℕ)) = 1
  /-- Positive edges stay within or across adjacent levels. -/
  edges_between_levels : ∀ v w, graph.edgeMult v w > 0 →
    ((level v : ℕ) = 0 ∧ (level w : ℕ) = 0) ∨
      (level w : ℕ) + 1 = (level v : ℕ) ∨
        (level v : ℕ) + 1 = (level w : ℕ)
  /-- Regularity below the floor. -/
  degree_eq : ∀ v, (level v : ℕ) < depth →
    graph.degree v = ℓ + 1
  /-- The graph is connected. -/
  connected : graph.IsConnected

instance {ℓ : ℕ} (C : IsogenyVolcano ℓ) : Fintype C.V :=
  C.instFintype

instance {ℓ : ℕ} (C : IsogenyVolcano ℓ) : DecidableEq C.V :=
  C.instDecEq

namespace IsogenyVolcano

variable {ℓ : ℕ} {C : IsogenyVolcano ℓ}

/-- **Surface of a volcano.** A vertex $v$ of an $\ell$-isogeny volcano $C$ lies on the surface
of $C$ when its level is $0$. -/
def isSurface (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = 0

/-- **Floor of a volcano.** A vertex $v$ of an $\ell$-isogeny volcano $C$ of depth $d$ lies on
the floor of $C$ when its level is $d$, the last of the levels $0, 1, \dots, d$. -/
def isFloor (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = Fin.last C.depth

/-- **Depth of an isogeny volcano.** The depth of an $\ell$-isogeny volcano $C$ is the natural
number $d$ recorded in $C$: the levels of the vertices of $C$ are exactly $0, 1, \dots, d$, with
level $0$ the surface and level $d$ the floor. -/
def volcanoDepth (C : IsogenyVolcano ℓ) : ℕ :=
  C.depth

/-- **Horizontal edge.** In an $\ell$-isogeny volcano $C$, the pair $(v, w)$ of vertices is a
horizontal edge when the edge multiplicity between $v$ and $w$ is positive and both $v$ and $w$
lie on the surface, that is, both have level $0$. -/
def IsHorizontalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) = 0 ∧ (C.level w : ℕ) = 0

/-- **Descending edge.** In an $\ell$-isogeny volcano $C$, the pair $(v, w)$ of vertices is a
descending edge when the edge multiplicity between $v$ and $w$ is positive and $w$ lies one level
below $v$, that is, the level of $v$ plus one equals the level of $w$ (level $0$ being the
surface). -/
def IsDescendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) + 1 = (C.level w : ℕ)

/-- **Ascending edge.** In an $\ell$-isogeny volcano $C$, the pair $(v, w)$ of vertices is an
ascending edge when the edge multiplicity between $v$ and $w$ is positive and $w$ lies one level
above $v$, that is, the level of $w$ plus one equals the level of $v$ (level $0$ being the
surface). -/
def IsAscendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level w : ℕ) + 1 = (C.level v : ℕ)

/-- **Vertical edge.** In an $\ell$-isogeny volcano $C$, the pair $(v, w)$ of vertices is a
vertical edge when it is a descending edge or an ascending edge, that is, when the edge
multiplicity between $v$ and $w$ is positive and the levels of $v$ and $w$ differ by exactly
one. -/
def IsVerticalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.IsDescendingEdge v w ∨ C.IsAscendingEdge v w

instance decPredIsSurface (C : IsogenyVolcano ℓ) :
    DecidablePred C.isSurface :=
  fun v => inferInstanceAs (Decidable (C.level v = 0))

/-- **Reversing a descending edge gives an ascending edge.** In an $\ell$-isogeny volcano, for
vertices $v$ and $w$, $(v, w)$ is a descending edge if and only if $(w, v)$ is an ascending
edge. -/
theorem descending_iff_ascending_symm (v w : C.V) :
    C.IsDescendingEdge v w ↔ C.IsAscendingEdge w v := by
  simp only [IsDescendingEdge, IsAscendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [← C.graph.symm v w]
    exact hpos
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [C.graph.symm v w]
    exact hpos

/-- **Reversing an ascending edge gives a descending edge.** In an $\ell$-isogeny volcano, for
vertices $v$ and $w$, $(v, w)$ is an ascending edge if and only if $(w, v)$ is a descending
edge. -/
theorem ascending_iff_descending_symm (v w : C.V) :
    C.IsAscendingEdge v w ↔ C.IsDescendingEdge w v := by
  simp only [IsAscendingEdge, IsDescendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [← C.graph.symm v w]
    exact hpos
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [C.graph.symm v w]
    exact hpos

/-- **Every edge of an isogeny volcano is horizontal, descending or ascending.**
Let $C$ be an $\ell$-isogeny volcano, with levels numbered from $0$ at the surface, and let $v, w$
be vertices of $C$ whose edge multiplicity is positive. Then $(v, w)$ is a horizontal edge (both
$v$ and $w$ have level $0$), a descending edge (the level of $w$ is the level of $v$ plus one) or
an ascending edge (the level of $v$ is the level of $w$ plus one). -/
theorem edge_direction (v w : C.V)
    (h : C.graph.edgeMult v w > 0) :
    C.IsHorizontalEdge v w ∨ C.IsDescendingEdge v w ∨
      C.IsAscendingEdge v w := by
  rcases C.edges_between_levels v w h with
    ⟨hv0, hw0⟩ | hdesc | hasc
  · exact Or.inl ⟨h, hv0, hw0⟩
  · exact Or.inr (Or.inr ⟨h, hdesc⟩)
  · exact Or.inr (Or.inl ⟨h, hasc⟩)

/-- **Surface vertices are those of level zero.** A vertex $v$ of an $\ell$-isogeny volcano $C$
lies on the surface of $C$ if and only if the level of $v$, as a natural number, is $0$. -/
@[simp] theorem isSurface_iff (v : C.V) :
    C.isSurface v ↔ (C.level v : ℕ) = 0 := by
  change C.level v = (0 : Fin (C.depth + 1)) ↔ (C.level v : ℕ) = 0
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

/-- **Floor vertices are those whose level equals the depth.** A vertex $v$ of an
$\ell$-isogeny volcano $C$ lies on the floor of $C$ if and only if the level of $v$, as a natural
number, equals the depth of $C$. -/
@[simp] theorem isFloor_iff (v : C.V) :
    C.isFloor v ↔ (C.level v : ℕ) = C.depth := by
  unfold isFloor
  constructor
  · intro h; rw [h]; simp
  · intro h; apply Fin.ext; simpa [Fin.val_last] using h

/-- **Surface regularity of an isogeny volcano.** Let $C$ be an $\ell$-isogeny volcano with edge
multiplicities $m$ and surface degree $s$. For every surface vertex $v$ of $C$, that is, every
vertex of level $0$, the sum of $m(v, w)$ over all surface vertices $w$ of $C$ equals $s$.

This restates the surface-regularity condition of an isogeny volcano in terms of the surface
predicate. -/
@[simp] theorem surface_degreeOn (v : C.V) (hv : C.isSurface v) :
    C.graph.degreeOn v (fun w => C.isSurface w) = C.surfaceDegree := by
  have hv0 : C.level v = ⟨0, Nat.zero_lt_succ _⟩ := by
    exact Fin.ext ((C.isSurface_iff v).mp hv)
  calc
    C.graph.degreeOn v (fun w => C.isSurface w) =
        C.graph.degreeOn v
          (fun w => C.level w = ⟨0, Nat.zero_lt_succ _⟩) := by
      apply C.graph.degreeOn_congr
      intro w _
      constructor
      · intro hw
        exact Fin.ext ((C.isSurface_iff w).mp hw)
      · intro hw
        apply (C.isSurface_iff w).mpr
        exact congrArg Fin.val hw
    _ = C.surfaceDegree := C.surface_regular v hv0

end IsogenyVolcano
