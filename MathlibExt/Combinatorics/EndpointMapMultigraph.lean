/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Finite edge-identity multigraphs

This file supplies small reusable definitions for finite undirected multigraphs represented by
an edge type and two endpoint maps. Distinct edge values retain parallel-edge identity. Degrees
count endpoint incidences, so a loop contributes two, while `incident` contains a loop only once.
-/

namespace EndpointMapMultigraph

/-- **Edges incident to a vertex.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed
as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. For a vertex $v \in V$ and a finite set $F \subseteq E$, the edges of
$F$ incident to $v$ form the finite set of all $e \in F$ with $\mathrm{end}_1(e) = v$ or
$\mathrm{end}_2(e) = v$. An edge appears once even when it is a loop. -/
noncomputable def incident {V E : Type*} (end₁ end₂ : E → V)
    (v : V) (F : Finset E) : Finset E := by
  classical
  exact F.filter (fun e => end₁ e = v ∨ end₂ e = v)

/-- **Degree within an edge set.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed
as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. For a finite set $F \subseteq E$ and a vertex $v \in V$, the degree of
$v$ in $F$ is the number of $e \in F$ with $\mathrm{end}_1(e) = v$ plus the number of $e \in F$
with $\mathrm{end}_2(e) = v$. Each endpoint incidence counts once, so a loop at $v$ contributes
two. -/
noncomputable def degreeWithin {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (v : V) : ℕ := by
  classical
  exact (F.filter (fun e => end₁ e = v)).card + (F.filter (fun e => end₂ e = v)).card

/-- **Support of an edge set.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed as
an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. The support of a finite set $F \subseteq E$ is the set of vertices
$v \in V$ such that $\mathrm{end}_1(e) = v$ or $\mathrm{end}_2(e) = v$ for some $e \in F$. -/
noncomputable def support {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Set V := by
  classical
  exact {v | ∃ e ∈ F, end₁ e = v ∨ end₂ e = v}

/-- **Adjacency through an edge set.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps,
viewed as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints
$\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$. For a finite set $F \subseteq E$, vertices
$u, v \in V$ are adjacent using $F$ when some $e \in F$ has $\mathrm{end}_1(e) = u$ and
$\mathrm{end}_2(e) = v$, or $\mathrm{end}_1(e) = v$ and $\mathrm{end}_2(e) = u$. -/
noncomputable def AdjacentUsing {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (u v : V) : Prop := by
  classical
  exact ∃ e ∈ F, (end₁ e = u ∧ end₂ e = v) ∨ (end₁ e = v ∧ end₂ e = u)

/-- **Edge sets connected on their support.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be
maps, viewed as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints
$\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$. A finite set $F \subseteq E$ is connected on its
support when for all vertices $u$ and $v$ in the support of $F$ there are vertices
$u = w_0, w_1, \dots, w_k = v$, with $k \ge 0$, such that $w_{i-1}$ and $w_i$ are adjacent
using $F$ for each $1 \le i \le k$. -/
noncomputable def IsConnectedOnSupport {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Prop :=
  ∀ u ∈ support end₁ end₂ F, ∀ v ∈ support end₁ end₂ F,
    Relation.ReflTransGen (AdjacentUsing end₁ end₂ F) u v

/-- **Circuits in an edge set.** Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed
as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. A finite set $F \subseteq E$ is a circuit when $F$ is nonempty, $F$ is
connected on its support, and every vertex in the support of $F$ has degree exactly $2$ in $F$,
where degree counts endpoint incidences, so that a loop contributes two.

This includes a loop as a $1$-circuit and two parallel edges between distinct vertices as a
$2$-circuit. -/
noncomputable def IsCircuit {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Prop :=
  F.Nonempty ∧ IsConnectedOnSupport end₁ end₂ F ∧
    ∀ v ∈ support end₁ end₂ F, degreeWithin end₁ end₂ F v = 2

/-- **Cut of a vertex set.** Let $E$ be a finite set and $\mathrm{end}_1, \mathrm{end}_2 : E \to V$
be maps, viewed as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints
$\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$. For a finite set $X \subseteq V$, the cut of $X$ is
the set of edges $e \in E$ such that exactly one of $\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$
lies in $X$. Loops never cross a cut. -/
noncomputable def cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => decide (end₁ e ∈ X) != decide (end₂ e ∈ X))

@[simp] theorem mem_incident {V E : Type*} (end₁ end₂ : E → V) (v : V)
    (F : Finset E) (e : E) :
    e ∈ incident end₁ end₂ v F ↔ e ∈ F ∧ (end₁ e = v ∨ end₂ e = v) := by
  classical
  simp [incident]

theorem incident_swap {V E : Type*} (end₁ end₂ : E → V) (v : V) (F : Finset E) :
    incident end₂ end₁ v F = incident end₁ end₂ v F := by
  classical
  ext e
  simp [or_comm]

theorem degreeWithin_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) (v : V) :
    degreeWithin end₂ end₁ F v = degreeWithin end₁ end₂ F v := by
  classical
  simp [degreeWithin, Nat.add_comm]

@[simp] theorem mem_support {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) (v : V) :
    v ∈ support end₁ end₂ F ↔ ∃ e ∈ F, end₁ e = v ∨ end₂ e = v := by
  classical
  simp [support]

theorem support_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    support end₂ end₁ F = support end₁ end₂ F := by
  ext v
  simp [or_comm]

theorem adjacentUsing_symm {V E : Type*} (end₁ end₂ : E → V) (F : Finset E)
    {u v : V} : AdjacentUsing end₁ end₂ F u v ↔ AdjacentUsing end₁ end₂ F v u := by
  classical
  simp [AdjacentUsing, and_comm, or_comm]

theorem adjacentUsing_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E)
    (u v : V) : AdjacentUsing end₂ end₁ F u v ↔ AdjacentUsing end₁ end₂ F u v := by
  classical
  simp [AdjacentUsing, and_comm, or_comm]

theorem isConnectedOnSupport_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    IsConnectedOnSupport end₂ end₁ F ↔ IsConnectedOnSupport end₁ end₂ F := by
  have hadj : AdjacentUsing end₂ end₁ F = AdjacentUsing end₁ end₂ F := by
    funext u v
    exact propext (adjacentUsing_swap end₁ end₂ F u v)
  rw [IsConnectedOnSupport, IsConnectedOnSupport, support_swap, hadj]

theorem isCircuit_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    IsCircuit end₂ end₁ F ↔ IsCircuit end₁ end₂ F := by
  simp only [IsCircuit, support_swap, degreeWithin_swap, isConnectedOnSupport_swap]

/-- **Degree counts incident edges in a loopless edge set.** Let
$\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed as an undirected multigraph on $V$ in
which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$. Let
$F \subseteq E$ be a finite set of edges with no loops, that is,
$\mathrm{end}_1(e) \ne \mathrm{end}_2(e)$ for every $e \in F$. Then for every vertex $v \in V$,
the degree of $v$ in $F$ equals the number of edges of $F$ incident to $v$. -/
theorem degreeWithin_eq_card_incident_of_loopless {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (v : V) (h : ∀ e ∈ F, end₁ e ≠ end₂ e) :
    degreeWithin end₁ end₂ F v = (incident end₁ end₂ v F).card := by
  classical
  let F₁ := F.filter (fun e => end₁ e = v)
  let F₂ := F.filter (fun e => end₂ e = v)
  have hdisjoint : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [F₁, F₂, Finset.mem_filter] at he₁ he₂
    exact h e he₁.1 (he₁.2.trans he₂.2.symm)
  have hunion : F₁ ∪ F₂ = incident end₁ end₂ v F := by
    ext e
    simp only [F₁, F₂, incident, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [degreeWithin]
  change F₁.card + F₂.card = _
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion]

@[simp] theorem mem_cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) (e : E) :
    e ∈ cut end₁ end₂ X ↔ (end₁ e ∈ X) ≠ (end₂ e ∈ X) := by
  classical
  simp [cut]

theorem cut_swap {V E : Type*} [Fintype E] (end₁ end₂ : E → V) (X : Finset V) :
    cut end₂ end₁ X = cut end₁ end₂ X := by
  ext e
  simp only [mem_cut]
  exact ne_comm

theorem degreeWithin_singleton_loop {V E : Type*} (end₁ end₂ : E → V) (e : E)
    (h : end₁ e = end₂ e) : degreeWithin end₁ end₂ {e} (end₁ e) = 2 := by
  classical
  rw [degreeWithin, Finset.filter_singleton, Finset.filter_singleton]
  simp [h.symm]

theorem loop_not_mem_cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) (e : E) (h : end₁ e = end₂ e) : e ∉ cut end₁ end₂ X := by
  classical
  simp [h]

@[simp] theorem isConnectedOnSupport_empty {V E : Type*} (end₁ end₂ : E → V) :
    IsConnectedOnSupport end₁ end₂ (∅ : Finset E) := by
  simp [IsConnectedOnSupport]

@[simp] theorem not_isCircuit_empty {V E : Type*} (end₁ end₂ : E → V) :
    ¬IsCircuit end₁ end₂ (∅ : Finset E) := by
  simp [IsCircuit]

end EndpointMapMultigraph
