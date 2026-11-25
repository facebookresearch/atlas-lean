/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Centered vertex colorings

Following Jędrzej Hodor and Piotr Micek, "Superlinear Separation Between Linear
and Centered Colorings" (https://arxiv.org/abs/2608.18620v1):

* main.tex lines 94–95 define a `φ`-center of a subgraph (a vertex whose color
  appears exactly once in that subgraph) and a centered coloring (every
  connected subgraph has a `φ`-center).
* main.tex lines 123–124 fix the conventions that all graphs are finite,
  simple, and undirected, and that connected graphs and paths are nonnull.

The paper works with finite graphs. Finiteness is not logically needed for the
reusable predicates and theorems here: whether a color occurs exactly once
depends only on the vertex set together with the coloring, and quantifying over
vertex sets whose induce is connected is faithful because adding all induced
edges on the same vertices keeps a connected subgraph connected. Hence
`IsPhiCenter` and `IsCentered` below generalize to arbitrary vertex types with
no `Fintype` assumption. Colorings use Mathlib's `SimpleGraph.Coloring`, which
is a proper vertex coloring.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}
variable {G : SimpleGraph V} {C : Type*}

/-- **Center of a vertex set under a coloring.** Let $\varphi$ be a proper vertex coloring of a
simple graph $G$, let $s$ be a set of vertices of $G$ and let $v$ be a vertex of $G$. Then $v$ is
a $\varphi$-center of $s$ if $v \in s$ and no other vertex of $s$ has the color $\varphi(v)$. -/
def IsPhiCenter (φ : G.Coloring C) (s : Set V) (v : V) : Prop :=
  v ∈ s ∧ ∀ w ∈ s, φ w = φ v → w = v

/-- **Centered coloring.** A proper vertex coloring $\varphi$ of a simple graph $G$ is centered
if, for every set $s$ of vertices of $G$ whose induced subgraph is connected, some vertex is a
$\varphi$-center of $s$.

Quantifying over vertex sets whose induced subgraph is connected suffices: adding all induced
edges on the same vertices keeps a connected subgraph connected, and whether a color occurs
exactly once depends only on the vertex set together with the coloring. -/
def IsCentered (φ : G.Coloring C) : Prop :=
  ∀ s : Set V, (G.induce s).Connected → ∃ v, IsPhiCenter φ s v

/-- **Centers via unique existence.** Let $\varphi$ be a proper vertex coloring of a simple graph
$G$, let $s$ be a set of vertices of $G$ and let $v$ be a vertex of $G$. Then $v$ is a
$\varphi$-center of $s$ if and only if $v \in s$ and there is exactly one vertex $u \in s$ with
$\varphi(u) = \varphi(v)$. -/
theorem isPhiCenter_iff_existsUnique (φ : G.Coloring C) (s : Set V) (v : V) :
    IsPhiCenter φ s v ↔ v ∈ s ∧ ∃! u, u ∈ s ∧ φ u = φ v := by
  constructor
  · rintro ⟨hmem, huniq⟩
    refine ⟨hmem, v, ⟨hmem, rfl⟩, ?_⟩
    rintro w ⟨hwmem, hweq⟩
    exact huniq w hwmem hweq
  · rintro ⟨hmem, u₀, ⟨_, _⟩, huniq⟩
    refine ⟨hmem, fun w hwmem hweq => ?_⟩
    have hw : w = u₀ := huniq w ⟨hwmem, hweq⟩
    have hv : v = u₀ := huniq v ⟨hmem, rfl⟩
    exact hw.trans hv.symm

/-- **A vertex is a center of its singleton.** For every proper vertex coloring $\varphi$ of a
simple graph $G$ and every vertex $v$ of $G$, $v$ is a $\varphi$-center of $\{v\}$. -/
theorem isPhiCenter_singleton (φ : G.Coloring C) (v : V) :
    IsPhiCenter φ {v} v :=
  ⟨Set.mem_singleton v, fun _ hw _ => Set.mem_singleton_iff.mp hw⟩

/-- **Injective colorings are centered.** Every injective proper vertex coloring of a simple graph
is centered: any vertex of a set whose induced subgraph is connected is a center of that set. -/
theorem isCentered_of_injective (φ : G.Coloring C)
    (hinj : Function.Injective ⇑φ) : IsCentered φ := by
  intro s hs
  have hne : s.Nonempty := Set.nonempty_coe_sort.mp hs.nonempty
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv, fun w _ heq => hinj heq⟩

/-- **The identity coloring is centered.** For every simple graph $G$ with vertex set $V$, the
proper vertex coloring of $G$ by $V$ that gives each vertex itself as its color is centered. -/
theorem selfColoring_isCentered (G : SimpleGraph V) :
    IsCentered (SimpleGraph.selfColoring G) :=
  isCentered_of_injective (SimpleGraph.selfColoring G) fun _ _ h => h

end SimpleGraph

end
