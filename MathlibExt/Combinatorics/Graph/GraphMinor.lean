/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite graphs and the graph-minor relation
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt

/-- **Finite simple graph.** A finite graph consists of a finite vertex set $V$ together with a
simple graph on $V$, that is, a symmetric and irreflexive adjacency relation on $V$.

Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
structure FinGraph where
  V : Type*
  [fin : Finite V]
  G : SimpleGraph V

/-! ## Complete graphs as `FinGraph`s -/

/-- **Complete graph as a finite graph.** For a natural number $n$, $K_n$ is the finite graph whose
vertices are the natural numbers less than $n$, in which any two distinct vertices are adjacent. -/
abbrev cliqueFinGraph (n : ℕ) : FinGraph where
  V := Fin n
  G := SimpleGraph.completeGraph (Fin n)

/-- **Adjacency in the complete graph.** For every natural number $n$ and all vertices $x$ and $y$
of the complete graph $K_n$, whose vertices are the natural numbers less than $n$, $x$ and $y$ are
adjacent if and only if $x \ne y$. -/
theorem cliqueFinGraph_adj {n : ℕ} {x y : Fin n} :
    (cliqueFinGraph n).G.Adj x y ↔ x ≠ y := by
  show (SimpleGraph.completeGraph (Fin n)).Adj x y ↔ x ≠ y
  rw [SimpleGraph.completeGraph_eq_top]
  exact SimpleGraph.top_adj _ _

/-- **One-step graph minor.** For finite graphs $H$ and $G$, $H$ arises from $G$ by one minor step
when one of the following holds. Isomorphism: $H$ is isomorphic to $G$. Vertex deletion: for some
vertex $a$ of $G$ there is an injective map $f$ from the vertices of $H$ to the vertices of $G$
whose image consists of all vertices other than $a$, such that vertices $u, v$ of $H$ are adjacent
exactly when $f(u), f(v)$ are adjacent in $G$. Edge deletion: for some edge $xy$ of $G$ there is a
bijection $e$ from the vertices of $H$ to the vertices of $G$ such that, for all vertices $u, v$ of
$H$, the vertices $e(u), e(v)$ are adjacent in $G$ whenever $u, v$ are adjacent in $H$, and if
$e(u), e(v)$ are adjacent in $G$, then either $u, v$ are adjacent in $H$ or the pair $(e(u), e(v))$
is $(x, y)$ or $(y, x)$; moreover, $e^{-1}(x), e^{-1}(y)$ are not adjacent in $H$. Edge
contraction: for some edge $ab$ of $G$ there is a surjective map $f$ from the vertices of $G$ to
the vertices of $H$ with $f(a) = f(b)$ such that, for all vertices $x, y$ of $G$, $f(x) = f(y)$
implies $x = y$ or $(x, y)$ is $(a, b)$ or $(b, a)$, and vertices $u, v$ of $H$ are adjacent
exactly when $u \ne v$ and there are adjacent vertices $u', v'$ of $G$ with $f(u') = u$ and
$f(v') = v$.

Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
inductive MinorStep : FinGraph → FinGraph → Prop where
  | iso (H G : FinGraph) (e : H.G ≃g G.G) : MinorStep H G
  | deleteVertex (H G : FinGraph) (f : H.V ↪ G.V)
      (h_induced : ∀ u v, H.G.Adj u v ↔ G.G.Adj (f u) (f v))
      (a : G.V) (h_missing : ∀ x, (∃ y, f y = x) ↔ x ≠ a) : MinorStep H G
  | deleteEdge (H G : FinGraph) (e : H.V ≃ G.V)
      (h_sub : ∀ u v, H.G.Adj u v → G.G.Adj (e u) (e v))
      (x y : G.V) (h_edge : G.G.Adj x y)
      (h_miss : ¬H.G.Adj (e.symm x) (e.symm y))
      (h_only : ∀ u v, G.G.Adj (e u) (e v) →
        H.G.Adj u v ∨ (e u = x ∧ e v = y) ∨ (e u = y ∧ e v = x)) :
      MinorStep H G
  | contractEdge (H G : FinGraph) (f : G.V → H.V)
      (hsurj : Function.Surjective f)
      (a b : G.V) (h_adj : G.G.Adj a b) (h_ne : a ≠ b)
      (h_collapse : f a = f b)
      (h_single : ∀ x y, f x = f y →
        x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
      (h_adj_iff : ∀ u v, H.G.Adj u v ↔
        u ≠ v ∧ ∃ u' v', f u' = u ∧ f v' = v ∧ G.G.Adj u' v') :
      MinorStep H G

/-- **Graph minor relation.** For finite graphs $H$ and $G$, $H$ is a minor of $G$ when there is a
finite sequence $H = G_0, G_1, \dots, G_k = G$ of finite graphs, with $k \ge 0$, such that for
each $i < k$, $G_i$ arises from $G_{i+1}$ by one minor step: an isomorphism, the deletion of one
vertex, the deletion of one edge, or the contraction of one edge.

Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
def IsMinor (H G : FinGraph) : Prop :=
  Relation.ReflTransGen MinorStep H G

/-- **Reflexivity of the graph minor relation.** Every finite graph $G$ is a minor of itself. -/
theorem IsMinor.refl (G : FinGraph) : IsMinor G G :=
  Relation.ReflTransGen.refl

/-- **Transitivity of the graph minor relation.** For finite graphs $H$, $K$ and $G$, if $H$ is a
minor of $K$ and $K$ is a minor of $G$, then $H$ is a minor of $G$. -/
theorem IsMinor.trans {H K G : FinGraph} :
    IsMinor H K → IsMinor K G → IsMinor H G :=
  Relation.ReflTransGen.trans

/-- **A single minor step gives a minor.** For finite graphs $H$ and $G$, if $H$ arises from $G$ by
one minor step, then $H$ is a minor of $G$. -/
theorem IsMinor.of_step {H G : FinGraph} (h : MinorStep H G) : IsMinor H G :=
  Relation.ReflTransGen.single h

/-- **An isomorphic copy is a minor.** For finite graphs $H$ and $G$, if $H$ is isomorphic to $G$,
then $H$ is a minor of $G$. -/
theorem IsMinor.of_iso {H G : FinGraph} (e : H.G ≃g G.G) : IsMinor H G :=
  IsMinor.of_step (MinorStep.iso H G e)

end MetaMathlibExt
