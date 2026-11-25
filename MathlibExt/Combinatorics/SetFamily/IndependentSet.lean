/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph

@[expose] public section

/-!
# Independent sets and Steiner triple systems in finite hypergraphs

Shared set-family API: a vertex set is independent when no hyperedge is
fully contained in it, and a Steiner triple system is a 3-uniform family
in which every pair of distinct vertices lies in a unique edge.
-/

namespace SetFamily

variable {V : Type*}

/-- **Independent set in a hypergraph.** Let $H$ be a finite hypergraph, that is a finite
family of finite sets of vertices, called its edges. A finite set $I$ of vertices is
independent in $H$ when no edge $e$ of $H$ satisfies $e \subseteq I$. -/
def IsIndependent (H : Finset (Finset V)) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- **Independence unfolded.** A finite set $I$ of vertices is independent in a finite
hypergraph $H$ if and only if no edge $e$ of $H$ satisfies $e \subseteq I$. -/
theorem isIndependent_iff (H : Finset (Finset V)) (I : Finset V) :
    IsIndependent H I ↔ ∀ e ∈ H, ¬ e ⊆ I :=
  Iff.rfl

/-- **Every set is independent in the empty hypergraph.** Every finite set of vertices is
independent in the empty hypergraph, the hypergraph with no edges. -/
theorem isIndependent_empty_hypergraph (I : Finset V) :
    IsIndependent (∅ : Finset (Finset V)) I := by
  simp [IsIndependent]

/-- **Subsets of independent sets are independent.** If a finite set $I$ of vertices is
independent in a finite hypergraph $H$ and $J \subseteq I$, then $J$ is independent in $H$. -/
theorem isIndependent_of_subset {H : Finset (Finset V)} {I J : Finset V}
    (h : IsIndependent H I) (hJI : J ⊆ I) : IsIndependent H J := by
  intro e he hsub
  exact h e he (hsub.trans hJI)

/-- **When the empty set is independent.** For a finite hypergraph $H$, the empty set is
independent in $H$ if and only if every edge of $H$ is nonempty. -/
theorem isIndependent_empty_iff (H : Finset (Finset V)) :
    IsIndependent H ∅ ↔ ∀ e ∈ H, e.Nonempty := by
  simp [IsIndependent, Finset.subset_empty, Finset.nonempty_iff_ne_empty]

/-- **Steiner triple system.** A finite hypergraph $H$ on a vertex type $V$, that is a finite
family of finite subsets of $V$, is a Steiner triple system when it is $3$-uniform (every
edge of $H$ has exactly $3$ elements) and any two distinct vertices $u \ne v$ of $V$ lie
together in exactly one edge of $H$. -/
def IsSteinerTripleSystem (H : Finset (Finset V)) : Prop :=
  IsUniform H 3 ∧
    ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e

/-- **Steiner triple systems are 3-uniform.** If $H$ is a Steiner triple system, then $H$ is
$3$-uniform: every edge of $H$ has exactly $3$ elements. -/
theorem uniform_of_isSteinerTripleSystem {H : Finset (Finset V)}
    (h : IsSteinerTripleSystem H) : IsUniform H 3 :=
  h.1

/-- **Pairs in a Steiner triple system.** If $H$ is a Steiner triple system on a vertex type
$V$, then for all vertices $u \ne v$ of $V$ there is exactly one edge $e$ of $H$ with
$u \in e$ and $v \in e$. -/
theorem pairCover_of_isSteinerTripleSystem {H : Finset (Finset V)}
    (h : IsSteinerTripleSystem H) :
    ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e :=
  h.2

/-- **Unique element of a singleton family.** Let $t$ be a finite set of vertices and let
$P$ be a property of finite sets of vertices. If $t$ satisfies $P$, then there is exactly
one finite set $e$ of vertices with $e \in \{t\}$ and $P(e)$. -/
theorem existsUnique_mem_singleton {t : Finset V} {P : Finset V → Prop}
    (hP : P t) : ∃! e : Finset V, e ∈ ({t} : Finset (Finset V)) ∧ P e :=
  ⟨t, ⟨Finset.mem_singleton_self t, hP⟩,
    fun _e he => Finset.mem_singleton.mp he.1⟩

end SetFamily
