/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card

/-!
# Degenerate graphs

A finite graph is `k`-degenerate on a vertex set when every nonempty subset contains a
vertex with at most `k` neighbors in that subset. The unrestricted version takes the
vertex set to be universal.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {U T : Set V} {k l : ℕ}

/-- **Degeneracy on a vertex set.** Let $G$ be a simple graph on a finite vertex type $V$, let
$U \subseteq V$ and let $k$ be a natural number. Then $G$ is $k$-degenerate on $U$ if every
nonempty subset $W \subseteq U$ contains a vertex $v$ with at most $k$ neighbors in $W$. -/
def IsDegenerateOn {V : Type*} [Finite V] (G : SimpleGraph V) (U : Set V) (k : ℕ) : Prop :=
  ∀ W : Set V, W.Nonempty → W ⊆ U →
    ∃ v ∈ W, (G.neighborSet v ∩ W).ncard ≤ k

/-- **Degenerate graph.** A simple graph $G$ on a finite vertex type $V$ is $k$-degenerate, for a
natural number $k$, if it is $k$-degenerate on the full vertex set $V$: every nonempty set $W$ of
vertices contains a vertex with at most $k$ neighbors in $W$. -/
def IsDegenerate {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsDegenerateOn Set.univ k

/-- **Degeneracy on a vertex set is monotone in the degree bound.** Let $G$ be a simple graph on
a finite vertex type $V$, let $U \subseteq V$, and let $k \le l$ be natural numbers. If $G$ is
$k$-degenerate on $U$, then $G$ is $l$-degenerate on $U$. -/
theorem IsDegenerateOn.mono [Finite V] (h : G.IsDegenerateOn U k) (hkl : k ≤ l) :
    G.IsDegenerateOn U l := by
  intro W hWne hWU
  obtain ⟨v, hvW, hv⟩ := h W hWne hWU
  exact ⟨v, hvW, hv.trans hkl⟩

/-- **Degeneracy on a vertex set passes to subsets.** Let $G$ be a simple graph on a finite
vertex type $V$, let $T \subseteq U \subseteq V$ and let $k$ be a natural number. If $G$ is
$k$-degenerate on $U$, then $G$ is $k$-degenerate on $T$. -/
theorem IsDegenerateOn.of_subset [Finite V] (h : G.IsDegenerateOn U k) (hTU : T ⊆ U) :
    G.IsDegenerateOn T k := by
  intro W hWne hWT
  exact h W hWne (hWT.trans hTU)

/-- **A degenerate graph is degenerate on every vertex set.** Let $G$ be a simple graph on a
finite vertex type $V$ and let $k$ be a natural number. If $G$ is $k$-degenerate, then $G$ is
$k$-degenerate on every subset $U \subseteq V$. -/
theorem IsDegenerate.isDegenerateOn [Finite V] (h : G.IsDegenerate k) (U : Set V) :
    G.IsDegenerateOn U k :=
  h.of_subset (Set.subset_univ U)

end SimpleGraph

end
