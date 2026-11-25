/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Strongly minimal vertex covers

Hollom and Randall Shaw's graph on the natural numbers refutes Aharoni's conjecture that every
hypergraph with nonempty edges of bounded size has a strongly minimal vertex cover.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted

/-- **Vertex cover of a hypergraph.** Let $E$ be a set of finite subsets of a type $V$, the edges
of a hypergraph. A set $X \subseteq V$ is a (vertex) cover of $E$ if it meets every edge: every
$e \in E$ contains some $v \in X$. -/
def IsVertexCover {V : Type} (E : Set (Finset V)) (X : Set V) : Prop :=
  ∀ e ∈ E, ∃ v ∈ e, v ∈ X

/-- **Strongly minimal cover.** Let $E$ be a set of finite subsets of a type $V$, the edges of a
hypergraph. A set $X \subseteq V$ is a strongly minimal cover of $E$ (Aharoni) if $X$ is a cover of
$E$, that is, it meets every edge in $E$, and $|X \setminus X'| \le |X' \setminus X|$, as cardinals,
for every cover $X'$ of $E$. -/
def IsStronglyMinimalCover {V : Type} (E : Set (Finset V)) (X : Set V) : Prop :=
  IsVertexCover E X ∧ ∀ X', IsVertexCover E X' → Cardinal.mk ↥(X \ X') ≤ Cardinal.mk ↥(X' \ X)

/-- **Aharoni's strongly minimal cover conjecture.** The statement that for every type $V$, every
set $E$ of finite subsets of $V$ (the edges of a hypergraph, possibly infinitely many) and every
natural number $k$ such that each edge in $E$ is nonempty and has at most $k$ elements, the
hypergraph with edge set $E$ has a strongly minimal cover. -/
def boundedEdgesStronglyMinimalCover : Prop :=
  ∀ (V : Type) (E : Set (Finset V)) (k : ℕ), (∀ e ∈ E, e.Nonempty ∧ e.card ≤ k) →
    ∃ X, IsStronglyMinimalCover E X

private def doublingEdges : Set (Finset ℕ) :=
  {e | ∃ u v : ℕ, u < v ∧ 2 * u ≤ v ∧ e = {u, v}}

private theorem cover_doublingEdges_iff (X : Set ℕ) :
    IsVertexCover doublingEdges X ↔ ∀ u v : ℕ, u < v → 2 * u ≤ v → u ∈ X ∨ v ∈ X := by
  constructor
  · intro h u v huv hdouble
    simpa using h {u, v} ⟨u, v, huv, hdouble, rfl⟩
  · rintro h _ ⟨u, v, huv, hdouble, rfl⟩
    simpa using h u v huv hdouble

/-- Beyond twice any missed vertex, every vertex belongs to the cover. -/
private theorem cover_contains_tail {X : Set ℕ} (h : IsVertexCover doublingEdges X) :
    ∃ n : ℕ, ∀ v ≥ n, v ∈ X := by
  by_cases hall : ∀ v, v ∈ X
  · exact ⟨0, fun v _ ↦ hall v⟩
  obtain ⟨u, hu⟩ := not_forall.mp hall
  exact ⟨2 * u + 1, fun v hv ↦
    ((cover_doublingEdges_iff X).mp h u v (by omega) (by omega)).resolve_left hu⟩

/--
**Aharoni's strongly minimal cover conjecture is false.** There are a type $V$, a set $E$ of
finite subsets of $V$ (the edges of a hypergraph) and a natural number $k$ such that every edge in
$E$ is nonempty and has at most $k$ elements, but no strongly minimal cover of $E$ exists. Here a
cover of $E$ is a set $X \subseteq V$ that meets every edge in $E$, and a cover $X$ is strongly
minimal if $|X \setminus X'| \le |X' \setminus X|$, as cardinals, for every cover $X'$ of $E$.

Hollom and Randall Shaw (Section 3.4) show that the graph on $\mathbb{N}$ whose edges are the
pairs $\{u, v\}$ with $2u \le v$ has no strongly minimal vertex cover, so already hypergraphs with
all edges of size $2$ need not have a strongly minimal cover.

Source: Open Problem Garden, Strong
matchings and covers (node 690; R. Aharoni),
http://www.openproblemgarden.org/op/strong_matchings_and_covers; resolution: L. Hollom and B.
Randall Shaw, Counterexamples to conjectures on strong maximality and minimality, Electron. J.
Combin. 33(2) (2026), #P2.11, doi:10.37236/14948; arXiv:2511.13709, Section 3.4 (Strongly minimal
vertex-covers): the graph G on N with edges {u, v} such that 2u ≤ v has no strongly minimal
vertex-cover; the introduction defines strongly minimal vertex-covers by |C \ C'| ≤ |C' \ C| for
every vertex-cover C', https://doi.org/10.37236/14948.
-/
theorem boundedEdgesStronglyMinimalCover_refuted : ¬ boundedEdgesStronglyMinimalCover := by
  intro h
  obtain ⟨X, hX, hmin⟩ := h ℕ doublingEdges 2 (by
    rintro _ ⟨u, v, huv, _, rfl⟩
    simp [Finset.card_pair huv.ne])
  obtain ⟨n, htail⟩ := cover_contains_tail hX
  -- This interval lies in X and has no edge, so its complement is a cover.
  let I := Finset.Ico (n + 1) (2 * (n + 1))
  let Y := (I : Set ℕ)ᶜ
  have hY : IsVertexCover doublingEdges Y := by
    apply (cover_doublingEdges_iff Y).2
    intro u v _ huv
    by_contra! h
    simp [Y, I] at h
    omega
  -- The exchange removes all n + 1 interval vertices and adds at most n missed vertices.
  have hremove : (I : Set ℕ) ⊆ X \ Y := by
    intro v hv
    exact ⟨htail v (Nat.le_of_succ_le (Finset.mem_Ico.mp hv).1), fun h ↦ h hv⟩
  have hadd : Y \ X ⊆ (Finset.range n : Set ℕ) := by
    intro v hv
    exact Finset.mem_range.mpr (lt_of_not_ge fun h ↦ hv.2 (htail v h))
  have hcard := (Cardinal.mk_le_mk_of_subset hremove).trans
    ((hmin Y hY).trans (Cardinal.mk_le_mk_of_subset hadd))
  simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, Finset.card_range, I, Nat.card_Ico,
    Nat.cast_le] at hcard
  omega

end MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted
