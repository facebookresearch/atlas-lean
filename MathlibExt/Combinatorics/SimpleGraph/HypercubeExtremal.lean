/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Set.Card

/-!
# Hypercube Turán extremal number for `Q_n`

Primary source: Marko Pejić, *On the Turán Density of C10 in the Hypercube*,
arXiv:2608.12237v2 (defining text, lines 122-123, with subgraph and `H`-free
conventions at lines 136-140).

Scope: this file defines the `n`-dimensional hypercube `Q_n` as a Mathlib
`SimpleGraph` on `Fin n → Bool` and defines `ex(Q_n, H)` as the maximum edge
count over `H`-free `SimpleGraph.Subgraph`s, including non-spanning ones.
It proves the adjacency characterization, the lower bound into the maximum,
the upper bound by the edges of `Q_n`, attainment under nonemptiness, and the
`Q_0` boundary value. It does not formalize the asymptotic density, existence
of its limit, or the paper's `C_6`/`C_10` bounds.
-/

@[expose]
public section

namespace SimpleGraph

/-- **Hypercube graph.** For a natural number $n$, the $n$-dimensional hypercube $Q_n$ is the
simple graph whose vertices are the functions from $\{0, \dots, n-1\}$ to the Booleans
$\{\mathrm{true}, \mathrm{false}\}$, with an edge between two vertices exactly when they differ
in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => ∃! i, x i ≠ y i)

/-- **Adjacency in the hypercube.** For every natural number $n$ and all vertices $x, y$ of the
$n$-dimensional hypercube $Q_n$ (functions from $\{0, \dots, n-1\}$ to the Booleans), $x$ and
$y$ are adjacent in $Q_n$ if and only if there is exactly one coordinate $i$ with
$x_i \ne y_i$. -/
@[simp]
theorem hypercubeGraph_adj (n : ℕ) (x y : Fin n → Bool) :
    (hypercubeGraph n).Adj x y ↔ ∃! i, x i ≠ y i := by
  unfold hypercubeGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · obtain ⟨i, hi, huniq⟩ := h
      exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩
  · intro h
    have hne : x ≠ y := by
      obtain ⟨i, hi, _⟩ := h
      exact fun heq => hi (congrFun heq i)
    exact ⟨hne, Or.inl h⟩

/-- **No two vertices of the zero-dimensional hypercube are adjacent.** For all vertices $x, y$
of the $0$-dimensional hypercube $Q_0$, $x$ and $y$ are not adjacent in $Q_0$.

Any two vertices agree on all (zero) coordinates. -/
theorem hypercubeGraph_zero_not_adj (x y : Fin 0 → Bool) :
    ¬ (hypercubeGraph 0).Adj x y := by
  rw [hypercubeGraph_adj]
  rintro ⟨i, _, _⟩
  exact Fin.elim0 i

/-- **An edge of the one-dimensional hypercube.** In the $1$-dimensional hypercube $Q_1$, the
constant vertex $\mathrm{true}$ and the constant vertex $\mathrm{false}$ are adjacent. -/
theorem hypercubeGraph_one_adj :
    (hypercubeGraph 1).Adj (fun _ => true) (fun _ => false) := by
  rw [hypercubeGraph_adj]
  exact ⟨0, by simp, fun j _ => Subsingleton.elim j 0⟩

/-- **The zero-dimensional hypercube has no edges.** The edge set of the $0$-dimensional
hypercube $Q_0$ is empty. -/
theorem hypercubeGraph_zero_edgeSet : (hypercubeGraph 0).edgeSet = ∅ := by
  rw [SimpleGraph.edgeSet_eq_empty]
  ext x y
  constructor
  · exact hypercubeGraph_zero_not_adj x y
  · intro h
    simp at h

/-- **Subgraphs of the hypercube have at most as many edges.** For every natural number $n$,
every subgraph of the $n$-dimensional hypercube $Q_n$ has at most as many edges as $Q_n$. -/
theorem hypercubeGraph_subgraph_edgeSet_ncard_le (n : ℕ)
    (S : Subgraph (hypercubeGraph n)) :
    S.edgeSet.ncard ≤ (hypercubeGraph n).edgeSet.ncard :=
  Set.ncard_le_ncard S.edgeSet_subset (Set.toFinite _)

/-- **Hypercube Turán number.** For a natural number $n$ and a simple graph $H$, let $Q_n$ be the
$n$-dimensional hypercube. The hypercube Turán number $\mathrm{ex}(Q_n, H)$ is the largest number
of edges of a subgraph (not necessarily spanning) of $Q_n$ that contains no copy of $H$, that is,
no subgraph isomorphic to $H$; it is $0$ when no such subgraph exists. -/
noncomputable def hypercubeTuranNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ := by
  classical
  exact Finset.sup
    ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m))
    id

/-- **The hypercube Turán number bounds every free subgraph.** For every natural number $n$ and
every simple graph $H$, let $Q_n$ be the $n$-dimensional hypercube and let $\mathrm{ex}(Q_n, H)$
be the hypercube Turán number of $H$ in $Q_n$. If $S$ is a subgraph of $Q_n$ that contains no
copy of $H$, then $S$ has at most $\mathrm{ex}(Q_n, H)$ edges. -/
theorem le_hypercubeTuranNumber (n : ℕ) {W : Type*} {H : SimpleGraph W}
    (S : Subgraph (hypercubeGraph n)) (hfree : H.Free S.coe) :
    S.edgeSet.ncard ≤ hypercubeTuranNumber n H := by
  classical
  unfold hypercubeTuranNumber
  have hmem : S.edgeSet.ncard ∈
      ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
        (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S), S, hfree, rfl⟩
  have h := Finset.le_sup hmem (f := id)
  simpa using h

/-- **Upper bound for the hypercube Turán number.** For every natural number $n$ and every
simple graph $H$, writing $Q_n$ for the $n$-dimensional hypercube, the hypercube Turán number
$\mathrm{ex}(Q_n, H)$ is at most the number of edges of $Q_n$. -/
theorem hypercubeTuranNumber_le_edgeSet_ncard (n : ℕ) {W : Type*} (H : SimpleGraph W) :
    hypercubeTuranNumber n H ≤ (hypercubeGraph n).edgeSet.ncard := by
  classical
  unfold hypercubeTuranNumber
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, _, rfl⟩ := hm
  simpa using hypercubeGraph_subgraph_edgeSet_ncard_le n S

/-- **Attainment of the hypercube Turán number.** Let $n$ be a natural number, $H$ a simple
graph, $Q_n$ the $n$-dimensional hypercube, and $\mathrm{ex}(Q_n, H)$ the hypercube Turán number.
If $Q_n$ has at least one subgraph (not necessarily spanning) that contains no copy of $H$, then
some subgraph $S$ of $Q_n$ contains no copy of $H$ and has exactly $\mathrm{ex}(Q_n, H)$ edges. -/
theorem exists_attains_hypercubeTuranNumber (n : ℕ) {W : Type*} {H : SimpleGraph W}
    (hne : ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe) :
    ∃ S : Subgraph (hypercubeGraph n),
      H.Free S.coe ∧ S.edgeSet.ncard = hypercubeTuranNumber n H := by
  classical
  obtain ⟨S₀, hfree₀⟩ := hne
  have hmem₀ : S₀.edgeSet.ncard ∈
      ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
        (fun m => ∃ S : Subgraph (hypercubeGraph n),
          H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S₀), S₀, hfree₀, rfl⟩
  have hne' : (((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n),
        H.Free S.coe ∧ S.edgeSet.ncard = m)) : Finset ℕ).Nonempty :=
    ⟨_, hmem₀⟩
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup _ hne' (id : ℕ → ℕ)
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, hfree, rfl⟩ := hm
  exact ⟨S, hfree, hsup.symm⟩

/-- **The hypercube Turán number in dimension zero.** For every simple graph $H$, writing $Q_0$
for the $0$-dimensional hypercube, the hypercube Turán number $\mathrm{ex}(Q_0, H)$ is $0$. -/
theorem hypercubeTuranNumber_zero {W : Type*} (H : SimpleGraph W) :
    hypercubeTuranNumber 0 H = 0 := by
  have h := hypercubeTuranNumber_le_edgeSet_ncard 0 H
  rw [hypercubeGraph_zero_edgeSet, Set.ncard_empty] at h
  exact Nat.le_zero.mp h

end SimpleGraph
