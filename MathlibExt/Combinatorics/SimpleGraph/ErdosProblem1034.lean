/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/1034.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definitions `JoinedToTwo`, `conjecture`, `disprovedForm`,
`bookLowerBound`, `maTangUpperBound` and `k4FreeUpperBound`, and the statement of
`conjecture_refuted`.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# The Erdős–Faudree triangle conjecture is false

Erdős and Faudree conjectured (Erdős Problem 1034) that every graph on `n` vertices with more
than `n² / 4` edges contains a triangle `T` and `(1 / 2 - o(1)) n` vertices, each adjacent to
two vertices of `T`. This file proves `conjecture_refuted`: the conjecture is false.

The counterexample here is elementary; its constant is weaker than that of Ma and Tang, recorded
in the docstring of `conjecture_refuted`, but suffices. `CliqueJoin.graph p k q` joins an
independent set of `p` vertices to every vertex of `k` disjoint cliques of `q` vertices each. A
triangle has at most one vertex in the independent set and its other vertices lie in a single
clique; every vertex adjacent to two vertices of the triangle lies in the independent set or in
that clique (`CliqueJoin.card_le_of_joinedToTwo`). For `p = 8 s`, `k = 5` and `q = 3 s` the graph
has `n = 23 s` vertices and `(285 s² - 15 s) / 2 > n² / 4` edges, but at most
`11 s = (1 / 2 - 1 / 46) n` vertices are adjacent to two vertices of any triangle.

## Main declarations

* `JoinedToTwo`, `conjecture`: the conjecture of Erdős and Faudree.
* `CliqueJoin.graph`: the counterexample graphs.
* `CliqueJoin.two_mul_card_edgeFinset`: twice the number of edges of `CliqueJoin.graph p k q`.
* `CliqueJoin.card_le_of_joinedToTwo`: the bound on the vertices adjacent to two vertices of a
  triangle.
* `conjecture_refuted`: the conjecture is false.
-/

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem1034Wanted

/-! Source record `FC-ErdosProblem1034`, ported from FormalConjectures
`ErdosProblems/1034.lean` (`def JoinedToTwo`, `theorem erdos_1034`,
`lower_bound`, `upper_bound`, `k4_free`) and checked against
erdosproblems.com/1034. A conjecture of Erdős and Faudree (stronger than
[905]). Status: resolved false (Ma–Tang; formalized in Lean). The
historical positive claim is preserved as `conjecture` (disproved); its
negation is the unregistered companion `disprovedForm`. The book lower
bound and the Ma–Tang and K₄-free upper bounds are unregistered
established companions. -/

/-- **Vertices joined to two vertices of a set.** Let $G$ be a simple graph on a vertex type $V$
and let $T$ and $Y$ be finite sets of vertices. The set $Y$ is joined to two vertices of $T$ in
$G$ if every vertex $y \in Y$ is adjacent in $G$ to two distinct vertices $u, v \in T$. -/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

/-- **Erdős–Faudree triangle conjecture.** For every real $\varepsilon > 0$ the following holds
for all sufficiently large $n$: every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ with
more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of vertices, each adjacent in $G$
to two distinct vertices of $T$, with $|Y| > (1/2 - \varepsilon)n$.

This claim (Erdős Problem 1034) was disproved by Ma and Tang. -/
def conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
        JoinedToTwo G T Y ∧ (1 / 2 - ε) * (n : ℝ) < (Y.card : ℝ)

/-- **Negation of the Erdős–Faudree triangle conjecture.** The proposition that the
Erdős–Faudree triangle conjecture fails, that is, that it is not the case that for every real
$\varepsilon > 0$ and all sufficiently large $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of
vertices, each adjacent in $G$ to two distinct vertices of $T$, with $|Y| > (1/2 - \varepsilon)n$.
-/
def disprovedForm : Prop := ¬ conjecture

/-- **Book lower bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the following
holds for all sufficiently large $n$: every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of
vertices, each adjacent in $G$ to two distinct vertices of $T$, with
$|Y| \ge (1/6 - \varepsilon)n$. -/
def bookLowerBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

/-- **Ma–Tang upper bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the following
holds for all sufficiently large $n$: there is a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges such that for every triangle $T$ of $G$, every
set $Y$ of vertices each adjacent in $G$ to two distinct vertices of $T$ satisfies
$|Y| \le (2 - \sqrt{5/2} + \varepsilon)n$. -/
def maTangUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ)

/-- **$K_4$-free upper bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the
following holds for all sufficiently large $n$: there is a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ that contains no $K_4$ and has more than $n^2/4$ edges, such that for every
triangle $T$ of $G$, every set $Y$ of vertices each adjacent in $G$ to two distinct vertices of
$T$ satisfies $|Y| \le (2\sqrt{3} - 3 + \varepsilon)n$. -/
def k4FreeUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 * Real.sqrt 3 - 3 + ε) * (n : ℝ)

/-! ### The counterexample graphs -/

namespace CliqueJoin

variable {p k q : ℕ}

/-- The adjacency relation of `CliqueJoin.graph p k q`: a vertex `Sum.inl a` of the independent
set is adjacent to every vertex `Sum.inr x` of the cliques, and two clique vertices are adjacent
when they are distinct and lie in the same clique. -/
def Adj : Fin p ⊕ (Fin k × Fin q) → Fin p ⊕ (Fin k × Fin q) → Prop
  | .inl _, .inl _ => False
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr x, .inr y => x.1 = y.1 ∧ x ≠ y

instance instDecidableRelAdj : DecidableRel (Adj (p := p) (k := k) (q := q))
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inl _, .inr _ => inferInstanceAs (Decidable True)
  | .inr _, .inl _ => inferInstanceAs (Decidable True)
  | .inr x, .inr y => inferInstanceAs (Decidable (x.1 = y.1 ∧ x ≠ y))

/-- The join of an independent set of `p` vertices `Sum.inl a` with `k` disjoint cliques of `q`
vertices each: the vertex `Sum.inr (i, b)` is the `b`-th vertex of the `i`-th clique. -/
def graph (p k q : ℕ) : SimpleGraph (Fin p ⊕ (Fin k × Fin q)) where
  Adj := Adj
  symm.symm := by
    rintro (a | x) (b | y) h <;> simp_all [Adj, eq_comm]
  loopless.irrefl := by
    rintro (a | x) h <;> simp_all [Adj]

instance instDecidableRelGraphAdj (p k q : ℕ) : DecidableRel (graph p k q).Adj :=
  instDecidableRelAdj

@[simp]
theorem graph_adj_inl_inl (a b : Fin p) : ¬ (graph p k q).Adj (.inl a) (.inl b) := id

@[simp]
theorem graph_adj_inl_inr (a : Fin p) (x : Fin k × Fin q) : (graph p k q).Adj (.inl a) (.inr x) :=
  trivial

@[simp]
theorem graph_adj_inr_inl (x : Fin k × Fin q) (a : Fin p) : (graph p k q).Adj (.inr x) (.inl a) :=
  trivial

@[simp]
theorem graph_adj_inr_inr (x y : Fin k × Fin q) :
    (graph p k q).Adj (.inr x) (.inr y) ↔ x.1 = y.1 ∧ x ≠ y :=
  Iff.rfl

/-- In the join of $p$ independent vertices with $k$ disjoint cliques of size $q$, each
independent vertex has degree $kq$, the total number of clique vertices. -/
theorem degree_inl (a : Fin p) : (graph p k q).degree (.inl a) = k * q := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter, Fintype.sum_sum_type]
  simp

/-- In the join of $p$ independent vertices with $k$ disjoint cliques of size $q$, a clique
vertex has degree $p+(q-1)$. Its neighbors are the independent vertices and the other
vertices of its clique. -/
theorem degree_inr (x : Fin k × Fin q) : (graph p k q).degree (.inr x) = p + (q - 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter, Fintype.sum_sum_type]
  obtain ⟨i, b⟩ := x
  simp only [Fintype.sum_prod_type]
  simp [Prod.ext_iff, ite_and, Finset.filter_ne, Finset.card_erase_of_mem]

/-- For natural numbers $p,k,q$, let $G$ be the join of an independent set of $p$ vertices with
$k$ disjoint cliques of size $q$. Summing the degrees in these two parts gives
$2|E(G)| = p(kq) + kq\bigl(p+(q-1)\bigr)$, with $q-1$ truncated at zero. -/
theorem two_mul_card_edgeFinset :
    2 * (graph p k q).edgeFinset.card = p * (k * q) + k * q * (p + (q - 1)) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type]
  simp [degree_inl, degree_inr]

section Triangles

variable {V : Type*} {c : V → Fin p ⊕ (Fin k × Fin q)} {T Y : Finset V}

/-- A triangle of a graph pulled back from `CliqueJoin.graph p k q` has a vertex in a clique:
the independent set contains at most one of its vertices. -/
theorem exists_inr_of_isNClique (hT : ((graph p k q).comap c).IsNClique 3 T) :
    ∃ t ∈ T, ∃ x, c t = .inr x := by
  by_contra! h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by rw [hT.card_eq]; norm_num)
  have hadj : (graph p k q).Adj (c u) (c v) := hT.isClique hu hv huv
  rcases hcu : c u with a | x
  · rcases hcv : c v with b | y
    · rw [hcu, hcv] at hadj
      exact graph_adj_inl_inl a b hadj
    · exact h v hv y hcv
  · exact h u hu x hcu

/-- Two vertices of a triangle of a graph pulled back from `CliqueJoin.graph p k q` that lie in
cliques lie in the same clique. -/
theorem fst_eq_of_isNClique (hT : ((graph p k q).comap c).IsNClique 3 T) {t w : V} (ht : t ∈ T)
    (hw : w ∈ T) {x y : Fin k × Fin q} (hct : c t = .inr x) (hcw : c w = .inr y) :
    y.1 = x.1 := by
  by_cases hwt : w = t
  · subst hwt
    rw [hct, Sum.inr.injEq] at hcw
    rw [hcw]
  · have hadj : (graph p k q).Adj (c w) (c t) := hT.isClique hw ht hwt
    rw [hcw, hct, graph_adj_inr_inr] at hadj
    exact hadj.1

/-- The vertices of the independent set together with the `i`-th clique. -/
def block (p q : ℕ) (i : Fin k) : Finset (Fin p ⊕ (Fin k × Fin q)) :=
  Finset.univ.disjSum ({i} ×ˢ Finset.univ)

@[simp]
theorem card_block (i : Fin k) : (block p q i).card = p + q := by
  simp [block]

/-- Let `t` be a vertex of a triangle `T` of a graph pulled back from `CliqueJoin.graph p k q`,
lying in the clique `x.1`. Every vertex adjacent to two distinct vertices of `T` lies in the
independent set or in the clique `x.1`. -/
theorem mem_block_of_joinedToTwo (hT : ((graph p k q).comap c).IsNClique 3 T)
    (hY : JoinedToTwo ((graph p k q).comap c) T Y) {t : V} (ht : t ∈ T) {x : Fin k × Fin q}
    (hct : c t = .inr x) {y : V} (hy : y ∈ Y) : c y ∈ block p q x.1 := by
  obtain ⟨u, hu, v, hv, huv, hyu, hyv⟩ := hY y hy
  have huv' : (graph p k q).Adj (c u) (c v) := hT.isClique hu hv huv
  change (graph p k q).Adj (c y) (c u) at hyu
  change (graph p k q).Adj (c y) (c v) at hyv
  rcases hcy : c y with a | z
  · simp [block]
  · rw [hcy] at hyu hyv
    have hz : z.1 = x.1 := by
      rcases hcu : c u with a₁ | z₁
      · rcases hcv : c v with a₂ | z₂
        · rw [hcu, hcv] at huv'
          exact absurd huv' (graph_adj_inl_inl _ _)
        · rw [hcv, graph_adj_inr_inr] at hyv
          exact hyv.1.trans (fst_eq_of_isNClique hT ht hv hct hcv)
      · rw [hcu, graph_adj_inr_inr] at hyu
        exact hyu.1.trans (fst_eq_of_isNClique hT ht hu hct hcu)
    obtain ⟨j, d⟩ := z
    simp [block, ← hz]

/-- **Vertices adjacent to two vertices of a triangle.** In a graph pulled back from
`CliqueJoin.graph p k q` along an injective map, a set of vertices, each adjacent to two distinct
vertices of a triangle, has at most `p + q` elements. -/
theorem card_le_of_joinedToTwo (hc : Function.Injective c)
    (hT : ((graph p k q).comap c).IsNClique 3 T) (hY : JoinedToTwo ((graph p k q).comap c) T Y) :
    Y.card ≤ p + q := by
  obtain ⟨t, ht, x, hct⟩ := exists_inr_of_isNClique hT
  calc Y.card ≤ (block p q x.1).card :=
        Finset.card_le_card_of_injOn c (fun y hy => mem_block_of_joinedToTwo hT hY ht hct hy)
          hc.injOn
    _ = p + q := card_block _

end Triangles

end CliqueJoin

/-- Pulling a graph back along an equivalence preserves its number of edges. -/
private theorem ncard_edgeSet_comap {V W : Type*} (G : SimpleGraph W) (e : V ≃ W) :
    (G.comap e).edgeSet.ncard = G.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (SimpleGraph.Iso.comap e G).mapEdgeSet

/--
**The Erdős–Faudree triangle conjecture is false.** It is not true that for every real
$\varepsilon > 0$ and all sufficiently large $n$, every simple graph on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set of more than
$(1/2 - \varepsilon)n$ vertices, each adjacent to two distinct vertices of $T$.

Source: Ma and Tang (disproof with upper bound (2-√(5/2)+o(1))n; K₄-free sketch with
(2√3-3+o(1))n), per erdosproblems.com/1034, https://www.erdosproblems.com/1034. Moved from
`OpenConjectures/GraphTheory/ErdosProblem1034`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1 / 46) (by norm_num))
  -- Let `s = N + 1`. The graph `CliqueJoin.graph (8 * s) 5 (3 * s)`, carried to the
  -- `n = 8 * s + 5 * (3 * s) = 23 * s` vertices of `Fin n`, has more than `n ^ 2 / 4` edges, but
  -- `Y.card ≤ 11 * s = (1 / 2 - 1 / 46) * n` for every triangle `T` and every admissible `Y`.
  let e : Fin (8 * (N + 1)) ⊕ (Fin 5 × Fin (3 * (N + 1))) ≃
      Fin (8 * (N + 1) + 5 * (3 * (N + 1))) :=
    (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv
  let G := (CliqueJoin.graph (8 * (N + 1)) 5 (3 * (N + 1))).comap e.symm
  have hE : 2 * G.edgeSet.ncard =
      8 * (N + 1) * (5 * (3 * (N + 1))) + 5 * (3 * (N + 1)) * (8 * (N + 1) + (3 * N + 2)) := by
    rw [ncard_edgeSet_comap, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
      CliqueJoin.two_mul_card_edgeFinset, show 3 * (N + 1) - 1 = 3 * N + 2 by omega]
  have hE' : (2 : ℝ) * G.edgeSet.ncard =
      8 * (N + 1) * (5 * (3 * (N + 1))) + 5 * (3 * (N + 1)) * (8 * (N + 1) + (3 * N + 2)) := by
    exact_mod_cast hE
  obtain ⟨T, hT, Y, hY, hlt⟩ := hN _ (by omega) G (by
    push_cast
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N])
  have hY' : (Y.card : ℝ) ≤ 8 * (N + 1) + 3 * (N + 1) := by
    exact_mod_cast CliqueJoin.card_le_of_joinedToTwo e.symm.injective hT hY
  push_cast at hlt
  linarith

end MathlibExt.GraphTheory.ErdosProblem1034Wanted
