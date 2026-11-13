/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Vertex cover: the matching-based 2-approximation

`APPROX-VERTEX-COVER` from CLRS, third edition, Section 35.1: repeatedly take an edge `(u, v)`
that no chosen vertex covers, add both endpoints to the cover, and discard the edges they cover.
The edges taken are pairwise vertex-disjoint, so any vertex cover needs a distinct vertex for each
of them, while the returned cover has exactly two vertices per edge taken. CLRS Theorem 35.1:
the result is a vertex cover at most twice the minimum size.

`approxVertexCover edges` scans an edge list once, in order, so "an arbitrary uncovered edge" is
the first uncovered edge in list order; the bounds hold for every order. An edge is covered when
either endpoint is already in the cover; then it is skipped. The edges taken form a maximal
matching (`approxVertexCover_matching`).

The graph is a Mathlib `SimpleGraph V`; `edges` enumerates it, each edge in either orientation and
possibly repeated. The cover property needs only that every edge of `G` occurs in `edges`; the
size bound needs only that every listed pair is an edge of `G`. The bound is stated against
Mathlib's `SimpleGraph.vertexCoverNum`, so `OPT` is the minimum over all vertex covers.

## Cost model

Each listed edge costs one unit: testing both endpoints for membership in the cover and, when the
edge is taken, inserting both endpoints. This is the constant-time-per-edge part of the `O(V + E)`
bound in CLRS, assuming constant-time membership (for example a Boolean array indexed by vertex);
allocating that structure is not charged. The list costs exactly `edges.length`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {V : Type u} [DecidableEq V]

/-- **Vertex cover scan.** Given a finite set $C$ of vertices and a list of pairs of vertices,
the scan processes the pairs in order, starting from the cover $C$ and charging one time unit
per pair. A pair $(u, v)$ is covered when $u$ or $v$ is already in the current cover; a covered
pair is skipped, and an uncovered pair adds both $u$ and $v$ to the cover. The scan returns the
cover reached after the last pair. -/
def vertexCoverScan (cover : Finset V) : List (V × V) → TimeM ℕ (Finset V)
  | [] => pure cover
  | (u, v) :: es => do
      ✓
      if u ∈ cover ∨ v ∈ cover then vertexCoverScan cover es
      else vertexCoverScan (insert u (insert v cover)) es

/-- **APPROX-VERTEX-COVER.** Given a list $L$ of ordered pairs of vertices, APPROX-VERTEX-COVER
starts from the empty cover and goes through $L$ in order: a pair $(u, v)$ with $u$ or $v$ already
in the cover is skipped, and otherwise both $u$ and $v$ are added to the cover. It returns the
final cover, a finite set of vertices, at a cost of one unit per pair of $L$.

CLRS (third edition, Section 35.1) takes an arbitrary uncovered edge at each step; here it is the
first uncovered pair in list order. -/
def approxVertexCover (edges : List (V × V)) : TimeM ℕ (Finset V) :=
  vertexCoverScan ∅ edges

/-! ## Cost -/

/-- **Running time of the vertex cover scan.** For every finite set $C$ of vertices and every list
$L$ of pairs of vertices, the running time of the vertex cover scan starting from $C$ on $L$ is
the length of $L$. -/
@[simp]
theorem vertexCoverScan_time (cover : Finset V) (edges : List (V × V)) :
    (vertexCoverScan cover edges).time = edges.length := by
  induction edges generalizing cover with
  | nil => simp [vertexCoverScan]
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      by_cases h : u ∈ cover ∨ v ∈ cover <;> simp [vertexCoverScan, h, ih, Nat.add_comm]

/-- **Running time of APPROX-VERTEX-COVER.** For every list $L$ of ordered pairs of vertices, the
cost of APPROX-VERTEX-COVER on $L$ is the length of $L$: one unit per listed pair. -/
@[simp]
theorem approxVertexCover_time (edges : List (V × V)) :
    (approxVertexCover edges).time = edges.length :=
  vertexCoverScan_time ∅ edges

/-! ## The result is a vertex cover -/

/-- **The vertex cover scan only adds vertices.** For every finite set $C$ of vertices and every
list of pairs of vertices, the cover returned by the vertex cover scan starting from $C$ on that
list contains $C$. -/
theorem subset_vertexCoverScan (cover : Finset V) (edges : List (V × V)) :
    cover ⊆ (vertexCoverScan cover edges).ret := by
  induction edges generalizing cover with
  | nil => simp [vertexCoverScan]
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      by_cases h : u ∈ cover ∨ v ∈ cover
      · simpa [vertexCoverScan, h] using ih cover
      · simp only [vertexCoverScan, h, ite_false, ret_bind]
        exact (Finset.subset_insert _ _).trans
          ((Finset.subset_insert _ _).trans (ih _))

theorem vertexCoverScan_covers (cover : Finset V) (edges : List (V × V)) :
    ∀ e ∈ edges, e.1 ∈ (vertexCoverScan cover edges).ret ∨
      e.2 ∈ (vertexCoverScan cover edges).ret := by
  induction edges generalizing cover with
  | nil => simp
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · by_cases h : u ∈ cover ∨ v ∈ cover
        · simp only [vertexCoverScan, h, ite_true, ret_bind]
          exact h.imp (fun hu => subset_vertexCoverScan _ _ hu)
            (fun hv => subset_vertexCoverScan _ _ hv)
        · simp only [vertexCoverScan, h, ite_false, ret_bind]
          exact Or.inl (subset_vertexCoverScan _ _ (by simp))
      · by_cases h : u ∈ cover ∨ v ∈ cover
        · simpa [vertexCoverScan, h] using ih cover f hf
        · simpa [vertexCoverScan, h] using ih _ f hf

/-- **APPROX-VERTEX-COVER covers every listed pair.** For every list $L$ of ordered pairs of
vertices and every pair $(u, v)$ in $L$, the cover that APPROX-VERTEX-COVER returns on $L$
contains $u$ or $v$. -/
theorem approxVertexCover_covers (edges : List (V × V)) :
    ∀ e ∈ edges, e.1 ∈ (approxVertexCover edges).ret ∨ e.2 ∈ (approxVertexCover edges).ret :=
  vertexCoverScan_covers ∅ edges

/-- **APPROX-VERTEX-COVER returns a vertex cover.** Let $G$ be a simple graph and $L$ a list of
ordered pairs of vertices such that for every edge $uv$ of $G$, $(u, v)$ or $(v, u)$ is in $L$.
Then the cover that APPROX-VERTEX-COVER returns on $L$ is a vertex cover of $G$. -/
theorem approxVertexCover_isVertexCover (G : SimpleGraph V) (edges : List (V × V))
    (hcomplete : ∀ ⦃u v⦄, G.Adj u v → (u, v) ∈ edges ∨ (v, u) ∈ edges) :
    G.IsVertexCover ↑(approxVertexCover edges).ret := by
  intro u v huv
  rcases hcomplete huv with h | h
  · simpa using approxVertexCover_covers edges _ h
  · simpa [or_comm] using approxVertexCover_covers edges _ h

/-! ## The factor-two bound -/

/-- **Counting invariant of the vertex cover scan.** Let $G$ be a simple graph, $S$ a vertex cover
of $G$, $C_0$ a finite set of vertices with $|C_0| \le 2|C_0 \cap S|$, and $L$ a list of ordered
pairs of vertices such that $u$ and $v$ are adjacent in $G$ for every $(u, v)$ in $L$. Then the
cover $C$ that the vertex cover scan returns on $L$ starting from $C_0$ satisfies
$|C| \le 2|C \cap S|$.

The invariant holds because each taken edge adds two new vertices, at least one of them in $S$. -/
theorem card_vertexCoverScan_le (G : SimpleGraph V) (S : Set V) (hS : G.IsVertexCover S)
    [DecidablePred (· ∈ S)] (cover : Finset V) (edges : List (V × V))
    (hsound : ∀ e ∈ edges, G.Adj e.1 e.2)
    (hcover : cover.card ≤ 2 * (cover.filter (· ∈ S)).card) :
    (vertexCoverScan cover edges).ret.card ≤
      2 * ((vertexCoverScan cover edges).ret.filter (· ∈ S)).card := by
  induction edges generalizing cover with
  | nil => simpa [vertexCoverScan] using hcover
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      have hes : ∀ e ∈ es, G.Adj e.1 e.2 := fun e he => hsound e (List.mem_cons_of_mem _ he)
      have huv : G.Adj u v := hsound (u, v) List.mem_cons_self
      by_cases h : u ∈ cover ∨ v ∈ cover
      · simpa [vertexCoverScan, h] using ih cover hes hcover
      · simp only [vertexCoverScan, h, ite_false, ret_bind]
        apply ih _ hes
        replace h := not_or.1 h
        have hne : u ≠ v := huv.ne
        have hu : u ∉ insert v cover := by simp [hne, h.1]
        rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem h.2,
          Finset.filter_insert, Finset.filter_insert]
        rcases hS huv with huS | hvS
        · by_cases hvS : v ∈ S
          · simp only [huS, hvS, ite_true]
            rw [Finset.card_insert_of_notMem (by simp [hne, h.1]),
              Finset.card_insert_of_notMem (by simp [h.2])]
            omega
          · simp only [huS, hvS, ite_true, ite_false]
            rw [Finset.card_insert_of_notMem (by simp [h.1])]
            omega
        · by_cases huS : u ∈ S
          · simp only [huS, hvS, ite_true]
            rw [Finset.card_insert_of_notMem (by simp [hne, h.1]),
              Finset.card_insert_of_notMem (by simp [h.2])]
            omega
          · simp only [huS, hvS, ite_true, ite_false]
            rw [Finset.card_insert_of_notMem (by simp [h.2])]
            omega

/-- **APPROX-VERTEX-COVER is at most twice any vertex cover.** Let $G$ be a simple graph and $L$ a
list of ordered pairs of vertices such that $u$ and $v$ are adjacent in $G$ for every $(u, v)$ in
$L$. Then for every vertex cover $S$ of $G$, finite or infinite, the cover $C$ that
APPROX-VERTEX-COVER returns on $L$ satisfies $|C| \le 2|S|$, with sizes in
$\mathbb{N} \cup \{\infty\}$. -/
theorem card_approxVertexCover_le_two_mul (G : SimpleGraph V) (edges : List (V × V))
    (hsound : ∀ e ∈ edges, G.Adj e.1 e.2) (S : Set V) (hS : G.IsVertexCover S) :
    ((approxVertexCover edges).ret.card : ℕ∞) ≤ 2 * S.encard := by
  classical
  have h := card_vertexCoverScan_le G S hS ∅ edges hsound (by simp)
  set C := (approxVertexCover edges).ret
  have hfilter : ((C.filter (· ∈ S)).card : ℕ∞) ≤ S.encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_le_encard (fun x hx => (Finset.mem_filter.1 hx).2)
  calc (C.card : ℕ∞) ≤ ((2 * (C.filter (· ∈ S)).card : ℕ) : ℕ∞) := by
        exact_mod_cast h
    _ = 2 * ((C.filter (· ∈ S)).card : ℕ∞) := by push_cast; rfl
    _ ≤ 2 * S.encard := by gcongr

/-- **APPROX-VERTEX-COVER is a 2-approximation.** Let $G$ be a simple graph and $L$ a list of
ordered pairs of vertices that lists exactly the edges of $G$, each in at least one orientation:
$u$ and $v$ are adjacent in $G$ for every $(u, v)$ in $L$, and for every edge $uv$ of $G$,
$(u, v)$ or $(v, u)$ is in $L$. Then the cover $C$ that APPROX-VERTEX-COVER returns on $L$ is a
vertex cover of $G$ and $|C| \le 2\tau(G)$, where $\tau(G) \in \mathbb{N} \cup \{\infty\}$ is the
vertex cover number of $G$, the minimum size of a vertex cover of $G$.

Source: CLRS, third edition, Theorem 35.1. -/
theorem approxVertexCover_two_approximation (G : SimpleGraph V) (edges : List (V × V))
    (hsound : ∀ e ∈ edges, G.Adj e.1 e.2)
    (hcomplete : ∀ ⦃u v⦄, G.Adj u v → (u, v) ∈ edges ∨ (v, u) ∈ edges) :
    G.IsVertexCover ↑(approxVertexCover edges).ret ∧
      ((approxVertexCover edges).ret.card : ℕ∞) ≤ 2 * G.vertexCoverNum := by
  refine ⟨approxVertexCover_isVertexCover G edges hcomplete, ?_⟩
  obtain ⟨S, hcard, hS⟩ := G.vertexCoverNum_exists
  rw [← hcard]
  exact card_approxVertexCover_le_two_mul G edges hsound S hS

/-! ## The edges taken form a maximal matching -/

/-- **Vertex-disjoint pairs.** Two pairs $(a, b)$ and $(c, d)$ of vertices are vertex-disjoint
when they share no endpoint: $a \ne c$, $a \ne d$, $b \ne c$ and $b \ne d$. -/
def VertexDisjoint (e f : V × V) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

/-- **Matching invariant of the vertex cover scan.** Let $G$ be a simple graph, $C_0$ a finite set
of vertices, and $L$ a list of ordered pairs of vertices such that $u$ and $v$ are adjacent in $G$
for every $(u, v)$ in $L$, and let $C$ be the cover that the vertex cover scan returns on $L$
starting from $C_0$. Then there is a sublist $A$ of $L$ such that neither endpoint of any pair in
$A$ lies in $C_0$, pairs at different positions of $A$ are vertex-disjoint, a vertex lies in $C$
exactly when it lies in $C_0$ or is an endpoint of some pair in $A$, and $|C| = |C_0| + 2|A|$,
where $|A|$ is the length of $A$. -/
theorem exists_matching_vertexCoverScan (G : SimpleGraph V) (cover : Finset V)
    (edges : List (V × V)) (hsound : ∀ e ∈ edges, G.Adj e.1 e.2) :
    ∃ A : List (V × V), A.Sublist edges ∧ (∀ e ∈ A, e.1 ∉ cover ∧ e.2 ∉ cover) ∧
      A.Pairwise VertexDisjoint ∧
      (∀ x, x ∈ (vertexCoverScan cover edges).ret ↔ x ∈ cover ∨ ∃ e ∈ A, x = e.1 ∨ x = e.2) ∧
      (vertexCoverScan cover edges).ret.card = cover.card + 2 * A.length := by
  induction edges generalizing cover with
  | nil => exact ⟨[], List.Sublist.slnil, by simp, List.Pairwise.nil, by simp [vertexCoverScan],
      by simp [vertexCoverScan]⟩
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      have hes : ∀ e ∈ es, G.Adj e.1 e.2 := fun e he => hsound e (List.mem_cons_of_mem _ he)
      have huv : u ≠ v := (hsound (u, v) List.mem_cons_self).ne
      by_cases h : u ∈ cover ∨ v ∈ cover
      · obtain ⟨A, hA, hnew, hpair, hmem, hcard⟩ := ih cover hes
        refine ⟨A, hA.cons _, hnew, hpair, ?_, ?_⟩
        · simpa only [vertexCoverScan, h, ite_true, ret_bind] using hmem
        · simpa only [vertexCoverScan, h, ite_true, ret_bind] using hcard
      · obtain ⟨hu, hv⟩ := not_or.1 h
        obtain ⟨A, hA, hnew, hpair, hmem, hcard⟩ := ih (insert u (insert v cover)) hes
        refine ⟨(u, v) :: A, hA.cons_cons _, ?_, ?_, ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨hu, hv⟩
          · have := hnew e he
            simp only [Finset.mem_insert, not_or] at this
            exact ⟨this.1.2.2, this.2.2.2⟩
        · refine List.Pairwise.cons (fun f hf => ?_) hpair
          have := hnew f hf
          simp only [Finset.mem_insert, not_or] at this
          exact ⟨Ne.symm this.1.1, Ne.symm this.2.1, Ne.symm this.1.2.1, Ne.symm this.2.2.1⟩
        · intro x
          simp only [vertexCoverScan, h, ite_false, ret_bind, hmem, Finset.mem_insert,
            List.mem_cons, or_and_right, exists_or, exists_eq_left]
          generalize (∃ e, e ∈ A ∧ (x = e.fst ∨ x = e.snd)) = Q
          tauto
        · simp only [vertexCoverScan, h, ite_false, ret_bind, hcard, List.length_cons]
          rw [Finset.card_insert_of_notMem (by simp [huv, hu]),
            Finset.card_insert_of_notMem hv]
          omega

/-- **The edges APPROX-VERTEX-COVER takes form a maximal matching of the listed pairs.** Let $G$
be a simple graph and $L$ a list of ordered pairs of vertices such that $u$ and $v$ are adjacent
in $G$ for every $(u, v)$ in $L$, and let $C$ be the cover that APPROX-VERTEX-COVER returns on
$L$. Then there is a sublist $A$ of $L$ such that pairs at different positions of $A$ are
vertex-disjoint, every pair in $L$ shares an endpoint with some pair in $A$, a vertex lies in $C$
exactly when it is an endpoint of some pair in $A$, and $|C| = 2|A|$, where $|A|$ is the length of
$A$. -/
theorem approxVertexCover_matching (G : SimpleGraph V) (edges : List (V × V))
    (hsound : ∀ e ∈ edges, G.Adj e.1 e.2) :
    ∃ A : List (V × V), A.Sublist edges ∧ A.Pairwise VertexDisjoint ∧
      (∀ e ∈ edges, ∃ f ∈ A, e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) ∧
      (∀ x, x ∈ (approxVertexCover edges).ret ↔ ∃ e ∈ A, x = e.1 ∨ x = e.2) ∧
      (approxVertexCover edges).ret.card = 2 * A.length := by
  obtain ⟨A, hA, -, hpair, hmem, hcard⟩ := exists_matching_vertexCoverScan G ∅ edges hsound
  have hmem' : ∀ x, x ∈ (approxVertexCover edges).ret ↔ ∃ e ∈ A, x = e.1 ∨ x = e.2 := by
    simpa [approxVertexCover] using hmem
  refine ⟨A, hA, hpair, fun e he => ?_, hmem', by simpa [approxVertexCover] using hcard⟩
  rcases approxVertexCover_covers edges e he with h | h
  · obtain ⟨f, hf, hx⟩ := (hmem' _).1 h
    exact ⟨f, hf, by tauto⟩
  · obtain ⟨f, hf, hx⟩ := (hmem' _).1 h
    exact ⟨f, hf, by tauto⟩

end Cslib.Algorithms.Lean.TimeM
