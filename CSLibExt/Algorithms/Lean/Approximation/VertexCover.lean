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

/-- Scan the remaining edges. A covered edge is skipped; an uncovered edge `(u, v)` puts both `u`
and `v` into the cover. -/
def vertexCoverScan (cover : Finset V) : List (V × V) → TimeM ℕ (Finset V)
  | [] => pure cover
  | (u, v) :: es => do
      ✓
      if u ∈ cover ∨ v ∈ cover then vertexCoverScan cover es
      else vertexCoverScan (insert u (insert v cover)) es

/-- CLRS `APPROX-VERTEX-COVER` over an edge list, starting from the empty cover. -/
def approxVertexCover (edges : List (V × V)) : TimeM ℕ (Finset V) :=
  vertexCoverScan ∅ edges

/-! ## Cost -/

@[simp]
theorem vertexCoverScan_time (cover : Finset V) (edges : List (V × V)) :
    (vertexCoverScan cover edges).time = edges.length := by
  induction edges generalizing cover with
  | nil => simp [vertexCoverScan]
  | cons e es ih =>
      obtain ⟨u, v⟩ := e
      by_cases h : u ∈ cover ∨ v ∈ cover <;> simp [vertexCoverScan, h, ih, Nat.add_comm]

/-- One unit per listed edge. -/
@[simp]
theorem approxVertexCover_time (edges : List (V × V)) :
    (approxVertexCover edges).time = edges.length :=
  vertexCoverScan_time ∅ edges

/-! ## The result is a vertex cover -/

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

/-- Every listed edge has an endpoint in the returned cover. -/
theorem approxVertexCover_covers (edges : List (V × V)) :
    ∀ e ∈ edges, e.1 ∈ (approxVertexCover edges).ret ∨ e.2 ∈ (approxVertexCover edges).ret :=
  vertexCoverScan_covers ∅ edges

/-- If every edge of `G` is listed, in either orientation, the result is a vertex cover of `G`. -/
theorem approxVertexCover_isVertexCover (G : SimpleGraph V) (edges : List (V × V))
    (hcomplete : ∀ ⦃u v⦄, G.Adj u v → (u, v) ∈ edges ∨ (v, u) ∈ edges) :
    G.IsVertexCover ↑(approxVertexCover edges).ret := by
  intro u v huv
  rcases hcomplete huv with h | h
  · simpa using approxVertexCover_covers edges _ h
  · simpa [or_comm] using approxVertexCover_covers edges _ h

/-! ## The factor-two bound -/

/-- The counting invariant: every vertex cover `S` of `G` contains at least half of the vertices
the scan has chosen, because each taken edge adds two new vertices, at least one of them in `S`. -/
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

/-- If every listed pair is an edge of `G`, the result has at most twice as many vertices as any
vertex cover of `G`. -/
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

/-- CLRS Theorem 35.1: if `edges` lists exactly the edges of `G`, each in at least one orientation,
then `approxVertexCover edges` is a vertex cover of `G` of size at most twice the vertex cover
number. -/
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

/-- Two pairs share no endpoint. -/
def VertexDisjoint (e f : V × V) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

/-- The scan's matching invariant: the edges it takes, in order, form a sublist of the scanned
edges whose endpoints are new, pairwise disjoint, and exactly the vertices it adds. -/
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

/-- The edges `APPROX-VERTEX-COVER` takes form a maximal matching `A` of the listed edges:
they are listed edges, pairwise vertex-disjoint, every listed edge shares an endpoint with one of
them, the returned cover is exactly their endpoints, and it has `2 * A.length` vertices. -/
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
