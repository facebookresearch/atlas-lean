/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted vertex cover: the pricing method

The pricing (primal-dual) 2-approximation for weighted vertex cover (R. Bar-Yehuda and S. Even,
*A linear-time approximation algorithm for the weighted vertex cover problem*, J. Algorithms 2,
1981; Kleinberg and Tardos, *Algorithm Design*, Section 11.4): every vertex `v` has a weight
`w v ≥ 0`; scan the edges, and let each edge `(u, v)` pay the price `δ = min (r u) (r v)`, where
`r` is the weight each vertex has left; subtract `δ` from `r u` and `r v`. At the end, take the
vertices whose weight is used up (`r v = 0`). With unit weights this is a weighted relative of
`APPROX-VERTEX-COVER` (`VertexCover.lean`).

Results, for nonnegative weights:

* `pricingVertexCover_covers`: every listed edge has an endpoint in the result (after an edge is
  paid, one endpoint has nothing left, and residual weights only decrease and stay
  nonnegative); `pricingVertexCover_isVertexCover` restates it for a Mathlib `SimpleGraph` each of
  whose edges is listed in at least one orientation.
* `pricingVertexCover_weight_le`: the result weighs at most twice any vertex cover `C*` of the
  listed edges.

The proof follows Kleinberg and Tardos. The prices are fair: no vertex pays more than its weight
(residuals stay nonnegative). Each vertex of the result has paid exactly its weight, and each
edge's price is paid by its two endpoints, so the result weighs at most twice the total price
(`sum_drop_le_two_mul_price`). Each edge has an endpoint in `C*`, which pays that edge's price,
so the total price is at most what the vertices of `C*` pay, at most their weight
(`price_le_sum_drop`).

## Cost model

One unit per listed edge (computing the price and updating two residual weights, constant time
with an array indexed by vertex), and one unit per vertex for the final selection; the result
costs exactly `|edges| + |V|` (`pricingVertexCover_time`). Arithmetic on weights is charged as
constant time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {V : Type u} [DecidableEq V]

/-- Scan the remaining edges with residual weights `r` and total price `P`: edge `(u, v)` pays
`δ = min (r u) (r v)`, subtracted from `r u` and `r v`. One unit per edge. -/
def pricingScan : (V → ℚ) → ℚ → List (V × V) → TimeM ℕ ((V → ℚ) × ℚ)
  | r, P, [] => pure (r, P)
  | r, P, (u, v) :: es => do
      ✓
      let δ := min (r u) (r v)
      pricingScan (fun x => if x = u ∨ x = v then r x - δ else r x) (P + δ) es

/-- The pricing method: scan the edges starting from the weights, then take the vertices whose
weight is used up. -/
def pricingVertexCover [Fintype V] (w : V → ℚ) (edges : List (V × V)) : TimeM ℕ (Finset V) := do
  let res ← pricingScan w 0 edges
  ✓[Fintype.card V]
  pure (Finset.univ.filter fun v => res.1 v = 0)

/-! ## The scan -/

/-- Residual weights stay nonnegative and only decrease. -/
theorem pricingScan_residual : ∀ (es : List (V × V)) (r : V → ℚ) (P : ℚ), (∀ v, 0 ≤ r v) →
    ∀ v, 0 ≤ (pricingScan r P es).ret.1 v ∧ (pricingScan r P es).ret.1 v ≤ r v
  | [], r, P, hr, v => by simp [pricingScan, hr v]
  | (a, b) :: es, r, P, hr, v => by
      simp only [pricingScan, ret_bind]
      have hr' : ∀ x, 0 ≤ (if x = a ∨ x = b then r x - min (r a) (r b) else r x) := by
        intro x
        split_ifs with hx
        · rcases hx with rfl | rfl
          · have := min_le_left (r x) (r b); linarith
          · have := min_le_right (r a) (r x); linarith
        · exact hr x
      obtain ⟨h1, h2⟩ := pricingScan_residual es _ (P + min (r a) (r b)) hr' v
      refine ⟨h1, h2.trans ?_⟩
      split_ifs
      · have := le_min (hr a) (hr b); linarith
      · exact le_rfl

/-- After the scan, every listed edge has an endpoint with nothing left. -/
theorem pricingScan_covers : ∀ (es : List (V × V)) (r : V → ℚ) (P : ℚ), (∀ v, 0 ≤ r v) →
    ∀ e ∈ es, (pricingScan r P es).ret.1 e.1 = 0 ∨ (pricingScan r P es).ret.1 e.2 = 0
  | [], _, _, _, e, he => by simp at he
  | (a, b) :: es, r, P, hr, e, he => by
      simp only [pricingScan, ret_bind]
      set r' : V → ℚ := fun x => if x = a ∨ x = b then r x - min (r a) (r b) else r x with hr'def
      have hr' : ∀ x, 0 ≤ r' x := by
        intro x
        simp only [hr'def]
        split_ifs with hx
        · rcases hx with rfl | rfl
          · have := min_le_left (r x) (r b); linarith
          · have := min_le_right (r a) (r x); linarith
        · exact hr x
      rcases List.mem_cons.1 he with heq | he
      · -- the edge just paid: its cheaper endpoint has nothing left, and stays so
        subst heq
        have hzero : r' a = 0 ∨ r' b = 0 := by
          simp only [hr'def, true_or, or_true, ite_true]
          rcases le_total (r a) (r b) with h | h
          · left; rw [min_eq_left h]; ring
          · right; rw [min_eq_right h]; ring
        have hres := pricingScan_residual es r' (P + min (r a) (r b)) hr'
        rcases hzero with h | h
        · left; have := hres a; simp only; linarith [this.1, this.2]
        · right; have := hres b; simp only; linarith [this.1, this.2]
      · exact pricingScan_covers es r' _ hr' e he

/-- What the vertices pay in total is at most twice the total price: each edge's price is paid by
its two endpoints. -/
theorem sum_drop_le_two_mul_price [Fintype V] : ∀ (es : List (V × V)) (r : V → ℚ) (P : ℚ),
    (∀ v, 0 ≤ r v) →
    ∑ v, (r v - (pricingScan r P es).ret.1 v) ≤ 2 * ((pricingScan r P es).ret.2 - P)
  | [], r, P, _ => by simp [pricingScan]
  | (a, b) :: es, r, P, hr => by
      simp only [pricingScan, ret_bind]
      set δ := min (r a) (r b)
      set r' : V → ℚ := fun x => if x = a ∨ x = b then r x - δ else r x with hr'def
      have hδ0 : 0 ≤ δ := le_min (hr a) (hr b)
      have hr' : ∀ x, 0 ≤ r' x := by
        intro x
        simp only [hr'def]
        split_ifs with hx
        · rcases hx with rfl | rfl
          · have := min_le_left (r x) (r b); linarith
          · have := min_le_right (r a) (r x); linarith
        · exact hr x
      have ih := sum_drop_le_two_mul_price es r' (P + δ) hr'
      -- the drop of this step: `δ` at `a` and at `b` (once if `a = b`)
      have hstep : ∑ v, (r v - r' v) ≤ 2 * δ := by
        have : ∀ v, r v - r' v = if v = a ∨ v = b then δ else 0 := by
          intro v; simp only [hr'def]; split_ifs <;> ring
        simp only [this]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.univ.filter fun v => v = a ∨ v = b).card ≤ 2 := by
          calc (Finset.univ.filter fun v => v = a ∨ v = b).card ≤ ({a, b} : Finset V).card :=
                Finset.card_le_card fun v hv => by simpa using hv
            _ ≤ 2 := Finset.card_le_two
        have : ((Finset.univ.filter fun v => v = a ∨ v = b).card : ℚ) ≤ 2 := by
          exact_mod_cast hcard
        nlinarith
      have hsplit : ∑ v, (r v - (pricingScan r' (P + δ) es).ret.1 v) =
          ∑ v, (r v - r' v) + ∑ v, (r' v - (pricingScan r' (P + δ) es).ret.1 v) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [hsplit]
      linarith

/-- The total price is at most what the vertices of any cover `C*` of the listed edges pay: every
edge has an endpoint in `C*`, which pays its price. -/
theorem price_le_sum_drop (C : Finset V) : ∀ (es : List (V × V)) (r : V → ℚ) (P : ℚ),
    (∀ v, 0 ≤ r v) → (∀ e ∈ es, e.1 ∈ C ∨ e.2 ∈ C) →
    (pricingScan r P es).ret.2 - P ≤ ∑ v ∈ C, (r v - (pricingScan r P es).ret.1 v)
  | [], r, P, _, _ => by simp [pricingScan]
  | (a, b) :: es, r, P, hr, hC => by
      simp only [pricingScan, ret_bind]
      set δ := min (r a) (r b)
      set r' : V → ℚ := fun x => if x = a ∨ x = b then r x - δ else r x with hr'def
      have hδ0 : 0 ≤ δ := le_min (hr a) (hr b)
      have hr' : ∀ x, 0 ≤ r' x := by
        intro x
        simp only [hr'def]
        split_ifs with hx
        · rcases hx with rfl | rfl
          · have := min_le_left (r x) (r b); linarith
          · have := min_le_right (r a) (r x); linarith
        · exact hr x
      have ih := price_le_sum_drop C es r' (P + δ) hr'
        (fun e he => hC e (List.mem_cons_of_mem _ he))
      -- this step's drops on `C` add up to at least `δ`
      have hdrop : ∀ v, 0 ≤ r v - r' v := by
        intro v; simp only [hr'def]; split_ifs <;> linarith
      have hstep : δ ≤ ∑ v ∈ C, (r v - r' v) := by
        rcases hC (a, b) List.mem_cons_self with h | h
        · have := Finset.single_le_sum (f := fun v => r v - r' v) (fun v _ => hdrop v) h
          simpa [hr'def] using this
        · have := Finset.single_le_sum (f := fun v => r v - r' v) (fun v _ => hdrop v) h
          simpa [hr'def] using this
      have hsplit : ∑ v ∈ C, (r v - (pricingScan r' (P + δ) es).ret.1 v) =
          ∑ v ∈ C, (r v - r' v) + ∑ v ∈ C, (r' v - (pricingScan r' (P + δ) es).ret.1 v) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [hsplit]
      linarith

/-! ## The pricing method -/

variable [Fintype V]

/-- The result covers every listed edge. -/
theorem pricingVertexCover_covers (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (edges : List (V × V)) :
    ∀ e ∈ edges,
      e.1 ∈ (pricingVertexCover w edges).ret ∨ e.2 ∈ (pricingVertexCover w edges).ret := by
  intro e he
  simp only [pricingVertexCover, ret_bind, ret_pure, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact pricingScan_covers edges w 0 hw e he

/-- For a graph each of whose edges is listed in at least one orientation, the result is a vertex
cover. -/
theorem pricingVertexCover_isVertexCover (G : SimpleGraph V) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (edges : List (V × V)) (hG : ∀ u v, G.Adj u v → (u, v) ∈ edges ∨ (v, u) ∈ edges) :
    G.IsVertexCover ↑(pricingVertexCover w edges).ret := by
  intro u v huv
  rcases hG u v huv with h | h
  · simpa using pricingVertexCover_covers w hw edges (u, v) h
  · simpa [or_comm] using pricingVertexCover_covers w hw edges (v, u) h

/-- **The 2-approximation.** For nonnegative weights, the result weighs at most twice any vertex
cover `C*` of the listed edges. -/
theorem pricingVertexCover_weight_le (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (edges : List (V × V))
    (C : Finset V) (hC : ∀ e ∈ edges, e.1 ∈ C ∨ e.2 ∈ C) :
    ∑ v ∈ (pricingVertexCover w edges).ret, w v ≤ 2 * ∑ v ∈ C, w v := by
  simp only [pricingVertexCover, ret_bind, ret_pure]
  set res := pricingScan w 0 edges
  have hres := pricingScan_residual edges w 0 hw
  -- each chosen vertex has paid its whole weight
  have h1 : ∑ v ∈ Finset.univ.filter (fun v => res.ret.1 v = 0), w v =
      ∑ v ∈ Finset.univ.filter (fun v => res.ret.1 v = 0), (w v - res.ret.1 v) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.1 hv).2, sub_zero]
  have h2 : ∑ v ∈ Finset.univ.filter (fun v => res.ret.1 v = 0), (w v - res.ret.1 v) ≤
      ∑ v, (w v - res.ret.1 v) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun v _ _ => by have := hres v; linarith
  have h3 := sum_drop_le_two_mul_price edges w 0 hw
  have h4 := price_le_sum_drop C edges w 0 hw hC
  have h5 : ∑ v ∈ C, (w v - res.ret.1 v) ≤ ∑ v ∈ C, w v :=
    Finset.sum_le_sum fun v _ => by have := hres v; linarith
  simp only [sub_zero] at h3 h4
  linarith

/-- **Cost.** Exactly one unit per listed edge and one per vertex. -/
theorem pricingVertexCover_time (w : V → ℚ) (edges : List (V × V)) :
    (pricingVertexCover w edges).time = edges.length + Fintype.card V := by
  have : ∀ (es : List (V × V)) (r : V → ℚ) (P : ℚ), (pricingScan r P es).time = es.length := by
    intro es
    induction es with
    | nil => intro r P; simp [pricingScan]
    | cons e es ih =>
        intro r P
        obtain ⟨a, b⟩ := e
        simp only [pricingScan, time_bind, time_tick, ih, List.length_cons]
        omega
  simp only [pricingVertexCover, time_bind, time_tick, time_pure, this]
  omega

end Cslib.Algorithms.Lean.TimeM
