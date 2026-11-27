/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
import MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reduced-cost certificates for minimum-cost flows

Balances are prescribed **net inflows**, in the sign convention of `ArcNetwork.incidenceMatrix`.
Neither arc costs nor lower bounds need be nonnegative. Each residual arc retains its original
arc ID and its direction, even for loops. When the vertex and arc sets are finite, a feasible flow
with a residual potential has least cost among flows with those bounds and balances.

For potential existence, only the original arc set must be finite. If no elementary residual cycle
has negative cost, least walk costs from arbitrary starting vertices supply such a potential.
The vertex type need not be finite, and no common source is required.

A. Schrijver, *A Course in Combinatorial Optimization* (23 March 2017), §4.6, Proposition 4,
pp. 71–72, gives the signed auxiliary costs and the sign split for competing flows of equal
`s`–`t` value. Here the incidence pairing handles prescribed balances and two signed bounds.
The walk argument uses the circuit erasure of §1.3, Theorem 1.9, pp. 12–13; it needs neither a
single vertex reaching all others nor an algorithm for comparing real lengths.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Combinatorics.Graph.ArcNetwork.MinCostFlow

open Matrix

variable {V E : Type*}

/-- Capacity of a labelled forward (`inl`) or reverse (`inr`) copy of an original arc. -/
noncomputable def residualCapacity (l u f : E → ℝ) : E ⊕ E → ℝ :=
  Sum.elim (u - f) (f - l)

/-- Only copies of strictly positive capacity occur in the residual network. -/
abbrev ResidualArc (l u f : E → ℝ) := {a : E ⊕ E // 0 < residualCapacity l u f a}

@[simp] theorem forward_capacity_pos {l u f : E → ℝ} {e : E} :
    0 < residualCapacity l u f (.inl e) ↔ f e < u e := sub_pos

@[simp] theorem reverse_capacity_pos {l u f : E → ℝ} {e : E} :
    0 < residualCapacity l u f (.inr e) ↔ l e < f e := sub_pos

variable {l u f : E → ℝ}

/-- The starting vertex, reversed on a reverse copy. -/
def ResidualArc.tail (tail head : E → V) (a : ResidualArc l u f) : V :=
  Sum.elim tail head a.val

/-- The ending vertex, reversed on a reverse copy. -/
def ResidualArc.head (tail head : E → V) (a : ResidualArc l u f) : V :=
  Sum.elim head tail a.val

/-- The length of a residual arc is the original cost forward and its negative in reverse. -/
noncomputable def ResidualArc.cost (c : E → ℝ) (a : ResidualArc l u f) : ℝ :=
  Sum.elim c (-c) a.val

/-- A price at each vertex making the reduced cost of every active residual arc nonnegative. -/
def IsResidualPotential (tail head : E → V) (l u f c : E → ℝ) (π : V → ℝ) : Prop :=
  ∀ a : ResidualArc l u f, 0 ≤ a.cost c + π (a.tail tail head) - π (a.head tail head)

section Balance

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- For flows of equal balances, adding a potential difference to each cost leaves the
cost gap unchanged. No feasibility inequalities or sign conditions are needed here. -/
theorem cost_sub_eq_sum_reducedCost (tail head : E → V) (c f g : E → ℝ) (π : V → ℝ)
    (hbal : (incidenceMatrix tail head) *ᵥ g = (incidenceMatrix tail head) *ᵥ f) :
    c ⬝ᵥ g - c ⬝ᵥ f = ∑ e, (c e + π (tail e) - π (head e)) * (g e - f e) := by
  have hz : π ⬝ᵥ ((incidenceMatrix tail head) *ᵥ (g - f)) = 0 := by
    rw [mulVec_sub, hbal, sub_self, dotProduct_zero]
  rw [dotProduct_mulVec, ← mulVec_transpose] at hz
  simp only [dotProduct, ArcNetworkLaplacian.incidenceMatrix_transpose_mulVec_apply,
    Pi.sub_apply] at hz
  calc c ⬝ᵥ g - c ⬝ᵥ f = (∑ e, c e * (g e - f e)) -
        ∑ e, (π (head e) - π (tail e)) * (g e - f e) := by
          rw [hz, sub_zero]; simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring

/-- On finite vertex and arc sets, a feasible flow admitting a residual potential minimizes real
arc cost among all flows with the same bounds and balances. -/
theorem minimumCost_of_residualPotential {tail head : E → V} {b : V → ℝ} {c : E → ℝ}
    {π : V → ℝ} (hf : l ≤ f ∧ f ≤ u ∧ (incidenceMatrix tail head) *ᵥ f = b)
    (hπ : IsResidualPotential tail head l u f c π) :
    ∀ g, l ≤ g ∧ g ≤ u ∧ (incidenceMatrix tail head) *ᵥ g = b → c ⬝ᵥ f ≤ c ⬝ᵥ g := by
  intro g hg
  apply sub_nonneg.mp
  rw [cost_sub_eq_sum_reducedCost tail head c f g π (hg.2.2.trans hf.2.2.symm)]
  refine Finset.sum_nonneg fun e _ => ?_
  rcases lt_trichotomy (f e) (g e) with h | h | h
  · have ha := hπ ⟨.inl e, forward_capacity_pos.mpr (h.trans_le (hg.2.1 e))⟩
    exact mul_nonneg ha (sub_nonneg.mpr h.le)
  · simp [h]
  · have ha := hπ ⟨.inr e, reverse_capacity_pos.mpr ((hg.1 e).trans_lt h)⟩
    change 0 ≤ -c e + π (head e) - π (tail e) at ha
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (sub_nonpos.mpr h.le)

end Balance

/-- A nonempty directed closed arc walk whose arrival vertices are all distinct. This includes
one-arc loops; the base vertex occurs as the final arrival, not as an extra initial entry. -/
def IsElementaryCycle (tail head : E → V) (v : V) (p : List E) : Prop :=
  p ≠ [] ∧ IsArcWalk tail head v v p ∧ (p.map head).Nodup

section Walks

variable {tail head : E → V} {w : E → ℝ}

/-- Erase elementary circuits without increasing the cost, keeping both endpoints. -/
private theorem erase_cycles (hc : ∀ v p, IsElementaryCycle tail head v p → 0 ≤ (p.map w).sum)
    {s t : V} {p : List E} (hp : IsArcWalk tail head s t p) :
    ∃ q, IsArcWalk tail head s t q ∧ (s :: q.map head).Nodup ∧ (q.map w).sum ≤ (p.map w).sum := by
  classical
  induction p generalizing s with
  | nil => exact ⟨[], hp, by simp, le_rfl⟩
  | cons a p ih =>
    obtain ⟨hs, hp'⟩ := walk_cons_pair hp
    obtain ⟨q, hq, hsimple, hle⟩ := ih hp'
    have hwalk := walk_cons_mk hs hq
    have hheads : ((a :: q).map head).Nodup := hsimple
    have hcost : ((a :: q).map w).sum ≤ ((a :: p).map w).sum := by
      simpa using add_le_add_left hle (w a)
    by_cases hvisit : s ∈ (a :: q).map head
    · -- The start reappears as an arrival. The prefix ending at that arrival is elementary.
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hvisit
      obtain ⟨left, right, hcut⟩ := List.append_of_mem he
      have hsplit : a :: q = (left ++ [e]) ++ right := by simpa using hcut
      rw [hsplit] at hwalk
      obtain ⟨m, hloop, hright⟩ := walk_append hwalk
      have hm : s = m := heq ▸ hloop.2.2.2 e (by simp)
      subst m
      have hnd := hheads
      rw [hsplit, List.map_append] at hnd
      have hnonneg := hc s (left ++ [e]) ⟨by simp, hloop, hnd.of_append_left⟩
      refine ⟨right, hright, ?_, ?_⟩
      · rw [hcut, List.map_append] at hheads
        simpa only [List.map_cons, heq] using hheads.of_append_right
      · rw [hsplit, List.map_append, List.sum_append] at hcost
        linarith
    · exact ⟨a :: q, hwalk, List.nodup_cons.mpr ⟨hvisit, hheads⟩, hcost⟩

/-- Minimum over walks *starting anywhere* and ending at `t`. The empty walk ensures
nonemptiness even at an isolated vertex. After erasure only finitely many arc lists matter. -/
private theorem exists_least_walk [Finite E]
    (hc : ∀ v p, IsElementaryCycle tail head v p → 0 ≤ (p.map w).sum) (t : V) :
    ∃ s p, IsArcWalk tail head s t p ∧
      ∀ s' q, IsArcWalk tail head s' t q → (p.map w).sum ≤ (q.map w).sum := by
  classical
  let := Fintype.ofFinite E
  let paths := (Finset.univ : Finset {p : List E // p.Nodup}).filter
    (fun p => ∃ s, IsArcWalk tail head s t p.val)
  have hmem (p : {p : List E // p.Nodup}) : p ∈ paths ↔ ∃ s, IsArcWalk tail head s t p.val := by
    simp [paths]
  have hne : paths.Nonempty := ⟨⟨[], by simp⟩, (hmem _).mpr ⟨t, walk_nil⟩⟩
  obtain ⟨p, hp, hmin⟩ := paths.exists_min_image (fun p => (p.val.map w).sum) hne
  obtain ⟨s, hs⟩ := (hmem _).mp hp
  refine ⟨s, p.val, hs, fun s' q hq => ?_⟩
  obtain ⟨r, hr, hsimple, hle⟩ := erase_cycles hc hq
  let r' : {p : List E // p.Nodup} := ⟨r, List.Nodup.of_map head (List.nodup_cons.mp hsimple).2⟩
  exact (hmin r' ((hmem _).mpr ⟨s', hr⟩)).trans hle

end Walks

/-- Suppose the original arc set is finite. If no elementary directed cycle in the
positive-capacity residual network has negative cost, there is a potential with nonnegative
reduced cost on every residual arc. The vertex type need not be finite, and no single source
need reach every vertex. -/
theorem exists_residualPotential_of_no_negative_cycle [Finite E] {tail head : E → V} {c : E → ℝ}
    (hc : ∀ v (p : List (ResidualArc l u f)),
      IsElementaryCycle (ResidualArc.tail tail head) (ResidualArc.head tail head) v p →
      0 ≤ (p.map (ResidualArc.cost c)).sum) :
    ∃ π, IsResidualPotential tail head l u f c π := by
  classical
  choose s p hp hleast using exists_least_walk hc
  refine ⟨fun v => ((p v).map (ResidualArc.cost c)).sum, fun a => ?_⟩
  have hext := walk_snoc (hp (a.tail tail head)) (a := a) rfl
  have hle := hleast (a.head tail head) _ _ hext
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero] at hle
  linarith

end MathlibExt.Combinatorics.Graph.ArcNetwork.MinCostFlow
