/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import CSLibExt.Algorithms.Lean.Graph.MaxFlowMinCut

/-!
# Integral arc networks

Integral endpoint-class splitting, the integral lift of dense feasible flows to
arc flows, and the integral arc max-flow min-cut theorem: under natural arc
capacities, a natural arc flow attains the maximum signed source value over all
real arc-feasible flows and meets an `s`-`t` out-cut.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Graph.ArcNetworkIntegral

/-- Bounded natural split of a sum: if `n` does not exceed the sum of `c` over a
finset, some `g ≤ c` sums to exactly `n` over that finset. -/
private theorem exists_nat_split_finset {ι : Type*} (c : ι → ℕ)
    (s : Finset ι) (n : ℕ) (hn : n ≤ ∑ i ∈ s, c i) :
    ∃ g : ι → ℕ, (∀ i ∈ s, g i ≤ c i) ∧ ∑ i ∈ s, g i = n := by
  classical
  refine Finset.induction (motive := fun s => ∀ n, n ≤ ∑ i ∈ s, c i →
    ∃ g : ι → ℕ, (∀ i ∈ s, g i ≤ c i) ∧ ∑ i ∈ s, g i = n) ?_ ?_ s n hn
  · intro n hn
    have hn0 : n = 0 := by simpa using hn
    exact ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i), by simp [hn0]⟩
  · intro a s ha ih n hn
    rw [Finset.sum_insert ha] at hn
    by_cases hle : n ≤ ∑ i ∈ s, c i
    · obtain ⟨g', hg'le, hg'sum⟩ := ih n hle
      refine ⟨fun i => if i = a then 0 else g' i, ?_, ?_⟩
      · intro i hi
        change (if i = a then (0 : ℕ) else g' i) ≤ c i
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · rw [ite_eq_left rfl]
          exact Nat.zero_le _
        · rw [ite_eq_right (by intro h; rw [h] at hi; exact ha hi)]
          exact hg'le i hi
      · rw [Finset.sum_insert ha]
        change (if a = a then (0 : ℕ) else g' a) +
          (∑ i ∈ s, (if i = a then (0 : ℕ) else g' i)) = n
        have h1 : (if a = a then (0 : ℕ) else g' a) = 0 := ite_eq_left rfl
        have h2 : (∑ i ∈ s, (if i = a then (0 : ℕ) else g' i)) = ∑ i ∈ s, g' i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply ite_eq_right
          intro h
          rw [h] at hi
          exact ha hi
        rw [h1, h2, hg'sum, zero_add]
    · have hle' : n - ∑ i ∈ s, c i ≤ c a := by omega
      refine ⟨fun i => if i = a then n - ∑ i ∈ s, c i else c i, ?_, ?_⟩
      · intro i hi
        change (if i = a then n - ∑ i ∈ s, c i else c i) ≤ c i
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · rw [ite_eq_left rfl]
          exact hle'
        · rw [ite_eq_right (by intro h; rw [h] at hi; exact ha hi)]
      · rw [Finset.sum_insert ha]
        change (if a = a then n - ∑ i ∈ s, c i else c a) +
          (∑ i ∈ s, (if i = a then n - ∑ i ∈ s, c i else c i)) = n
        have h1 : (if a = a then n - ∑ i ∈ s, c i else c a) = n - ∑ i ∈ s, c i :=
          ite_eq_left rfl
        have h2 : (∑ i ∈ s, (if i = a then n - ∑ i ∈ s, c i else c i)) = ∑ i ∈ s, c i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply ite_eq_right
          intro h
          rw [h] at hi
          exact ha hi
        rw [h1, h2]
        omega

/-- Dense feasibility pulls back along a vertex equivalence. -/
private theorem isFeasibleFlow_pullback {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (capV : V → V → ℝ) (capF : Fin n → Fin n → ℝ)
    (hcap : ∀ i j, capF i j = capV (e.symm i) (e.symm j))
    (f : Fin n → Fin n → ℝ) (s t : V)
    (hf : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow capF (e s) (e t) f) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow capV s t
      (fun p q => f (e p) (e q)) := by
  obtain ⟨hnn, hle, hcons⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    exact hnn (e p) (e q)
  · intro p q
    have h := hle (e p) (e q)
    rw [hcap] at h
    simp only [e.symm_apply_apply] at h
    exact h
  · intro v hvs hvt
    have hc := hcons (e v) (fun h => hvs (e.injective h)) (fun h => hvt (e.injective h))
    have hl : (∑ u : V, f (e u) (e v)) = ∑ i : Fin n, f i (e v) :=
      e.sum_comp (fun i => f i (e v))
    have hr : (∑ w : V, f (e v) (e w)) = ∑ j : Fin n, f (e v) j :=
      e.sum_comp (fun j => f (e v) j)
    change (∑ u : V, f (e u) (e v)) = ∑ w : V, f (e v) (e w)
    rw [hl, hr]
    exact hc

/-- Dense feasibility pushes forward along a vertex equivalence. -/
private theorem isFeasibleFlow_pushforward {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (capV : V → V → ℝ) (capF : Fin n → Fin n → ℝ)
    (hcap : ∀ i j, capF i j = capV (e.symm i) (e.symm j))
    (G : V → V → ℝ) (s t : V)
    (hG : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow capV s t G) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow capF (e s) (e t)
      (fun i j => G (e.symm i) (e.symm j)) := by
  obtain ⟨hnn, hle, hcons⟩ := hG
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact hnn (e.symm i) (e.symm j)
  · intro i j
    have h := hle (e.symm i) (e.symm j)
    have hc := hcap i j
    rw [hc]
    exact h
  · intro k hk1 hk2
    have hks : e.symm k ≠ s := by
      intro hcon
      apply hk1
      calc k = e (e.symm k) := (e.apply_symm_apply k).symm
        _ = e s := by rw [hcon]
    have hkt : e.symm k ≠ t := by
      intro hcon
      apply hk2
      calc k = e (e.symm k) := (e.apply_symm_apply k).symm
        _ = e t := by rw [hcon]
    have hc := hcons (e.symm k) hks hkt
    have hl : (∑ i : Fin n, G (e.symm i) (e.symm k)) = ∑ u : V, G u (e.symm k) :=
      e.symm.sum_comp (fun u => G u (e.symm k))
    have hr : (∑ j : Fin n, G (e.symm k) (e.symm j)) = ∑ w : V, G (e.symm k) w :=
      e.symm.sum_comp (fun w => G (e.symm k) w)
    change (∑ i : Fin n, G (e.symm i) (e.symm k)) = ∑ j : Fin n, G (e.symm k) (e.symm j)
    rw [hl, hr]
    exact hc

/-- Dense flow value is invariant under pullback along a vertex equivalence. -/
private theorem flowValue_pullback {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (f : Fin n → Fin n → ℝ) (s : V) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s (fun p q => f (e p) (e q)) =
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue (e s) f := by
  change (∑ w : V, f (e s) (e w)) - (∑ u : V, f (e u) (e s)) =
    (∑ j : Fin n, f (e s) j) - ∑ i : Fin n, f i (e s)
  have hl : (∑ w : V, f (e s) (e w)) = ∑ j : Fin n, f (e s) j :=
    e.sum_comp (fun j => f (e s) j)
  have hr : (∑ u : V, f (e u) (e s)) = ∑ i : Fin n, f i (e s) :=
    e.sum_comp (fun i => f i (e s))
  rw [hl, hr]

/-- Dense flow value is invariant under pushforward along a vertex equivalence. -/
private theorem flowValue_pushforward {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (G : V → V → ℝ) (s : V) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue (e s)
        (fun i j => G (e.symm i) (e.symm j)) =
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s G := by
  change (∑ j : Fin n, G (e.symm (e s)) (e.symm j)) - (∑ i : Fin n, G (e.symm i) (e.symm (e s))) =
    (∑ w : V, G s w) - ∑ u : V, G u s
  simp only [e.symm_apply_apply]
  have hl : (∑ j : Fin n, G s (e.symm j)) = ∑ w : V, G s w :=
    e.symm.sum_comp (fun w => G s w)
  have hr : (∑ i : Fin n, G (e.symm i) s) = ∑ u : V, G u s :=
    e.symm.sum_comp (fun u => G u s)
  rw [hl, hr]

/-- Integral class split: a natural dense flow bounded pointwise by aggregated
natural capacities is the aggregate of a natural arc flow within the capacities. -/
theorem exists_nat_split {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℕ) (F : V → V → ℕ)
    (hle : ∀ p q, (F p q : ℝ) ≤
      MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e => (u e : ℝ)) p q) :
    ∃ g : E → ℕ, (∀ e, g e ≤ u e) ∧
      MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e => (g e : ℝ)) =
        fun p q => (F p q : ℝ) := by
  have hbound : ∀ p q, F p q ≤
      ∑ e ∈ Finset.univ.filter (fun e => tail e = p ∧ head e = q), u e := by
    intro p q
    have h := hle p q
    simp only [MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate] at h
    rw [← Nat.cast_sum] at h
    exact Nat.cast_le.mp h
  choose g hle' hsum using fun p q => exists_nat_split_finset u _ (F p q) (hbound p q)
  refine ⟨fun e => g (tail e) (head e) e, ?_, ?_⟩
  · intro e
    exact hle' (tail e) (head e) e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩)
  · funext p q
    change MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head
      (fun e => ((g (tail e) (head e) e : ℕ) : ℝ)) p q = (F p q : ℝ)
    simp only [MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate]
    have hcongr : ∀ e ∈ Finset.univ.filter (fun e => tail e = p ∧ head e = q),
        ((g (tail e) (head e) e : ℕ) : ℝ) = ((g p q e : ℕ) : ℝ) := by
      intro e he
      rw [Finset.mem_filter] at he
      rw [he.2.1, he.2.2]
    have h1 : (∑ e ∈ Finset.univ.filter (fun e => tail e = p ∧ head e = q),
        ((g (tail e) (head e) e : ℕ) : ℝ)) =
        ∑ e ∈ Finset.univ.filter (fun e => tail e = p ∧ head e = q),
        ((g p q e : ℕ) : ℝ) :=
      Finset.sum_congr rfl hcongr
    rw [h1, ← Nat.cast_sum, hsum p q]

/-- Integral arc lift: a natural dense feasible flow lifts to a natural arc flow
that is arc-feasible, aggregates back to the dense flow, and keeps the signed
source value. -/
theorem exists_nat_arc_lift {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℕ) (s t : V) (F : V → V → ℕ)
    (hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e => (u e : ℝ))) s t
      (fun p q => (F p q : ℝ))) :
    ∃ g : E → ℕ,
      MathlibExt.Combinatorics.Graph.ArcNetwork.IsArcFeasible tail head (fun e => (u e : ℝ)) s t
        (fun e => (g e : ℝ)) ∧
      MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e => (g e : ℝ)) =
        (fun p q => (F p q : ℝ)) ∧
      -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
          (fun e => (g e : ℝ)) s) =
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s
          (fun p q => (F p q : ℝ)) := by
  obtain ⟨-, hcap, hcons⟩ := hF
  obtain ⟨g, hgle, hagg⟩ := exists_nat_split tail head u F (fun p q => hcap p q)
  refine ⟨g, ⟨?_, ?_, ?_⟩, hagg, ?_⟩
  · intro e
    exact Nat.cast_nonneg _
  · intro e
    exact Nat.cast_le.mpr (hgle e)
  · intro v hvs hvt
    have h := MathlibExt.Combinatorics.Graph.ArcNetwork.flowValue_aggregate_eq_neg_mulVec
      tail head (fun e => (g e : ℝ)) v
    rw [hagg] at h
    have hval : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue v
        (fun p q => (F p q : ℝ)) = 0 := by
      change (∑ w : V, (F v w : ℝ)) - (∑ u_1 : V, (F u_1 v : ℝ)) = 0
      rw [sub_eq_zero]
      exact (hcons v hvs hvt).symm
    rw [hval] at h
    exact neg_eq_zero.mp h.symm
  · have h := MathlibExt.Combinatorics.Graph.ArcNetwork.flowValue_aggregate_eq_neg_mulVec
      tail head (fun e => (g e : ℝ)) s
    rw [hagg] at h
    exact h.symm

/-- Integral arc max-flow min-cut: under natural arc capacities with `s ≠ t`, a
natural arc flow is arc-feasible, maximizes the signed source value over all real
arc-feasible flows, is bounded by every `s`-`t` out-cut, and attains some `s`-`t`
out-cut. -/
theorem exists_nat_arc_max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (u : E → ℕ) (s t : V) (hst : s ≠ t) :
    ∃ g : E → ℕ,
      MathlibExt.Combinatorics.Graph.ArcNetwork.IsArcFeasible tail head (fun e => (u e : ℝ)) s t
        (fun e => (g e : ℝ)) ∧
      (∀ f' : E → ℝ,
        MathlibExt.Combinatorics.Graph.ArcNetwork.IsArcFeasible tail head (fun e => (u e : ℝ)) s t
          f' →
        -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec f' s) ≤
        -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
          (fun e => (g e : ℝ)) s)) ∧
      (∀ S : Finset V,
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsSTCut s t S →
        -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
          (fun e => (g e : ℝ)) s) ≤
        ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), (u e : ℝ)) ∧
      (∃ S : Finset V,
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsSTCut s t S ∧
        -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
          (fun e => (g e : ℝ)) s) =
        ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), (u e : ℝ)) := by
  set e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hst' : e s ≠ e t := fun h => hst (e.injective h)
  set Cfin : Fin (Fintype.card V) → Fin (Fintype.card V) → ℕ :=
    fun i j => ∑ e_1 ∈ Finset.univ.filter
      (fun e_2 => tail e_2 = e.symm i ∧ head e_2 = e.symm j), u e_1 with hCfin
  obtain ⟨f, hf, hmax⟩ :=
    Cslib.Algorithms.Lean.Graph.MaxFlowMinCut.exists_nat_max_flow Cfin hst'
  have hcap : ∀ i j, Cslib.Algorithms.Lean.Graph.MaxFlowMinCut.realCap Cfin i j =
      MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e_1 => (u e_1 : ℝ))
        (e.symm i) (e.symm j) := by
    intro i j
    simp only [Cslib.Algorithms.Lean.Graph.MaxFlowMinCut.realCap, hCfin,
      MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate, Nat.cast_sum]
  have hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head (fun e_1 => (u e_1 : ℝ))) s t
      (fun p q => ((f (e p) (e q) : ℕ) : ℝ)) :=
    isFeasibleFlow_pullback e _ _ hcap _ s t hf
  obtain ⟨g, hgfeas, hagg, hval⟩ :=
    exists_nat_arc_lift tail head u s t (fun p q => f (e p) (e q)) hF
  have hval' : -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
        (fun e_1 => (g e_1 : ℝ)) s) =
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s
        (fun p q => ((f (e p) (e q) : ℕ) : ℝ)) := hval
  have hmax' : ∀ f' : E → ℝ,
      MathlibExt.Combinatorics.Graph.ArcNetwork.IsArcFeasible tail head
        (fun e_1 => (u e_1 : ℝ)) s t f' →
      -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec f' s) ≤
      -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
        (fun e_1 => (g e_1 : ℝ)) s) := by
    intro f' hf'
    have haggfeas := MathlibExt.Combinatorics.Graph.ArcNetwork.isFeasibleFlow_aggregate
      tail head (fun e_1 => (u e_1 : ℝ)) f' s t hf'
    have hpush := isFeasibleFlow_pushforward e _ _ hcap _ s t haggfeas
    have hle := hmax _ hpush
    have hpushval := flowValue_pushforward e
      (MathlibExt.Combinatorics.Graph.ArcNetwork.aggregate tail head f') s
    rw [hpushval] at hle
    have hR : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue (e s)
          (fun u_1 v => ((f u_1 v : ℕ) : ℝ)) =
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s
          (fun p q => ((f (e p) (e q) : ℕ) : ℝ)) :=
      (flowValue_pullback e (fun u_1 v => ((f u_1 v : ℕ) : ℝ)) s).symm
    rw [hR] at hle
    have haggval := MathlibExt.Combinatorics.Graph.ArcNetwork.flowValue_aggregate_eq_neg_mulVec
      tail head f' s
    rw [haggval, ← hval'] at hle
    exact hle
  have hcapnn : ∀ e_1 : E, (0 : ℝ) ≤ (u e_1 : ℝ) := fun e_1 => Nat.cast_nonneg _
  obtain ⟨fstar, hstarfeas, hstarmax, hstarcut_le, Sstar, hSstar, hStareq⟩ :=
    MathlibExt.Combinatorics.Graph.ArcNetwork.arc_max_flow_min_cut tail head
      (fun e_1 => (u e_1 : ℝ)) hcapnn s t hst
  have heq : -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec
        (fun e_1 => (g e_1 : ℝ)) s) =
      -((MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head).mulVec fstar s) :=
    le_antisymm (hstarmax _ hgfeas) (hmax' _ hstarfeas)
  refine ⟨g, hgfeas, hmax', ?_, ?_⟩
  · intro S hS
    rw [heq]
    exact hstarcut_le S hS
  · exact ⟨Sstar, hSstar, by rw [heq]; exact hStareq⟩

end Cslib.Algorithms.Lean.Graph.ArcNetworkIntegral
