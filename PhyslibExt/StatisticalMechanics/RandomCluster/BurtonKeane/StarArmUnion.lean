/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestCount

/-!
# Unions of arm segments

Finite arm segments lying in a tree form an acyclic graph; arms starting at three distinct
neighbours of each hub give degree three there and leaves at the arm ends.

## i. Overview

`bgf3_G ray len` is the graph formed by the first `len α` edges of each arm `ray α`. If every
segment lies in a tree, the union is acyclic. If arms are injective, start at hubs with three
distinct first steps per hub, and end in `B`, then hubs have degree at least three, interior arm
vertices degree at least two, and every leaf lies in `B`. The star on four vertices is the basic
example.

## ii. Key results

- `bgf3_acyclic` : arm segments inside a tree form an acyclic graph
- `bgf3_deg3` : hubs have degree at least three
- `bgf3_leaves_on_boundary` : leaves lie at the arm ends
- `bgf3_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

/-! ## A. Definitions -/

/-- The first `len α` edges of each arm `ray α`. -/
def bgf3_armEdges {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ) : Set (Sym2 V) :=
  {e | ∃ (α : Arm) (k : ℕ), k < len α ∧ e = s(ray α k, ray α (k + 1))}

/-- The graph formed by the arm segments. -/
def bgf3_G {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (bgf3_armEdges ray len)

/-! ## B. Results -/

lemma bgf3_adj_iff {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ) (u v : V) :
    (bgf3_G ray len).Adj u v ↔
      (∃ (α : Arm) (k : ℕ), k < len α ∧ s(u, v) = s(ray α k, ray α (k + 1))) ∧ u ≠ v := by
  unfold bgf3_G bgf3_armEdges
  rw [SimpleGraph.fromEdgeSet_adj]
  rfl

lemma bgf3_adj_step {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    (α : Arm) {k : ℕ} (hk : k < len α) (hne : ray α k ≠ ray α (k + 1)) :
    (bgf3_G ray len).Adj (ray α k) (ray α (k + 1)) := by
  rw [bgf3_adj_iff]
  exact ⟨⟨α, k, hk, rfl⟩, hne⟩

lemma bgf3_le_tree {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    (T : SimpleGraph V) (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) :
    bgf3_G ray len ≤ T := by
  intro u v huv
  rw [bgf3_adj_iff] at huv
  obtain ⟨⟨α, k, hk, hek⟩, -⟩ := huv
  rw [Sym2.eq_iff] at hek
  rcases hek with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadjT α k hk
  · exact (hadjT α k hk).symm

lemma bgf3_acyclic {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    {T : SimpleGraph V} (hT : T.IsTree)
    (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) :
    (bgf3_G ray len).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (bgf3_le_tree ray len T hadjT)

lemma bgf3_two_le_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a b : V} (hab : a ≠ b) (ha : G.Adj v a) (hb : G.Adj v b) : 2 ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : 1 < (G.neighborFinset v).card :=
    Finset.one_lt_card_iff.mpr
      ⟨a, b, by rw [SimpleGraph.mem_neighborFinset]; exact ha,
        by rw [SimpleGraph.mem_neighborFinset]; exact hb, hab⟩
  omega

lemma bgf3_three_le_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) : 3 ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : 2 < (G.neighborFinset v).card :=
    Finset.two_lt_card_iff.mpr
      ⟨a, b, c, by rw [SimpleGraph.mem_neighborFinset]; exact ha,
        by rw [SimpleGraph.mem_neighborFinset]; exact hb,
        by rw [SimpleGraph.mem_neighborFinset]; exact hc, hab, hac, hbc⟩
  omega

lemma bgf3_interior_two_le {V : Type*} [Fintype V] {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    [DecidableRel (bgf3_G ray len).Adj]
    (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
    (α : Arm) {j : ℕ} (hj0 : 0 < j) (hjlen : j < len α) :
    2 ≤ (bgf3_G ray len).degree (ray α j) := by
  have hle1 : j - 1 ≤ len α := by omega
  have hlej : j ≤ len α := by omega
  have hle2 : j + 1 ≤ len α := by omega
  have hstep1 : (bgf3_G ray len).Adj (ray α j) (ray α (j - 1)) := by
    have hk : j - 1 < len α := by omega
    have hsucc : j - 1 + 1 = j := by omega
    have hne : ray α (j - 1) ≠ ray α (j - 1 + 1) := by
      rw [hsucc]; intro h; exact absurd (hinj α (by exact hle1) (by exact hlej) h) (by omega)
    have := bgf3_adj_step ray len α hk hne
    rw [hsucc] at this
    exact this.symm
  have hstep2 : (bgf3_G ray len).Adj (ray α j) (ray α (j + 1)) := by
    have hne : ray α j ≠ ray α (j + 1) := by
      intro h; exact absurd (hinj α (by exact hlej) (by exact hle2) h) (by omega)
    exact bgf3_adj_step ray len α hjlen hne
  have hnab : ray α (j - 1) ≠ ray α (j + 1) := by
    intro h; exact absurd (hinj α (by exact hle1) (by exact hle2) h) (by omega)
  exact bgf3_two_le_degree (bgf3_G ray len) hnab hstep1 hstep2

lemma bgf3_deg3 {V : Type*} [Fintype V] {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    [DecidableRel (bgf3_G ray len).Adj]
    (hlen : ∀ α, 1 ≤ len α) (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
    {ι : Type*} (f : ι → V) (arm3 : ι → Fin 3 → Arm)
    (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
    (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1)
    (i : ι) : 3 ≤ (bgf3_G ray len).degree (f i) := by
  have hadj : ∀ j : Fin 3, (bgf3_G ray len).Adj (f i) (ray (arm3 i j) 1) := by
    intro j
    have h0 : (0 : ℕ) < len (arm3 i j) := hlen (arm3 i j)
    have hmem0 : (0 : ℕ) ∈ {n | n ≤ len (arm3 i j)} := Nat.zero_le _
    have hmem1 : (1 : ℕ) ∈ {n | n ≤ len (arm3 i j)} := h0
    have hne : ray (arm3 i j) 0 ≠ ray (arm3 i j) (0 + 1) := by
      simp only [Nat.zero_add]
      intro h
      exact absurd (hinj (arm3 i j) hmem0 hmem1 h) (by omega)
    have := bgf3_adj_step ray len (arm3 i j) h0 hne
    rw [harm3start i j] at this
    simpa using this
  exact bgf3_three_le_degree (bgf3_G ray len)
    (harm3dist i 0 1 (by decide)) (harm3dist i 0 2 (by decide)) (harm3dist i 1 2 (by decide))
    (hadj 0) (hadj 1) (hadj 2)

lemma bgf3_min_deg1 {V : Type*} [Fintype V] {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ)
    [DecidableRel (bgf3_G ray len).Adj]
    (hlen : ∀ α, 1 ≤ len α) (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
    (hcover : ∀ v, ∃ (α : Arm) (j : ℕ), j ≤ len α ∧ ray α j = v)
    (v : V) : 1 ≤ (bgf3_G ray len).degree v := by
  obtain ⟨α, j, hj, rfl⟩ := hcover v
  rcases Nat.lt_or_ge j (len α) with hjlt | hjge
  · have hne : ray α j ≠ ray α (j + 1) := by
      intro h
      exact absurd (hinj α (show j ≤ len α by omega) (show j + 1 ≤ len α by omega) h) (by omega)
    exact StatMech.Percolation.spc_deg_ge_one (bgf3_G ray len) _ _ (bgf3_adj_step ray len α hjlt hne)
  · have hjeq : j = len α := le_antisymm hj hjge
    have hk : j - 1 < len α := by have := hlen α; omega
    have hsucc : j - 1 + 1 = j := by have := hlen α; omega
    have hne : ray α (j - 1) ≠ ray α (j - 1 + 1) := by
      rw [hsucc]
      intro h
      exact absurd (hinj α (show j - 1 ≤ len α by omega) (show j ≤ len α by omega) h) (by omega)
    have hadj := bgf3_adj_step ray len α hk hne
    rw [hsucc] at hadj
    exact StatMech.Percolation.spc_deg_ge_one (bgf3_G ray len) _ _ hadj.symm

lemma bgf3_leaves_on_boundary {V : Type*} [Fintype V] {Arm : Type*}
    (ray : Arm → ℕ → V) (len : Arm → ℕ) [DecidableRel (bgf3_G ray len).Adj]
    (hlen : ∀ α, 1 ≤ len α) (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
    {B : Finset V} (htip : ∀ α, ray α (len α) ∈ B)
    {ι : Type*} (f : ι → V) (arm3 : ι → Fin 3 → Arm)
    (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
    (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1)
    (hhub : ∀ α, ∃ i, ray α 0 = f i)
    {v : V} (hdeg : (bgf3_G ray len).degree v = 1) : v ∈ B := by
  by_contra hvB
  have hpos : 0 < (bgf3_G ray len).degree v := by omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rw [SimpleGraph.mem_neighborFinset] at ha
  rw [bgf3_adj_iff] at ha
  obtain ⟨⟨α, k, hk, hek⟩, hne⟩ := ha
  rw [Sym2.eq_iff] at hek
  have hinterior : ∀ (β : Arm) (j : ℕ), 0 < j → j < len β → v = ray β j → False := by
    intro β j hj0 hjlt hvj
    have h2 : 2 ≤ (bgf3_G ray len).degree v := by
      rw [hvj]; exact bgf3_interior_two_le ray len hinj β hj0 hjlt
    omega
  have hhubcase : ∀ (β : Arm), v = ray β 0 → False := by
    intro β hv0
    obtain ⟨i, hi⟩ := hhub β
    have hvfi : v = f i := by rw [hv0, hi]
    have h3 : 3 ≤ (bgf3_G ray len).degree v := by
      rw [hvfi]
      exact bgf3_deg3 ray len hlen hinj f arm3 harm3start harm3dist i
    omega
  rcases hek with ⟨hv, ha'⟩ | ⟨hv, ha'⟩
  · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact hhubcase α (by rw [hv, hk0])
    · exact hinterior α k hkpos hk hv
  · rcases Nat.lt_or_ge (k + 1) (len α) with hlt | hge
    · exact hinterior α (k + 1) (Nat.succ_pos k) hlt hv
    · have hjeq : k + 1 = len α := le_antisymm hk hge
      apply hvB
      rw [hv, hjeq]
      exact htip α

lemma bgf3_count {V : Type*} [Fintype V] [Nonempty V] {Arm : Type*}
    (ray : Arm → ℕ → V) (len : Arm → ℕ) [DecidableRel (bgf3_G ray len).Adj]
    {T : SimpleGraph V} (hT : T.IsTree)
    (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1)))
    (hlen : ∀ α, 1 ≤ len α) (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
    (hcover : ∀ v, ∃ (α : Arm) (j : ℕ), j ≤ len α ∧ ray α j = v)
    {B : Finset V} (htip : ∀ α, ray α (len α) ∈ B)
    {ι : Type*} [Fintype ι] (f : ι → V) (hf : Function.Injective f) (arm3 : ι → Fin 3 → Arm)
    (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
    (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1)
    (hhub : ∀ α, ∃ i, ray α 0 = f i) :
    Fintype.card ι ≤ B.card :=
  bfk_forestCount (bgf3_G ray len)
    (bgf3_acyclic ray len hT hadjT)
    (bgf3_min_deg1 ray len hlen hinj hcover)
    f hf
    (fun i => bgf3_deg3 ray len hlen hinj f arm3 harm3start harm3dist i)
    B
    (fun v hv => bgf3_leaves_on_boundary ray len hlen hinj htip f arm3 harm3start harm3dist hhub hv)

/-- Three arms of length one from the centre `0` of a four-vertex star. -/
def bgf3_starRay : Fin 3 → ℕ → Fin 4 := fun j n => if n = 0 then 0 else (![1, 2, 3] : Fin 3 → Fin 4) j

/-- Every star arm has length one. -/
def bgf3_starLen : Fin 3 → ℕ := fun _ => 1

lemma bgf3_star_witness :
    Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
  classical
  have : DecidableRel (bgf3_G bgf3_starRay bgf3_starLen).Adj := Classical.decRel _
  refine bgf3_count bgf3_starRay bgf3_starLen bau_star_witness.1 ?_ ?_ ?_ ?_ ?_
    (fun _ => (0 : Fin 4)) ?_ (fun _ j => j) ?_ ?_ ?_
  · intro j k hk
    simp only [bgf3_starLen] at hk
    interval_cases k
    fin_cases j <;> (simp only [bgf3_starRay]; decide)
  · intro j; simp [bgf3_starLen]
  · intro j n hn m hm hnm
    simp only [Set.mem_ofPred_eq, bgf3_starLen] at hn hm
    simp only [bgf3_starRay] at hnm
    interval_cases n <;> interval_cases m <;> fin_cases j <;> simp_all
  · intro v
    fin_cases v
    · exact ⟨0, 0, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨0, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨1, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨2, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
  · intro j; simp only [bgf3_starLen, bgf3_starRay]; fin_cases j <;> decide
  · intro a b _; exact Subsingleton.elim a b
  · intro i j; simp [bgf3_starRay]
  · intro i j j' hjj'; simp only [bgf3_starRay]; fin_cases j <;> fin_cases j' <;> simp_all
  · intro α; exact ⟨0, by simp [bgf3_starRay]⟩

/-! ## C. Summary -/

lemma bgf3_status :
    (∀ {V : Type} {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ) {T : SimpleGraph V},
      T.IsTree → (∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) →
      (bgf3_G ray len).IsAcyclic) ∧
    (∀ {V : Type} [Fintype V] {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ)
        [DecidableRel (bgf3_G ray len).Adj],
      (∀ α, 1 ≤ len α) → (∀ α, Set.InjOn (ray α) {n | n ≤ len α}) →
      ∀ {B : Finset V}, (∀ α, ray α (len α) ∈ B) →
      ∀ {ι : Type} (f : ι → V) (arm3 : ι → Fin 3 → Arm),
      (∀ i j, ray (arm3 i j) 0 = f i) →
      (∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1) →
      (∀ α, ∃ i, ray α 0 = f i) →
      ∀ {v : V}, (bgf3_G ray len).degree v = 1 → v ∈ B) ∧
    (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V Arm ray len T hT hadjT; exact bgf3_acyclic ray len hT hadjT
  · intro V _ Arm ray len _ hlen hinj B htip ι f arm3 h1 h2 h3 v hv
    exact bgf3_leaves_on_boundary ray len hlen hinj htip f arm3 h1 h2 h3 hv
  · exact bgf3_star_witness

end StatMech.Walls
