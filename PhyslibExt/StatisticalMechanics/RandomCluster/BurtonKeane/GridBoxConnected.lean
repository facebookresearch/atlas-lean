/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentConn

/-!
# Opening all edges of a box

Forcing every edge of `B_n` open joins all sites of the box into one cluster.

## i. Overview

`boxEdges d n` is the finite set of lattice edges with both ends in `B_n`. After `forceOpenFinset
(boxEdges d n)`, any two sites of the box are connected: one changes coordinates one at a time along
`mixSite x y k`, which stays in the box. Hence all sites of the box share one cluster. This is the
geometric input for finite-energy merging.

## ii. Key results

- `mem_boxEdges_iff` : membership in `boxEdges`
- `connected_mixSite` : the coordinate interpolation is connected after opening the box
- `box_allOpen_connected` : any two sites of the box are connected
- `box_allOpen_cluster_eq` : all sites of the box have the same cluster

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}


/-! ## A. Definitions -/

open Classical in
/-- The lattice edges with both endpoints in the box `B_n`. -/
noncomputable def boxEdges (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (((boxFinsetBK d n) ×ˢ (boxFinsetBK d n)).filter
      (fun p => (hypercubicLattice d).Adj p.1 p.2)).image (fun p => s(p.1, p.2))

/-! ## B. Results -/

lemma mk_mem_boxEdges {n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hadj : (hypercubicLattice d).Adj x y) :
    s(x, y) ∈ boxEdges d n := by
  classical
  unfold boxEdges
  rw [Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj⟩ <;>
    · simp only [boxFinsetBK, Set.Finite.mem_toFinset]; assumption

lemma mem_boxEdges_iff {n : ℕ} {x y : Site d} :
    s(x, y) ∈ boxEdges d n ↔
      x ∈ box d n ∧ y ∈ box d n ∧ (hypercubicLattice d).Adj x y := by
  classical
  constructor
  · intro h
    unfold boxEdges at h
    rw [Finset.mem_image] at h
    obtain ⟨⟨a, b⟩, hab, he⟩ := h
    rw [Finset.mem_filter, Finset.mem_product] at hab
    rcases hab with ⟨⟨ha, hb⟩, hadj⟩
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simpa [boxFinsetBK] using ha,
        by simpa [boxFinsetBK] using hb, hadj⟩
    · exact ⟨by simpa [boxFinsetBK] using hb,
        by simpa [boxFinsetBK] using ha, hadj.symm⟩
  · rintro ⟨hx, hy, hxy⟩
    exact mk_mem_boxEdges hx hy hxy

lemma adj_forceOpen_boxEdges {n : ℕ} (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hadj : (hypercubicLattice d).Adj x y) :
    (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Adj x y := by
  rw [openSubgraph_adj]
  exact ⟨hadj, forceOpenFinset_of_mem (mk_mem_boxEdges hx hy hadj) ω⟩

lemma update_mem_box {n : ℕ} {x : Site d} (hx : x ∈ box d n) (j : Fin d) {a : ℤ}
    (ha : a.natAbs ≤ n) : Function.update x j a ∈ box d n := by
  intro i
  by_cases hij : i = j
  · subst hij; rwa [Function.update_self]
  · rw [Function.update_of_ne hij]; exact hx i

lemma connected_update_ascend {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) :
    ∀ (k : ℕ) (a : ℤ), a.natAbs ≤ n → (a + (k : ℤ)).natAbs ≤ n →
      Connected d (forceOpenFinset (boxEdges d n) ω)
        (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
  set ω' := forceOpenFinset (boxEdges d n) ω with hω'
  intro k
  induction k with
  | zero => intro a _ _; simpa using connected_rfl
  | succ m ih =>
    intro a ha hak
    have hint : (a + (m : ℤ)).natAbs ≤ n := by
      have h1 := ha; have h2 := hak; push_cast at h2 ⊢; omega
    have hstep : Connected d ω' (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := by
      refine SimpleGraph.Adj.reachable
        (adj_forceOpen_boxEdges ω (update_mem_box hx j hint)
          (update_mem_box hx j ?_) (adj_update_succ x j (a + (m : ℤ))))
      have : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact hak
    have hrec := (ih a ha hint).trans hstep
    have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [he] at hrec

lemma connected_update {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) {a : ℤ} (ha : a.natAbs ≤ n) :
    Connected d (forceOpenFinset (boxEdges d n) ω) x (Function.update x j a) := by
  have hxj : (x j).natAbs ≤ n := hx j
  have hxupd : Function.update x j (x j) = x := Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    subst hk
    have hconn := connected_update_ascend ω hx j k (x j) hxj ha
    rwa [hxupd] at hconn
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have hconn := connected_update_ascend ω hx j k a ha (by rw [hk]; exact hxj)
    rw [hk, hxupd] at hconn
    exact hconn.symm

/-- The site whose first `k` coordinates are those of `y` and the rest those of `x`. -/
def mixSite (x y : Site d) (k : ℕ) : Site d :=
  fun i => if (i : ℕ) < k then y i else x i

@[simp] lemma mixSite_zero (x y : Site d) : mixSite x y 0 = x := by
  funext i; simp [mixSite]

@[simp] lemma mixSite_full (x y : Site d) : mixSite x y d = y := by
  funext i; simp [mixSite, i.isLt]

lemma mixSite_mem_box {n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    (k : ℕ) : mixSite x y k ∈ box d n := by
  intro i
  simp only [mixSite]
  by_cases h : (i : ℕ) < k
  · rw [ite_eq_left h]; exact hy i
  · rw [ite_eq_right h]; exact hx i

lemma mixSite_succ {x y : Site d} {k : ℕ} (hk : k < d) :
    mixSite x y (k + 1) = Function.update (mixSite x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext i
  by_cases hik : i = ⟨k, hk⟩
  · subst hik; simp [mixSite, Function.update_self]
  · rw [Function.update_of_ne hik]
    simp only [mixSite]
    have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
    by_cases h : (i : ℕ) < k
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

lemma connected_mixSite {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    ∀ k ≤ d, Connected d (forceOpenFinset (boxEdges d n) ω) x (mixSite x y k) := by
  intro k
  induction k with
  | zero => intro _; rw [mixSite_zero]
  | succ m ih =>
    intro hsucc
    have hm : m < d := by omega
    have hmle : m ≤ d := by omega
    have h1 := ih hmle
    have hstep : Connected d (forceOpenFinset (boxEdges d n) ω)
        (mixSite x y m) (mixSite x y (m + 1)) := by
      rw [mixSite_succ hm]
      exact connected_update ω (mixSite_mem_box hx hy m) ⟨m, hm⟩ (hy ⟨m, hm⟩)
    exact h1.trans hstep

lemma box_allOpen_connected {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    Connected d (forceOpenFinset (boxEdges d n) ω) x y := by
  have h := connected_mixSite ω hx hy d le_rfl
  rwa [mixSite_full] at h

lemma box_allOpen_reachable {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Reachable x y :=
  box_allOpen_connected ω hx hy

lemma box_allOpen_oneCluster {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) :
    box d n ⊆ cluster d (forceOpenFinset (boxEdges d n) ω) x := by
  intro y hy
  rw [mem_cluster]
  exact box_allOpen_connected ω hx hy

lemma box_allOpen_cluster_eq {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    cluster d (forceOpenFinset (boxEdges d n) ω) x
      = cluster d (forceOpenFinset (boxEdges d n) ω) y :=
  cluster_eq_of_connected (box_allOpen_connected ω hx hy)

end Percolation

end StatMech
