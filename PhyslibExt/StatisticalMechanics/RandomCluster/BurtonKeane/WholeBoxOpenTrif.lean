/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifNeighbourReach
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

/-!
# Opening the whole box does not create a classical trifurcation

Opening every edge of a box reconnects the neighbours of the origin, so it never makes the origin a
classical trifurcation; a finite modification making the origin a classical trifurcation gives
disjoint routing.

## i. Overview

`bc58_boxOpen d k ω` forces every edge of `B_k` open. Its neighbours of the origin are then
connected around the origin, so the origin is not a classical trifurcation of the opened
configuration. `bc58_OriginTrifModification d n` asks that every configuration in `threeMeetBox d n`
become one with a classical trifurcation at the origin after opening finitely many edges; it gives
disjoint routing and uniqueness for Bernoulli percolation. The even-lines configuration is an
example.

## ii. Key results

- `bc58_reconnect_around_origin` : opening the box reconnects the neighbours of the origin
- `bc58_boxOpen_not_classicalTrif` : the opened box has no classical trifurcation at the origin
- `bc58_disjointRouting_of_originTrifModification` : origin modifications give disjoint routing
- `bc58_status` : the statements together

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
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The lattice edges with both endpoints in `B_k`. -/
noncomputable def bc58_boxInternalEdges (d k : ℕ) : Finset (Sym2 (Site d)) := by
  classical
  exact (((box_finite d k).toFinset ×ˢ (box_finite d k).toFinset).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2)).image (fun p => s(p.1, p.2))

/-! ## B. Results -/

lemma bc58_mem_boxInternalEdges {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y) :
    s(x, y) ∈ bc58_boxInternalEdges d k := by
  classical
  unfold bc58_boxInternalEdges
  rw [Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj⟩ <;> rw [Set.Finite.mem_toFinset]
  · exact hx
  · exact hy

/-- The configuration `ω` with every edge of `B_k` forced open. -/
noncomputable def bc58_boxOpen (d k : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  forceOpenFinset (bc58_boxInternalEdges d k) ω

lemma bc58_boxOpen_edge_open {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    IsOpenEdge d (bc58_boxOpen d k ω) x y :=
  ⟨hadj, forceOpenFinset_of_mem (bc58_mem_boxInternalEdges hx hy hadj) ω⟩

lemma bc58_boxOpen_adj_connected {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    Connected d (bc58_boxOpen d k ω) x y :=
  IsOpenEdge.connected (bc58_boxOpen_edge_open hx hy hadj ω)

lemma bc58_boxOpen_removeSite_edge_open {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (h0 : (0 : Site d) ∉ s(x, y)) (ω : ConfigSpace (Sym2 (Site d))) :
    IsOpenEdge d (removeSite 0 (bc58_boxOpen d k ω)) x y := by
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  exact forceOpenFinset_of_mem (bc58_mem_boxInternalEdges hx hy hadj) ω

lemma bc58_boxOpen_removeSite_adj_connected {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (h0 : (0 : Site d) ∉ s(x, y)) (ω : ConfigSpace (Sym2 (Site d))) :
    Connected d (removeSite 0 (bc58_boxOpen d k ω)) x y :=
  IsOpenEdge.connected (bc58_boxOpen_removeSite_edge_open hx hy hadj h0 ω)

/-- The planar site `(a, b)`. -/
def bc58_p (a b : ℤ) : Site 2 := ![a, b]

@[simp] lemma bc58_p_fst (a b : ℤ) : (bc58_p a b) 0 = a := by simp [bc58_p]
@[simp] lemma bc58_p_snd (a b : ℤ) : (bc58_p a b) 1 = b := by simp [bc58_p]

lemma bc58_p_mem_box {k : ℕ} {a b : ℤ} (ha : a.natAbs ≤ k) (hb : b.natAbs ≤ k) :
    bc58_p a b ∈ box 2 k := by
  rw [mem_box]; intro i; fin_cases i
  · change ((bc58_p a b) 0).natAbs ≤ k; rw [bc58_p_fst]; exact ha
  · change ((bc58_p a b) 1).natAbs ≤ k; rw [bc58_p_snd]; exact hb

lemma bc58_p_adj_horiz (a b : ℤ) :
    (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p (a + 1) b) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]

lemma bc58_p_adj_vert (a b : ℤ) :
    (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p a (b + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]

lemma bc58_origin_eq : (0 : Site 2) = bc58_p 0 0 := by
  funext i; fin_cases i <;> simp [bc58_p]

lemma bc58_p_eq_origin_iff {a b : ℤ} : bc58_p a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [bc58_origin_eq]
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp only [bc58_p_fst, bc58_p_snd] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]

lemma bc58_origin_notMem_edge {a b c e : ℤ}
    (h1 : ¬ (a = 0 ∧ b = 0)) (h2 : ¬ (c = 0 ∧ e = 0)) :
    (0 : Site 2) ∉ s(bc58_p a b, bc58_p c e) := by
  rw [Sym2.mem_iff]
  rintro (h | h)
  · exact h1 ((bc58_p_eq_origin_iff).mp h.symm)
  · exact h2 ((bc58_p_eq_origin_iff).mp h.symm)

lemma bc58_reconnect_around_origin {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0) := by
  have hk1 : (1 : ℤ).natAbs ≤ k := by simpa using hk
  have hkm1 : ((-1 : ℤ)).natAbs ≤ k := by simpa using hk
  have hk0 : (0 : ℤ).natAbs ≤ k := by simp
  have m10 : bc58_p 1 0 ∈ box 2 k := bc58_p_mem_box hk1 hk0
  have m11 : bc58_p 1 1 ∈ box 2 k := bc58_p_mem_box hk1 hk1
  have m01 : bc58_p 0 1 ∈ box 2 k := bc58_p_mem_box hk0 hk1
  have mm11 : bc58_p (-1) 1 ∈ box 2 k := bc58_p_mem_box hkm1 hk1
  have mm10 : bc58_p (-1) 0 ∈ box 2 k := bc58_p_mem_box hkm1 hk0
  have s1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p 1 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact bc58_boxOpen_removeSite_adj_connected m10 m11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω
  have s2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 1) (bc58_p 0 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p 0 1) (bc58_p 1 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected m01 m11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  have s3 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 1) (bc58_p (-1) 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p (-1) 1) (bc58_p 0 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected mm11 m01 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  have s4 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p (-1) 1) (bc58_p (-1) 0) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p (-1) 0) (bc58_p (-1) 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected mm10 mm11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  exact (s1.trans s2).trans (s3.trans s4)

/-- Every configuration with three distinct infinite clusters meeting `B_n` has a finite
modification with a classical trifurcation at the origin. -/
def bc58_OriginTrifModification (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ G : Finset (Sym2 (Site d)),
    bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0

lemma bc58_disjointRouting_of_originTrifModification {n : ℕ}
    (h : bc58_OriginTrifModification d n) : hrHD_DisjointRouting d n := by
  intro ω hω
  obtain ⟨G, a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := h ω hω
  exact ⟨G, a₁, a₂, a₃, hne, ⟨he1.1, he2.1, he3.1⟩, ⟨hi1, hi2, hi3⟩, hsep⟩

lemma bc58_hroute_of_originTrifModification
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hrHD_route_of_routing μ hfe (fun n => bc58_disjointRouting_of_originTrifModification (hmod n))

lemma bc58_burton_keane_bernoulli_of_originTrifModification (hd : 1 ≤ d)
    (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc54_burton_keane_bernoulli hd p hp1 hp0
    (bc58_hroute_of_originTrifModification (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
      (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hmod)

lemma bc58_origin_nbr_cases {a : Site 2} (hadj : (hypercubicLattice 2).Adj 0 a) :
    a = bc58_p 1 0 ∨ a = bc58_p (-1) 0 ∨ a = bc58_p 0 1 ∨ a = bc58_p 0 (-1) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg] at hadj
  have key : (a 0 = 1 ∧ a 1 = 0) ∨ (a 0 = -1 ∧ a 1 = 0) ∨
      (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 0 ∧ a 1 = -1) := by omega
  have hcoord : a = bc58_p (a 0) (a 1) := by
    funext i; fin_cases i <;> simp [bc58_p]
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [hcoord, h1, h2]
  · right; left; rw [hcoord, h1, h2]
  · right; right; left; rw [hcoord, h1, h2]
  · right; right; right; rw [hcoord, h1, h2]

lemma bc58_origin_nbr_connected_to_e {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} (hadj : (hypercubicLattice 2).Adj 0 a) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a (bc58_p 1 0) := by
  have hk1 : (1 : ℤ).natAbs ≤ k := by simpa using hk
  have hkm1 : ((-1 : ℤ)).natAbs ≤ k := by simpa using hk
  have hk0 : (0 : ℤ).natAbs ≤ k := by simp
  have m10 : bc58_p 1 0 ∈ box 2 k := bc58_p_mem_box hk1 hk0
  have m11 : bc58_p 1 1 ∈ box 2 k := bc58_p_mem_box hk1 hk1
  have m01 : bc58_p 0 1 ∈ box 2 k := bc58_p_mem_box hk0 hk1
  have m1m1 : bc58_p 1 (-1) ∈ box 2 k := bc58_p_mem_box hk1 hkm1
  have m0m1 : bc58_p 0 (-1) ∈ box 2 k := bc58_p_mem_box hk0 hkm1
  rcases bc58_origin_nbr_cases hadj with h | h | h | h
  · rw [h]
  · rw [h]; exact (bc58_reconnect_around_origin hk ω).symm
  · rw [h]
    have e1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 1) (bc58_p 1 1) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 0 1) (bc58_p 1 1) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact bc58_boxOpen_removeSite_adj_connected m01 m11 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω
    have e2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 1) (bc58_p 1 0) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 1) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact (bc58_boxOpen_removeSite_adj_connected m10 m11 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
    exact e1.trans e2
  · rw [h]
    have e1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 (-1)) (bc58_p 1 (-1)) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 0 (-1)) (bc58_p 1 (-1)) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact bc58_boxOpen_removeSite_adj_connected m0m1 m1m1 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω
    have e2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 (-1)) (bc58_p 1 0) := by
      have hadj' : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 (-1)) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
      exact (bc58_boxOpen_removeSite_adj_connected m10 m1m1 hadj'
        (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
    exact e1.trans e2

lemma bc58_origin_nbrs_connected {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2)))
    {a b : Site 2} (ha : (hypercubicLattice 2).Adj 0 a) (hb : (hypercubicLattice 2).Adj 0 b) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a b :=
  (bc58_origin_nbr_connected_to_e hk ω ha).trans
    (bc58_origin_nbr_connected_to_e hk ω hb).symm

lemma bc58_boxOpen_not_classicalTrif {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0 := by
  rintro ⟨a₁, a₂, a₃, ⟨h12, _, _⟩, ⟨he1, he2, _⟩, _, ⟨hsep12, _, _⟩⟩
  exact hsep12 (bc58_origin_nbrs_connected hk ω he1.1 he2.1)

lemma bc58_wholeBoxG_not_witness {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    ¬ bc47_IsClassicalTrifurcation
        (forceOpenFinset (bc58_boxInternalEdges 2 k) ω) 0 :=
  bc58_boxOpen_not_classicalTrif hk ω

lemma bc58_evenLines_boxOpen_reconnect {k : ℕ} (hk : 1 ≤ k) :
    ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k bc57_evenLines) 0 :=
  bc58_boxOpen_not_classicalTrif hk bc57_evenLines

/-! ## C. Summary -/

lemma bc58_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    ((∀ n : ℕ, bc58_OriginTrifModification d n) →
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 0} = 1 ∨
        bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 1} = 1)
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)),
      Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0)) ∧
    (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0) ∧
    (bc57_evenLines ∈ threeMeetBox 2 6) :=
  ⟨fun hmod => bc58_burton_keane_bernoulli_of_originTrifModification hd p hp1 hp0 hmod,
   fun hk ω => bc58_reconnect_around_origin hk ω,
   fun hk ω => bc58_boxOpen_not_classicalTrif hk ω,
   bc57_mem_threeMeetBox⟩

end StatMech.Walls
