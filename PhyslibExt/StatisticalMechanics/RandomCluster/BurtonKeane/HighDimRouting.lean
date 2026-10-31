/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentConn
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Axis corridors and trifurcations in dimension at least three

In `d ≥ 3` three coordinate axes give disjoint open corridors from the origin, which route three
infinite clusters to a trifurcation precursor.

## i. Overview

`hrHD_rayPt j t` is the site `t e_j` and `hrHD_corridorEdges j L` the edges of the axis segment from
`0` to `L e_j`. Segments along distinct axes meet only at the origin. If every configuration with
three distinct infinite clusters meeting `B_n` can be completed by finitely many opened edges to a
neighbour trifurcation precursor (`hrHD_DisjointRouting`), finite-energy merging gives positive
probability of a trifurcation precursor, and the counting route of
`burton_keane_uniqueness_trif_route` applies.

## ii. Key results

- `hrHD_rayPt_disjoint_of_ne` : rays along distinct axes meet only at the origin
- `hrHD_corridor_connected_one_to_L` : an opened corridor connects `e_j` to `L e_j`
- `hrHD_route_of_routing` : disjoint routing gives the trifurcation route
- `hrHD_exists_three_independent_axes` : `d ≥ 3` provides three distinct axes
- `hrHD_burton_keane_uniqueness_dim_ge_three` : uniqueness from disjoint routing and a
  configuration-wide trifurcation bound

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The site `t e_j` on the `j`-th coordinate axis. -/
def hrHD_rayPt {d : ℕ} (j : Fin d) (t : ℤ) : Site d := Pi.single j t

/-! ## B. Results -/

@[simp] lemma hrHD_rayPt_self (j : Fin d) (t : ℤ) : hrHD_rayPt j t j = t := by simp [hrHD_rayPt]

lemma hrHD_rayPt_of_ne (j : Fin d) (t : ℤ) {i : Fin d} (h : i ≠ j) : hrHD_rayPt j t i = 0 := by
  simp [hrHD_rayPt, Pi.single_eq_of_ne h]

@[simp] lemma hrHD_rayPt_zero (j : Fin d) : hrHD_rayPt j 0 = (0 : Site d) := by
  funext i; by_cases h : i = j <;> simp [hrHD_rayPt, h, Pi.single_eq_of_ne]

lemma hrHD_rayPt_eq_zero_iff (j : Fin d) (t : ℤ) : hrHD_rayPt j t = (0 : Site d) ↔ t = 0 := by
  constructor
  · intro h; have := congrFun h j; simpa using this
  · rintro rfl; simp

lemma hrHD_adj_rayPt (j : Fin d) (t : ℤ) :
    (hypercubicLattice d).Adj (hrHD_rayPt j t) (hrHD_rayPt j (t + 1)) := by
  have h := adj_update_succ (0 : Site d) j t
  have e1 : Function.update (0 : Site d) j t = hrHD_rayPt j t := by
    funext i; by_cases hij : i = j <;> simp [hij, hrHD_rayPt, Pi.single, Function.update]
  have e2 : Function.update (0 : Site d) j (t + 1) = hrHD_rayPt j (t + 1) := by
    funext i; by_cases hij : i = j <;> simp [hij, hrHD_rayPt, Pi.single, Function.update]
  rwa [e1, e2] at h

lemma hrHD_adj_origin_rayPt_one (j : Fin d) :
    (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1) := by
  have h := hrHD_adj_rayPt j 0
  simpa using h

lemma hrHD_rayPt_one_ne_of_ne {i j : Fin d} (h : i ≠ j) :
    (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 := by
  intro he
  have hh := congrFun he i
  rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j 1 h] at hh
  exact one_ne_zero hh

lemma hrHD_rayPt_disjoint_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
  intro he
  have hh := congrFun he i
  rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j t h] at hh
  exact hs hh

/-- The edges of the axis segment from `0` to `L e_j`. -/
noncomputable def hrHD_corridorEdges (j : Fin d) (L : ℕ) : Finset (Sym2 (Site d)) :=
  (Finset.range L).image (fun t : ℕ => s(hrHD_rayPt j (t : ℤ), hrHD_rayPt j ((t : ℤ) + 1)))

lemma hrHD_mem_corridorEdges {j : Fin d} {L : ℕ} {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j (t : ℤ), hrHD_rayPt j ((t : ℤ) + 1)) ∈ hrHD_corridorEdges j L := by
  rw [hrHD_corridorEdges, Finset.mem_image]; exact ⟨t, Finset.mem_range.mpr ht, rfl⟩

lemma hrHD_origin_notMem_rayEdge (j : Fin d) (s : ℤ) (hs : 1 ≤ s) :
    (0 : Site d) ∉ s(hrHD_rayPt j s, hrHD_rayPt j (s + 1)) := by
  simp only [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega

lemma hrHD_corridor_step_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (s : ℕ)
    (h1 : 1 ≤ s) (hsL : s < L) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω))
      (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
  refine ⟨hrHD_adj_rayPt j (s : ℤ), ?_⟩
  have hmem : s(hrHD_rayPt j (s : ℤ), hrHD_rayPt j ((s : ℤ) + 1)) ∈ hrHD_corridorEdges j L :=
    hrHD_mem_corridorEdges hsL
  have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j (s : ℤ), hrHD_rayPt j ((s : ℤ) + 1)) :=
    hrHD_origin_notMem_rayEdge j (s : ℤ) (by exact_mod_cast h1)
  rw [removeSite_apply_of_notMem hno0, forceOpenFinset_of_mem hmem]

lemma hrHD_corridor_connected_one_to_L (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hL : 1 ≤ L) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
  set ω' := removeSite (0 : Site d) (forceOpenFinset (hrHD_corridorEdges j L) ω) with hω'
  suffices H : ∀ m : ℕ, 1 ≤ m → m ≤ L → Connected d ω' (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) by
    have := H L hL le_rfl; simpa using this
  intro m
  induction m with
  | zero => intro h; omega
  | succ p ih =>
    intro _ hpL
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · have hp1 : 1 ≤ p := by omega
      have hppL : p < L := by omega
      have hstep : IsOpenEdge d ω' (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        hrHD_corridor_step_open ω j L p hp1 hppL
      have hrec : Connected d ω' (hrHD_rayPt j 1) (hrHD_rayPt j (p : ℤ)) := ih hp1 (by omega)
      have hgoal := hrec.trans hstep.connected
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hgoal
    · have hp1 : p + 1 = 1 := by omega
      rw [hp1]; simpa using connected_rfl

lemma hrHD_precursor_of_removeSite_conditions
    (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hc; exact hdist.1 (cluster_eq_of_connected hc)
  · intro hc; exact hdist.2.1 (cluster_eq_of_connected hc)
  · intro hc; exact hdist.2.2 (cluster_eq_of_connected hc)

/-- Disjoint routing in `B_n`: every configuration with three distinct infinite clusters meeting
`B_n` becomes a neighbour trifurcation precursor after opening finitely many edges. -/
def hrHD_DisjointRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
    forceOpenFinset G ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃

/-- Index of a route: the opened edge set and the three neighbours of the origin. -/
abbrev hrHD_RouteIdx (d : ℕ) := Finset (Sym2 (Site d)) × Site d × Site d × Site d

/-- Configurations that become the neighbour trifurcation precursor of the route after its edges are
opened. -/
noncomputable def hrHD_routePre (p : hrHD_RouteIdx d) : Set (ConfigSpace (Sym2 (Site d))) :=
  (fun ω => forceOpenFinset p.1 ω) ⁻¹' (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)

lemma hrHD_threeMeetBox_subset_iUnion_routePre {n : ℕ} (hrt : hrHD_DisjointRouting d n) :
    threeMeetBox d n ⊆ ⋃ p : hrHD_RouteIdx d, hrHD_routePre p := by
  intro ω hω
  obtain ⟨G, a₁, a₂, a₃, hpre⟩ := hrt ω hω
  exact Set.mem_iUnion.mpr ⟨(G, a₁, a₂, a₃), hpre⟩

lemma hrHD_route_step
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (n : ℕ) (hrt : hrHD_DisjointRouting d n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ p : hrHD_RouteIdx d, μ (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2) = 0 := by
    intro p; exact le_antisymm (hcon p.2.1 p.2.2.1 p.2.2.2) bot_le
  have hpre0 : ∀ p : hrHD_RouteIdx d, μ (hrHD_routePre p) = 0 := by
    intro p
    have hpush : (μ.map (fun ω => forceOpenFinset p.1 ω))
          (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)
        = μ ((fun ω => forceOpenFinset p.1 ω) ⁻¹'
            (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)) :=
      Measure.map_apply (measurable_forceOpenFinset p.1)
        (DisjointPaths.measurableSet_neighborTrifPrecursor _ _ _)
    have hnull : μ ((fun ω => forceOpenFinset p.1 ω) ⁻¹'
        (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)) = 0 := by
      rw [← hpush]; exact (hfe p.1) (hzero p)
    exact hnull
  have hsum : (∑' p : hrHD_RouteIdx d, μ (hrHD_routePre p)) = 0 := by
    simp only [hpre0, tsum_zero]
  have hunion0 : μ (⋃ p : hrHD_RouteIdx d, hrHD_routePre p) = 0 := by
    refine le_antisymm ?_ bot_le
    exact le_trans (measure_iUnion_le (μ := μ) (fun p => hrHD_routePre p)) (le_of_eq hsum)
  have hle : μ (threeMeetBox d n) ≤ μ (⋃ p : hrHD_RouteIdx d, hrHD_routePre p) :=
    measure_mono (hrHD_threeMeetBox_subset_iUnion_routePre hrt)
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)

lemma hrHD_route_of_routing
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  intro n hpos
  exact hrHD_route_step μ hfe n (hrt n) hpos

lemma hrHD_exists_three_independent_axes (hd : 3 ≤ d) :
    ∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;>
    · intro h; simp [Fin.ext_iff] at h

lemma hrHD_axis_corridor_branches
    (ω : ConfigSpace (Sym2 (Site d))) {j₁ j₂ j₃ : Fin d}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (L : ℕ) (hL : 1 ≤ L) :
    (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧
     hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧ hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧
    ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) ∧
    (Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω))
        (hrHD_rayPt j₁ 1) (hrHD_rayPt j₁ (L : ℤ)) ∧
      Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω))
        (hrHD_rayPt j₂ 1) (hrHD_rayPt j₂ (L : ℤ)) ∧
      Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω))
        (hrHD_rayPt j₃ 1) (hrHD_rayPt j₃ (L : ℤ))) := by
  refine ⟨⟨hrHD_rayPt_one_ne_of_ne h12, hrHD_rayPt_one_ne_of_ne h13, hrHD_rayPt_one_ne_of_ne h23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    ?_, ?_, ?_, ?_⟩
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h12 hs
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h13 hs
  · exact fun s t hs => hrHD_rayPt_disjoint_of_ne h23 hs
  · exact ⟨hrHD_corridor_connected_one_to_L ω j₁ L hL,
      hrHD_corridor_connected_one_to_L ω j₂ L hL,
      hrHD_corridor_connected_one_to_L ω j₃ L hL⟩

/-- Burton–Keane uniqueness in dimension `d ≥ 3` from disjoint routing (Burton and Keane, *Density
and uniqueness in percolation*, 1989). The hypotheses `hbound` (a trifurcation bound for every
configuration) and `hdens` (bound over volume tends to `0`) cannot both hold when `d ≥ 1`: see
`tfc_not_hbound_hdens`. So the statement is vacuous. -/
theorem hrHD_burton_keane_uniqueness_dim_ge_three
    (hd : 3 ≤ d)
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  ⟨hrHD_exists_three_independent_axes hd,
    burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
      (hrHD_route_of_routing μ hfe hrt)⟩

end Percolation

end StatMech
