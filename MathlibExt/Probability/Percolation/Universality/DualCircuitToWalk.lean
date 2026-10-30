/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour
public import MathlibExt.Probability.Percolation.Universality.BoxCrossingDichotomy

/-!
# Barrier edges of the left-reach set and the rotated barrier graph

A *barrier edge* of `rect 0 n 0 n` is a lattice edge `{v, w}` inside the square with `v` in the
left-reach set `bcd_leftReach ω n` and `w` not in it. Barrier edges are closed, so their quarter
turns are open in the rotated dual configuration `dualConfig ω`. The *rotated barrier graph* has
these quarter turns as edges; it is a subgraph of the `dualConfig ω`-open graph, so a walk in it
gives a crossing in `dualConfig ω`.

The barrier graph lives in the rotated square `rect (-n) 0 0 n`, which meets `rect 0 n 0 n` only
in the column `x = 0`. Consequently a *barrier route* (a barrier walk from the bottom to the top
side of `rect 0 n 0 n` inside that square, `dcw_BarrierRoute`) is very restrictive, and the
hypothesis of `dcw_square_dichotomy` (a barrier route whenever there is no horizontal crossing)
is false for every `n ≥ 2` (`bcc_square_dichotomy_hyp_false`). The rotated-square version is
`dcp_DualCutConnectsRot`.

## Main definitions

* `StatMech.Universality.dcw_isBarrierEdge`: an in-square edge from the left-reach set to its
  complement.
* `StatMech.Universality.dcw_dualBarrierGraph`: the quarter turns of the barrier edges, as a
  graph on `ℤ²`.
* `StatMech.Universality.dcw_BarrierRoute`: a barrier walk from the bottom to the top side of
  `rect 0 n 0 n` staying in the square.

## Main results

* `StatMech.Universality.dcw_dualBarrierGraph_le_open`: the rotated barrier graph is contained in
  the `dualConfig ω`-open graph.
* `StatMech.Universality.dcw_dualVerticalCrossing_of_route`: a barrier route gives a vertical
  crossing of `rect 0 n 0 n` in `dualConfig ω`.
* `StatMech.Universality.dcw_barrierEdge_exists`: without a horizontal crossing there is a
  barrier edge on the bottom row.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}

/-- `{v, w}` is a barrier edge of `rect 0 n 0 n`: a lattice edge with `v` in the left-reach set
and `w` in the square but not in the left-reach set. -/
def dcw_isBarrierEdge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (v w : Site 2) : Prop :=
  v ∈ bcd_leftReach ω n ∧ w ∈ rect 0 n 0 n ∧ w ∉ bcd_leftReach ω n ∧
    (hypercubicLattice 2).Adj v w

theorem dcw_barrier_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : ω s(v, w) = false :=
  bcd_leftReach_boundary_closed ω n h.1 h.2.1 h.2.2.2 h.2.2.1

theorem dcw_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : dualConfig ω (crossEdge s(v, w)) = true :=
  bcd_leftReach_boundary_dual_open ω n h.1 h.2.1 h.2.2.2 h.2.2.1

/-- The quarter turn of a barrier edge is an edge of the `dualConfig ω`-open graph. -/
theorem dcw_barrier_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
  refine ⟨?_, ?_⟩
  · exact (rot90_adj v w).mpr h.2.2.2
  · have := dcw_barrier_dual_open ω n h
    rwa [crossEdge_mk] at this

theorem dcw_leftSide_in_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) :
    x ∈ bcd_leftReach ω n := by
  refine ⟨leftSide_subset hx, x, hx, leftSide_subset hx, ?_⟩
  exact connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩

theorem dcw_rightSide_notin_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ rightSide 0 n 0 n) :
    y ∉ bcd_leftReach ω n :=
  (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hy

/-- Without a horizontal crossing, deleting the edge boundary of the left-reach set disconnects
the left side from the right side of `ℤ²`. -/
theorem dcw_barrier_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcd_leftReach ω n)
    (dcw_leftSide_in_L ω n hx) (dcw_rightSide_notin_L ω n hnoH hy)

/-- Without a horizontal crossing, every lattice walk from the left side to the right side
crosses the edge boundary of the left-reach set an odd number of times. An instance of
`crossCount_odd_of_separated`. -/
theorem dcw_leftRight_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (bcd_leftReach ω n) w) :=
  crossCount_odd_of_separated (bcd_leftReach ω n)
    (dcw_leftSide_in_L ω n hx) (dcw_rightSide_notin_L ω n hnoH hy) w

/-- The rotated barrier graph: `p` and `q` are adjacent when `{p, q}` is the quarter turn
`{rot90Fun v, rot90Fun w}` of a barrier edge `{v, w}`. It is the image of
`pdc_barrierGraphPrimal` under `rot90Fun` (`pdc_rot90Iso`). -/
def dcw_dualBarrierGraph (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj p q :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((p = rot90Fun v ∧ q = rot90Fun w) ∨ (p = rot90Fun w ∧ q = rot90Fun v))
  symm := by
    refine ⟨?_⟩
    rintro p q ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · exact ⟨v, w, hvw, Or.inr ⟨hq, hp⟩⟩
    · exact ⟨v, w, hvw, Or.inl ⟨hq, hp⟩⟩
  loopless := by
    refine ⟨fun p hp => ?_⟩
    have hinj : Function.Injective rot90Fun := rot90Equiv.injective
    rcases hp with ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq)
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq.symm)

theorem dcw_dualBarrierGraph_le_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n ≤ openSubgraph 2 (dualConfig ω) := by
  rintro p q ⟨v, w, hvw, hpq⟩
  have hopen : (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
    dcw_barrier_dualAdj ω n hvw
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]; exact hopen
  · rw [hp, hq]; exact hopen.symm

/-- A rotated barrier walk viewed as a `dualConfig ω`-open walk. -/
def dcw_dualBarrier_walk_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (c : (dcw_dualBarrierGraph ω n).Walk p q) :
    (openSubgraph 2 (dualConfig ω)).Walk p q :=
  c.mapLe (dcw_dualBarrierGraph_le_open ω n)

theorem dcw_dualBarrier_reachable_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
    (openSubgraph 2 (dualConfig ω)).Reachable p q :=
  h.mono (dcw_dualBarrierGraph_le_open ω n)

/-- A barrier route of `rect 0 n 0 n`: a walk in the rotated barrier graph from the bottom side
to the top side whose support stays in the square. Since the rotated barrier graph lies in
`rect (-n) 0 0 n`, such a walk runs along the column `x = 0`; for the all-closed configuration
and `n ≥ 2` there is none (`bcc_barrierRoute_false`). -/
def dcw_BarrierRoute (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
    (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n)
    (c : (dcw_dualBarrierGraph ω n).Walk p₀ q₀),
    ∀ u ∈ c.support, u ∈ rect 0 n 0 n

/-- A barrier route gives a vertical crossing of `rect 0 n 0 n` in `dualConfig ω`. -/
theorem dcw_dualVerticalCrossing_of_route (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hroute : dcw_BarrierRoute ω n) :
    DualVerticalCrossing ω 0 n 0 n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, hsupp⟩ := hroute
  set c' : (openSubgraph 2 (dualConfig ω)).Walk p₀ q₀ := dcw_dualBarrier_walk_open ω n c with hc'
  have hsupp' : c'.support = c.support := by
    rw [hc', dcw_dualBarrier_walk_open, SimpleGraph.Walk.support_mapLe_eq_support]
  have hsuppbox : ∀ u ∈ c'.support, u ∈ rect 0 n 0 n := by
    intro u hu; rw [hsupp'] at hu; exact hsupp u hu
  refine ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩, ?_⟩
  exact walk_induce_reachable (openSubgraph 2 (dualConfig ω)) (rect 0 n 0 n) c'
    hsuppbox (bottomSide_subset hp₀) (topSide_subset hq₀)

/-- If every configuration without a horizontal crossing of `rect 0 n 0 n` has a barrier route,
then every such configuration has a vertical crossing of the same square in `dualConfig ω`.

This is **not** the box-crossing dichotomy. The hypothesis is false for every `n ≥ 2`
(`bcc_square_dichotomy_hyp_false`), and for `n = 2` the conclusion itself is false
(`bcc_dichotomy_false`), because `dualConfig` is the dual only up to a quarter turn. The statement
is non-vacuous only for `n ≤ 1`. -/
theorem dcw_square_dichotomy (n : ℤ)
    (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
  intro ω hω
  rw [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
  rw [mem_dualVerticalCrossingEvent]
  exact dcw_dualVerticalCrossing_of_route ω n (hroute ω hω)

/-- Without a horizontal crossing of `rect 0 n 0 n` (`n ≥ 0`), some edge of the bottom row is a
barrier edge: the first site `(k, 0)` outside the left-reach set and its left neighbor. -/
theorem dcw_barrierEdge_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = 0 ∧ w 1 = 0 := by
  classical
  have hbl : (![0, 0] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨⟨by simp, by simpa using hn, by simp, by simpa using hn⟩, by simp⟩
  have hbr : (![n, 0] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨⟨by simpa using hn, by simp, by simp, by simpa using hn⟩, by simp⟩
  set P : ℕ → Prop := fun k => (![(k:ℤ), 0] : Site 2) ∈ bcd_leftReach ω n with hP
  have hP0 : P 0 := by simpa [hP] using hbl
  have hPn : ¬ P n.toNat := by
    have : ((n.toNat : ℤ)) = n := by omega
    simpa [hP, this] using hbr
  have hex : ∃ k, ¬ P k := ⟨n.toNat, hPn⟩
  set k := Nat.find hex with hk
  have hkfail : ¬ P k := Nat.find_spec hex
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkfail; exact absurd hP0 hkfail
    · exact h0
  have hkprev : P (k - 1) := by
    by_contra hcon
    have : k ≤ k - 1 := Nat.find_le hcon
    omega
  refine ⟨![((k:ℤ) - 1), 0], ![(k:ℤ), 0], ?_, by simp, by simp⟩
  have hv : (![((k:ℤ) - 1), 0] : Site 2) ∈ bcd_leftReach ω n := by
    have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
    rw [hP] at hkprev; rwa [hcast] at hkprev
  refine ⟨hv, ?_, ?_, ?_⟩
  · have hvbox : (![((k:ℤ) - 1), 0] : Site 2) ∈ rect 0 n 0 n := hv.1
    rw [mem_rect] at hvbox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvbox ⊢
    refine ⟨by omega, ?_, le_refl 0, hn⟩
    have hkle : k ≤ n.toNat := Nat.find_le hPn
    omega
  · simpa [hP] using hkfail
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

theorem dcw_dualBarrierGraph_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q := by
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨rot90Fun v, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩

end Universality

end StatMech
