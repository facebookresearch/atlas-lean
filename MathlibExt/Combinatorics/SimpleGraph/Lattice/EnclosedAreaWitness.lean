/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingEarInduction

/-!
# Cycles in the square lattice enclose a site

Every cycle in the square lattice `ℤ²` encloses some site, in the sense of the ray count: take a
vertical edge of the cycle in the leftmost column that contains vertical edges, say from `(c, r)`
to `(c, r + 1)`; the horizontal ray going left from `(c + 1, r + 1)` crosses the cycle exactly
once. Existence of a vertical edge comes from the fact that a closed walk confined to one row
must revisit a site.

For boundary orbits this gives a winding witness whenever the face loop is a cycle and every
enclosed site belongs to `K` (`eaw_InteriorSubset`). The global hypothesis `eaw_LoopWindsRegion`,
asking this for every saturated orbit, is false: the inner orbit of the four neighbours of the
origin is saturated, and its face loop encloses the origin, which is not in the set
(`not_eaw_LoopWindsRegion`). Results that assume it are vacuous.

## Main definitions

* `StatMech.Lattice.eaw_InteriorSubset K a`: every site enclosed by the face loop of the orbit
  of `a` lies in `K`.
* `StatMech.Lattice.eaw_LoopWindsRegion`: every saturated orbit of a finite set with at least two
  sites has length at least three, no face pinches, and encloses only sites of the set (a false
  statement, see above).

## Main results

* `StatMech.Lattice.eaw_exists_vertEdge`: every cycle in `ℤ²` has a vertical edge.
* `StatMech.Lattice.eaw_rayCount_extreme`: the ray from just right of a leftmost vertical edge
  crosses the cycle once.
* `StatMech.Lattice.eaw_cycle_oddCell`: every cycle in `ℤ²` encloses a site with ray count one.
* `StatMech.Lattice.eaw_windingWitness_of_cycle_interior`: a boundary orbit whose face loop is a
  cycle enclosing only sites of `K` has a winding witness.
* `StatMech.Lattice.not_eaw_LoopWindsRegion`: the global hypothesis `eaw_LoopWindsRegion` is false.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- A closed integer sequence `g 0, …, g L = g 0` with unit steps and `L ≥ 3` cannot be injective
on `0, …, L - 1`: its maximum or minimum is attained at an interior index whose two neighbours
have the same value. -/
theorem eaw_no_monotone_loop (g : ℕ → ℤ) (L : ℕ) (h3 : 3 ≤ L)
    (hloop : g 0 = g L)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    (hne : g 1 ≠ g 0)
    (hinj : Set.InjOn g {i | i ≤ L - 1}) : False := by
  classical
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hkmem hjmem
  have machine : ∀ m, m ≤ L → (∀ i, i ≤ L → g i ≤ g m) → 0 < m → m < L → False := by
    intro m hmL hmmax hm0 hmL'
    have hs1 := hstep (m - 1) (by omega)
    have hs2 := hstep m (by omega)
    rw [show m - 1 + 1 = m by omega] at hs1
    have hle1 : g (m - 1) ≤ g m := hmmax (m - 1) (by omega)
    have hle2 : g (m + 1) ≤ g m := hmmax (m + 1) (by omega)
    have heq1 : g (m - 1) = g m - 1 := by omega
    have heq2 : g (m + 1) = g m - 1 := by omega
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by omega)
      omega
    · have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [heq1, ← heq2, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) this
      omega
  have machineMin : ∀ m, m ≤ L → (∀ i, i ≤ L → g m ≤ g i) → 0 < m → m < L → False := by
    intro m hmL hmmin hm0 hmL'
    have hs1 := hstep (m - 1) (by omega)
    have hs2 := hstep m (by omega)
    rw [show m - 1 + 1 = m by omega] at hs1
    have hle1 : g m ≤ g (m - 1) := hmmin (m - 1) (by omega)
    have hle2 : g m ≤ g (m + 1) := hmmin (m + 1) (by omega)
    have heq1 : g (m - 1) = g m + 1 := by omega
    have heq2 : g (m + 1) = g m + 1 := by omega
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by omega)
      omega
    · have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [heq1, ← heq2, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) this
      omega
  have hkmax' : ∀ i, i ≤ L → g i ≤ g k := fun i hi => hkmax i (Finset.mem_range.mpr (by omega))
  have hjmin' : ∀ i, i ≤ L → g j ≤ g i := fun i hi => hjmin i (Finset.mem_range.mpr (by omega))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hj1 : g j ≤ g 1 := hjmin' 1 (by omega)
    have hlt0 : g j < g 0 := by omega
    have hj0 : j ≠ 0 := by intro h; rw [h] at hlt0; omega
    have hjL : j ≠ L := by intro h; rw [h, ← hloop] at hlt0; omega
    exact machineMin j (by omega) hjmin' (by omega) (by omega)
  · have hk1 : g 1 ≤ g k := hkmax' 1 (by omega)
    have hgt0 : g 0 < g k := by omega
    have hk0 : k ≠ 0 := by intro h; rw [h] at hgt0; omega
    have hkL' : k ≠ L := by intro h; rw [h, ← hloop] at hgt0; omega
    exact machine k (by omega) hkmax' (by omega) (by omega)

/-- Consecutive vertices of a closed walk span an edge of the walk. See also
`SimpleGraph.Walk.mk_mem_edges_iff_exists`. -/
theorem eaw_getVert_edge_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {i : ℕ} (hi : i < Vc.length) :
    s(Vc.getVert i, Vc.getVert (i + 1)) ∈ Vc.edges :=
  Vc.mk_mem_edges_iff_exists.mpr ⟨i, hi, rfl⟩

/-- Every cycle in the square lattice has a vertical edge. -/
theorem eaw_exists_vertEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ i, i < Vc.length ∧ (Vc.getVert i) 0 = (Vc.getVert (i + 1)) 0 := by
  by_contra hcon
  push Not at hcon
  set L := Vc.length with hL
  have h3 : 3 ≤ L := hcyc.three_le_length
  have hstep1 : ∀ i, i < L → (Vc.getVert i) 1 = (Vc.getVert (i + 1)) 1 := by
    intro i hi
    have hadj := Vc.adj_getVert_succ (show i < Vc.length by rw [← hL]; exact hi)
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have hne := hcon i hi
    omega
  have hrow : ∀ i, i ≤ L → (Vc.getVert i) 1 = a 1 := by
    intro i hi
    induction i with
    | zero => rw [Vc.getVert_zero]
    | succ n ih => have hn : n < L := by omega
                   rw [← hstep1 n hn, ih (by omega)]
  set g : ℕ → ℤ := fun i => (Vc.getVert i) 0 with hg
  apply eaw_no_monotone_loop g L h3
  · change (Vc.getVert 0) 0 = (Vc.getVert L) 0
    rw [Vc.getVert_zero]
    rw [show Vc.getVert L = a from by rw [hL]; exact Vc.getVert_length]
  · intro i hi
    have hadj := Vc.adj_getVert_succ (show i < Vc.length by rw [← hL]; exact hi)
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have hne := hcon i hi
    have h1 := hstep1 i hi
    change (Vc.getVert (i + 1)) 0 = (Vc.getVert i) 0 + 1
      ∨ (Vc.getVert (i + 1)) 0 = (Vc.getVert i) 0 - 1
    omega
  · change (Vc.getVert 1) 0 ≠ (Vc.getVert 0) 0
    have h0 := hcon 0 (by omega)
    rw [Vc.getVert_zero] at h0 ⊢
    exact fun h => h0 h.symm
  · intro n hn m hm hnm
    simp only [Set.mem_ofPred_eq] at hn hm
    have hgvn : Vc.getVert n = Vc.getVert m := by
      funext t; fin_cases t
      · exact hnm
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = (1 : Fin 2) from rfl, hrow n (by omega),
          hrow m (by omega)]
    exact hcyc.getVert_injOn' (show n ≤ L - 1 by simpa [hL] using hn)
      (show m ≤ L - 1 by simpa [hL] using hm) hgvn

/-- If `(c, r)`–`(c, r + 1)` is an edge of a closed walk with no repeated edges and no vertical edge
of the walk lies left of column `c`, the ray going left from `(c + 1, r + 1)` crosses the walk
exactly once. -/
theorem eaw_rayCount_extreme {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c r : ℤ)
    (hmin : ∀ x y : Site 2, s(x, y) ∈ Vc.edges → x 0 = y 0 → c ≤ x 0)
    (he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges)
    (hnodup : Vc.edges.Nodup) :
    jec_rayCount (![c + 1, r + 1] : Site 2) Vc = 1 := by
  classical
  rw [jec_rayCount]
  have hkey : ∀ e ∈ Vc.edges,
      (decide (jec_rayEdge (![c + 1, r + 1] : Site 2) e) = true ↔
        (e == s((![c, r] : Site 2), ![c, r + 1])) = true) := by
    intro e he
    rw [decide_eq_true_eq, beq_iff_eq]
    obtain ⟨x, y⟩ := e
    have hadj : (hypercubicLattice 2).Adj x y := Vc.adj_of_mem_edges he
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨⟨hcol, hle⟩, hgap⟩
      have hge : c ≤ x 0 := hmin x y he hcol
      have hx0 : x 0 = c := by omega
      have hy0 : y 0 = c := by rw [← hcol]; exact hx0
      rcases hgap with ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩
      · have hx : x = (![c, r] : Site 2) := by funext i; fin_cases i <;> simp_all
        have hy : y = (![c, r + 1] : Site 2) := by funext i; fin_cases i <;> simp_all
        rw [hx, hy]
      · have hx : x = (![c, r + 1] : Site 2) := by funext i; fin_cases i <;> simp_all
        have hy : y = (![c, r] : Site 2) := by funext i; fin_cases i <;> simp_all
        rw [hx, hy, Sym2.eq_swap]
    · intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · subst hx; subst hy; exact ⟨⟨rfl, by simp⟩, Or.inl ⟨by simp, by simp⟩⟩
      · subst hx; subst hy; exact ⟨⟨rfl, by simp⟩, Or.inr ⟨by simp, by simp⟩⟩
  rw [List.countP_congr hkey, ← List.count]
  exact List.count_eq_one_of_mem hnodup he0

/-- Every cycle in the square lattice encloses a site: some site has ray count one. -/
theorem eaw_cycle_oddCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, jec_rayCount z Vc = 1 := by
  classical
  have hnodup : Vc.edges.Nodup := hcyc.edges_nodup
  set C : Finset ℤ :=
    ((Finset.range Vc.length).filter
      (fun i => (Vc.getVert i) 0 = (Vc.getVert (i + 1)) 0)).image (fun i => (Vc.getVert i) 0)
    with hC
  obtain ⟨i0, hi0, hi0v⟩ := eaw_exists_vertEdge Vc hcyc
  have hCne : C.Nonempty := by
    refine ⟨(Vc.getVert i0) 0, ?_⟩
    rw [hC, Finset.mem_image]
    exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0, hi0v⟩, rfl⟩
  set c : ℤ := C.min' hCne with hc
  obtain ⟨i, hiC, hic⟩ := Finset.mem_image.mp (C.min'_mem hCne)
  rw [Finset.mem_filter, Finset.mem_range] at hiC
  obtain ⟨hilen, hivert⟩ := hiC
  have hadj := Vc.adj_getVert_succ hilen
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hcol_i : (Vc.getVert i) 0 = c := hic
  have hcol_i1 : (Vc.getVert (i + 1)) 0 = c := by rw [← hivert]; exact hic
  have hrows : (Vc.getVert (i + 1)) 1 = (Vc.getVert i) 1 + 1 ∨
      (Vc.getVert (i + 1)) 1 = (Vc.getVert i) 1 - 1 := by
    rw [hcol_i, hcol_i1] at hadj; omega
  have hmin : ∀ x y : Site 2, s(x, y) ∈ Vc.edges → x 0 = y 0 → c ≤ x 0 := by
    intro x y hxy hxy0
    obtain ⟨j, hj, hje⟩ := Vc.mk_mem_edges_iff_exists.mp hxy
    rw [Sym2.eq_iff] at hje
    have hjvert : (Vc.getVert j) 0 = (Vc.getVert (j + 1)) 0 := by
      rcases hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hxy0
      · rw [h1, h2]; exact hxy0.symm
    have hjmemC : (Vc.getVert j) 0 ∈ C := by
      rw [hC, Finset.mem_image]
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjvert⟩, rfl⟩
    have hcle : c ≤ (Vc.getVert j) 0 := C.min'_le _ hjmemC
    rcases hje with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [← h1]; exact hcle
    · rw [← h2, ← hjvert]; exact hcle
  rcases hrows with hup | hdown
  · set r : ℤ := (Vc.getVert i) 1 with hr
    have hlow : Vc.getVert i = (![c, r] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i
      · change (Vc.getVert i) 1 = r; rw [hr]
    have hhigh : Vc.getVert (i + 1) = (![c, r + 1] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i1
      · change (Vc.getVert (i + 1)) 1 = r + 1
        rw [hup, hr]
    have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges := by
      rw [← hlow, ← hhigh]; exact eaw_getVert_edge_mem Vc hilen
    exact ⟨![c + 1, r + 1], eaw_rayCount_extreme Vc c r hmin he0 hnodup⟩
  · set r : ℤ := (Vc.getVert (i + 1)) 1 with hr
    have hlow : Vc.getVert (i + 1) = (![c, r] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i1
      · change (Vc.getVert (i + 1)) 1 = r; rw [hr]
    have hhigh : Vc.getVert i = (![c, r + 1] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i
      · change (Vc.getVert i) 1 = r + 1
        rw [hr]; omega
    have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges := by
      rw [Sym2.eq_swap, ← hlow, ← hhigh]; exact eaw_getVert_edge_mem Vc hilen
    exact ⟨![c + 1, r + 1], eaw_rayCount_extreme Vc c r hmin he0 hnodup⟩

/-- Every cycle in the square lattice encloses a site with odd ray count. -/
theorem eaw_cycle_oddCell' {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, ¬ Even (jec_rayCount z Vc) := by
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell Vc hcyc
  exact ⟨z, by rw [hz]; decide⟩

/-- Every site enclosed by the face loop of the orbit of `a` (odd ray count) lies in `K`. -/
def eaw_InteriorSubset (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z : Site 2, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K

/-- A boundary orbit of length at least three without face pinches, whose face loop encloses only
sites of `K`, has a winding witness. -/
theorem eaw_windingWitness_of_cycle_interior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hint : eaw_InteriorSubset K a) :
    wei_WindingWitness K a := by
  have hcyc : (mpl_orbitLoop K a).IsCycle :=
    mpl_orbitLoop_isCycle K a hp (orbitFace_injOn_of_noPinch K a hnp)
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell' (mpl_orbitLoop K a) hcyc
  exact ⟨z, hint z hz, hz⟩

/-- Every boundary orbit that probes all sites of a finite set `K` with at least two sites has
length at least three, has no face pinches, and its face loop encloses only sites of `K`.

This statement is false (`not_eaw_LoopWindsRegion`): for `K` the four neighbours of the origin and
a dart pointing into the origin, the orbit probes all of `K`, and its face loop encloses the
origin, which is not in `K`. Results assuming it are vacuous. -/
def eaw_LoopWindsRegion : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a

/-- `eaw_LoopWindsRegion` implies `wei_WindingSaturatingWitness`. Both are false
(`not_eaw_LoopWindsRegion`, `not_wei_WindingSaturatingWitness`). -/
theorem eaw_windingSaturatingWitness_of_residue (hres : eaw_LoopWindsRegion) :
    wei_WindingSaturatingWitness := by
  intro K hK hge a hsat
  obtain ⟨hp, hnp, hint⟩ := hres K hK hge a hsat
  exact eaw_windingWitness_of_cycle_interior K a hp hnp hint

/-- Under `eaw_LoopWindsRegion`, every boundary orbit of a finite nonempty star hull has a winding
witness. Vacuous: the hypothesis is false (`not_eaw_LoopWindsRegion`). -/
theorem eaw_starHull_windingWitness_of_residue (hres : eaw_LoopWindsRegion)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  wei_starHull_windingWitness_of_residue (eaw_windingSaturatingWitness_of_residue hres) K hSK hne a

/-- The ray count of a site `z` with respect to the face loop of the unit cell orbit. -/
theorem eaw_unitCell_rayCount_eq (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop unitCell ucBase)
      = (if 0 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0)
        + (if -1 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0) := by
  classical
  rw [jec_rayCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have e1 : decide (jec_rayEdge z s((![0, 0] : Site 2), ![0, -1])) =
      decide (0 ≤ z 0 - 1 ∧ z 1 = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have e2 : decide (jec_rayEdge z s((![0, -1] : Site 2), ![-1, -1])) = false := by
    rw [decide_eq_false_iff_not, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have e3 : decide (jec_rayEdge z s((![-1, -1] : Site 2), ![-1, 0])) =
      decide (-1 ≤ z 0 - 1 ∧ z 1 = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have e4 : decide (jec_rayEdge z s((![-1, 0] : Site 2), ![0, 0])) = false := by
    rw [decide_eq_false_iff_not, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [e1, e2, e3, e4, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  split_ifs <;> ring

/-- The face loop of the unit cell orbit encloses only the origin. -/
theorem eaw_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase := by
  intro z hz
  rw [eaw_unitCell_rayCount_eq z] at hz
  rw [unitCell, Set.mem_singleton_iff]
  by_contra hne
  apply hz
  by_cases hz1 : z 1 = 0
  · have hz0 : z 0 ≠ 0 := by
      intro h; exact hne (by funext i; fin_cases i <;> simp_all)
    by_cases hpos : 0 ≤ z 0 - 1
    · rw [ite_eq_left ⟨hpos, hz1⟩, ite_eq_left ⟨by omega, hz1⟩]; decide
    · rw [ite_eq_right (by tauto), ite_eq_right (by push Not; intro h; omega)]; decide
  · rw [ite_eq_right (by tauto), ite_eq_right (by tauto)]; decide

/-- The unit cell orbit satisfies the three conditions of `eaw_LoopWindsRegion` (the set has one
site, so this does not instantiate that hypothesis). -/
theorem eaw_unitCell_loopWindsRegion :
    3 ≤ dartOrbitPeriod unitCell ucBase ∧ OrbitFaceNoPinch unitCell ucBase ∧
      eaw_InteriorSubset unitCell ucBase := by
  refine ⟨?_, usc_unitCell_noPinch, eaw_unitCell_interiorSubset⟩
  rw [unitCell_orbitPeriod_eq_four]; norm_num

/-- `eaw_LoopWindsRegion` is false, since it implies the false statement
`wei_WindingSaturatingWitness`. -/
theorem not_eaw_LoopWindsRegion : ¬ eaw_LoopWindsRegion :=
  fun h => not_wei_WindingSaturatingWitness (eaw_windingSaturatingWitness_of_residue h)

end Lattice

end StatMech
