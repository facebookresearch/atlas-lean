/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.PercolationApproximation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume

/-!
# Periodic planar dual pairs

Plane embeddings of periodic graphs, pairs of mutually dual periodic planar graphs, and the
translation of dual percolation into percolation of the dual configuration under the primal
free measure.

## i. Overview

A periodic plane embedding draws vertices as points of `ℂ` and edges as injective arcs, compatibly
with a lattice of periods, so that distinct edges meet only at common endpoints. A periodic
planar dual pair consists of two such embeddings with an edge bijection `e ↦ e†` under which each
primal edge crosses exactly its dual edge. The structure also records, as the fields
`free_wired_infiniteVolume_dual_law` and `wired_free_infiniteVolume_dual_law`, that the wired
(free) dual buffered infinite-volume measure at `p*` is the image of the free (wired) primal one
at `p` under configuration duality (`ThermodynamicDuality` derives such laws from finite-volume
exchange). Through these laws, wired dual percolation at `p*` is free-primal percolation of the
dual configuration at `p`, which rewrites the coverage and no-coexistence inputs of the critical
relation.
The headline `PeriodicPlanarDualPair.dualCritical_relation_of_freeDual` is conditional: it
assumes a dual pair `D` (including the two dual-law fields above), coverage (free dual percolation
for every `p < pc`) and no-coexistence of wired primal and free dual percolation, besides
`pc, pc* ∈ (0, 1)` and `1 ≤ q`.

## ii. Key results

- `PeriodicPlaneEmbedding` : a periodic embedding of a periodic graph in the plane.
- `PeriodicPlanarDualPair` : a pair of mutually dual periodic planar graphs with dual laws.
- `PeriodicPlanarDualPair.swap` : the roles of primal and dual exchanged.
- `PeriodicPlanarDualPair.wiredPercolationProbability_dualParam` : wired dual percolation at `p*`
  equals free percolation of the dual configuration at `p`.
- `PeriodicPlanarDualPair.dualCritical_relation_of_freeDual` : the critical relation from
  coverage and no-coexistence for a dual pair.

## iii. Table of contents

- A. Plane embeddings and dual pairs
- B. Swapping primal and dual
- C. Auxiliary counting and measure facts
- D. Dual percolation
- E. The critical relation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 6.1 and 6.2.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

set_option linter.unusedSectionVars false

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## A. Plane embeddings and dual pairs -/

/-- A periodic plane embedding: vertices as points of `ℂ`, translations acting by an injective
lattice of periods, and edges as injective arcs that meet only at common endpoints, with only
finitely many arcs meeting any compact set. -/
structure PeriodicPlaneEmbedding (P : PeriodicGraph V) where
  vertex : V ↪ ℂ
  period : Site 2 →+ ℂ
  period_injective : Function.Injective period
  coordinates : ℂ ≃L[ℝ] (Fin 2 → ℝ)
  coordinates_period : ∀ z i, coordinates (period z) i = z i
  vertex_shift : ∀ z x, vertex (P.shift z x) = vertex x + period z
  proper : ∀ R : ℝ, {x | ‖(vertex x : ℂ)‖ ≤ R}.Finite
  edgeArc : ∀ {x y : V}, P.graph.Adj x y → Path (vertex x) (vertex y)
  edgeArc_injective : ∀ {x y : V} (hxy : P.graph.Adj x y),
    Function.Injective (edgeArc hxy)
  edgeArc_symm : ∀ {x y : V} (hxy : P.graph.Adj x y),
    Set.range (edgeArc hxy.symm) = Set.range (edgeArc hxy)
  edgeArc_shift : ∀ (z : Site 2) {x y : V} (hxy : P.graph.Adj x y),
    Set.range (edgeArc ((P.shift_adj z x y).2 hxy)) =
      (fun p => p + period z) '' Set.range (edgeArc hxy)
  edgeArc_intersection : ∀ {x y z w : V}
      (hxy : P.graph.Adj x y) (hzw : P.graph.Adj z w) (p : ℂ),
      s(x, y) ≠ s(z, w) →
      p ∈ Set.range (edgeArc hxy) → p ∈ Set.range (edgeArc hzw) →
        ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧ vertex v = p
  edgeArc_disjoint : ∀ {x y z w : V}
      (hxy : P.graph.Adj x y) (hzw : P.graph.Adj z w),
      x ≠ z → x ≠ w → y ≠ z → y ≠ w →
        Disjoint (Set.range (edgeArc hxy)) (Set.range (edgeArc hzw))
  edgeArc_locallyFinite : ∀ (K : Set ℂ), IsCompact K →
    {xy : V × V | ∃ hxy : P.graph.Adj xy.1 xy.2,
      (Set.range (edgeArc hxy) ∩ K).Nonempty}.Finite

/-- A periodic planar dual pair: plane embeddings of a periodic graph and of its dual in the same
coordinates, an edge bijection under which each primal edge crosses exactly its dual edge, and the
free/wired infinite-volume dual laws at `p*`. -/
structure PeriodicPlanarDualPair
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) where
  primalEmbedding : PeriodicPlaneEmbedding P
  dualEmbedding : PeriodicPlaneEmbedding Pdual
  coordinates_eq : primalEmbedding.coordinates = dualEmbedding.coordinates
  primal_connected : P.graph.Connected
  dual_connected : Pdual.graph.Connected
  edgeDual : Sym2 V ≃ Sym2 W
  edgeDual_mem_edgeSet : ∀ e,
    e ∈ P.graph.edgeSet ↔ edgeDual e ∈ Pdual.graph.edgeSet
  edgeDual_shift : ∀ z e,
    edgeDual (Sym2.map (P.shift z) e) =
      Sym2.map (Pdual.shift z) (edgeDual e)
  edgeDual_crossing : ∀ {x y : V} {a b : W}
      (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b),
      edgeDual s(x, y) = s(a, b) →
        ∃ t u,
          primalEmbedding.edgeArc hxy t = dualEmbedding.edgeArc hab u
  edgeDual_of_crossing : ∀ {x y : V} {a b : W}
      (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b) (t u),
      primalEmbedding.edgeArc hxy t = dualEmbedding.edgeArc hab u →
        edgeDual s(x, y) = s(a, b)
  free_wired_infiniteVolume_dual_law : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
    Pdual.wiredBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (dualConfigEquiv edgeDual)
  wired_free_infiniteVolume_dual_law : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
    Pdual.freeBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (dualConfigEquiv edgeDual)

namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## B. Swapping primal and dual -/

lemma period_eq
    (D : PeriodicPlanarDualPair P Pdual) :
    D.primalEmbedding.period = D.dualEmbedding.period := by
  apply AddMonoidHom.ext
  intro z
  apply D.primalEmbedding.coordinates.injective
  ext i
  rw [D.primalEmbedding.coordinates_period]
  have h := D.dualEmbedding.coordinates_period z i
  rw [← D.coordinates_eq] at h
  exact h.symm

/-- The dual pair with the roles of the primal and dual graphs exchanged. -/
noncomputable def swap
    (D : PeriodicPlanarDualPair P Pdual) :
    PeriodicPlanarDualPair Pdual P where
  primalEmbedding := D.dualEmbedding
  dualEmbedding := D.primalEmbedding
  coordinates_eq := D.coordinates_eq.symm
  primal_connected := D.dual_connected
  dual_connected := D.primal_connected
  edgeDual := D.edgeDual.symm
  edgeDual_mem_edgeSet := by
    intro e
    simpa using (D.edgeDual_mem_edgeSet (D.edgeDual.symm e)).symm
  edgeDual_shift := by
    intro z e
    apply D.edgeDual.injective
    simpa using (D.edgeDual_shift z (D.edgeDual.symm e)).symm
  edgeDual_crossing := by
    intro x y a b hxy hab hedge
    have hedge' : D.edgeDual s(a, b) = s(x, y) := by
      apply D.edgeDual.symm.injective
      simpa using hedge.symm
    obtain ⟨u, t, hut⟩ := D.edgeDual_crossing hab hxy hedge'
    exact ⟨t, u, hut.symm⟩
  edgeDual_of_crossing := by
    intro x y a b hxy hab t u hcross
    have hedge := D.edgeDual_of_crossing hab hxy u t hcross.symm
    apply D.edgeDual.injective
    simpa using hedge.symm
  free_wired_infiniteVolume_dual_law := by
    intro p q hp hp1 hq
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hpStar := dualParam_mem_Ioo hp hp1 hq0
    have hinv := dualParam_involutive hp hp1 hq0
    have h := D.wired_free_infiniteVolume_dual_law
      hpStar.1 hpStar.2 hq
    have h' :
        Pdual.freeBufferedInfiniteVolume hp hp1 hq0 =
          (P.wiredBufferedInfiniteVolume hpStar.1 hpStar.2 hq0).map
            (dualConfigEquiv D.edgeDual) := by
      simpa only [hinv] using h
    apply ProbabilityMeasure.toMeasure_injective
    change _ = Measure.map _ _
    rw [h', ProbabilityMeasure.toMeasure_map, Measure.map_map]
    · simp [dualConfigEquiv_symm]
    · exact (continuous_dualConfigEquiv D.edgeDual.symm).measurable
    · exact (continuous_dualConfigEquiv D.edgeDual).measurable
  wired_free_infiniteVolume_dual_law := by
    intro p q hp hp1 hq
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hpStar := dualParam_mem_Ioo hp hp1 hq0
    have hinv := dualParam_involutive hp hp1 hq0
    have h := D.free_wired_infiniteVolume_dual_law
      hpStar.1 hpStar.2 hq
    have h' :
        Pdual.wiredBufferedInfiniteVolume hp hp1 hq0 =
          (P.freeBufferedInfiniteVolume hpStar.1 hpStar.2 hq0).map
            (dualConfigEquiv D.edgeDual) := by
      simpa only [hinv] using h
    apply ProbabilityMeasure.toMeasure_injective
    change _ = Measure.map _ _
    rw [h', ProbabilityMeasure.toMeasure_map, Measure.map_map]
    · simp [dualConfigEquiv_symm]
    · exact (continuous_dualConfigEquiv D.edgeDual.symm).measurable
    · exact (continuous_dualConfigEquiv D.edgeDual).measurable

@[simp] lemma swap_primalEmbedding
    (D : PeriodicPlanarDualPair P Pdual) :
    D.swap.primalEmbedding = D.dualEmbedding := rfl

@[simp] lemma swap_dualEmbedding
    (D : PeriodicPlanarDualPair P Pdual) :
    D.swap.dualEmbedding = D.primalEmbedding := rfl

/-! ## C. Auxiliary counting and measure facts -/

lemma PeriodicPlaneEmbedding.shift_ne_of_ne
    (E : PeriodicPlaneEmbedding P) {z : Site 2} (hz : z ≠ 0) (x : V) :
    P.shift z x ≠ x := by
  intro hfix
  have hperiod : E.period z = 0 := by
    have hshift := E.vertex_shift z x
    rw [hfix] at hshift
    have hcancel : E.vertex x + E.period z = E.vertex x + 0 := by
      simpa using hshift.symm
    exact add_left_cancel hcancel
  exact hz (E.period_injective (hperiod.trans E.period.map_zero.symm))

lemma PeriodicGraph.orbitBox_card_le_quadratic
    (P : PeriodicGraph V) (n : ℕ) :
    (P.orbitBox n).card ≤ (2 * n + 1) ^ 2 * P.fundamentalDomain.card := by
  rw [PeriodicGraph.orbitBox]
  calc
    ((((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain).image
      (fun zu => P.shift zu.1 zu.2))).card ≤
        ((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain).card :=
      Finset.card_image_le
    _ = (2 * n + 1) ^ 2 * P.fundamentalDomain.card := by
      rw [Finset.card_product, ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]

lemma probabilityMeasure_eq_of_finiteCylinder_real_eq
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (ConfigSpace E))
    (h : ∀ (s : Finset E) (S : Set (∀ _i : s, Bool)),
      (mu : Measure (ConfigSpace E)).real (cylinder s S) =
        (nu : Measure (ConfigSpace E)).real (cylinder s S)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨s, S, _hS, rfl⟩ := hC
    have hreal := h s S
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure (ConfigSpace E)) (cylinder s S))
      (measure_ne_top (nu : Measure (ConfigSpace E)) (cylinder s S))).mp hreal
  · rw [measure_univ, measure_univ]

/-! ## D. Dual percolation -/

lemma percolationEvent_measurableSet (P : PeriodicGraph V) :
    MeasurableSet P.percolationEvent := by
  rw [← P.iInter_bufferedRootBoundaryCylinder]
  exact MeasurableSet.iInter fun n =>
    P.bufferedCylinder_measurableSet n (P.bufferedRootBoundaryEvent n)

lemma wiredDual_percolationEvent
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ((Pdual.wiredBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 W))) :
      Measure (ConfigSpace (Sym2 W))) Pdual.percolationEvent =
    ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V)))
      ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent) := by
  apply weakLimit_dual_event D.edgeDual
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.wiredBufferedInfiniteVolume
      (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
      (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
      (zero_lt_one.trans_le hq))
    (D.free_wired_infiniteVolume_dual_law hp hp1 hq)
    (percolationEvent_measurableSet Pdual)

/-- The probability under the free primal buffered infinite-volume measure that the dual
configuration percolates at the dual root, and `0` outside `0 < p < 1`, `0 < q`. -/
noncomputable def freeDualPercolationProbability
    (D : PeriodicPlanarDualPair P Pdual) (p q : ℝ) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real
      ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent)
  else 0

/-- The dual configuration percolates with positive probability under the free primal measure at
`(p, q)`. -/
def FreeDualPercolates
    (D : PeriodicPlanarDualPair P Pdual) (p q : ℝ) : Prop :=
  0 < D.freeDualPercolationProbability p q

/-- The wired dual percolation probability at `p*` equals the free dual percolation probability at
`p`. -/
lemma wiredPercolationProbability_dualParam
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.wiredPercolationProbability (dualParam p q) q =
      D.freeDualPercolationProbability p q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := dualParam_mem_Ioo hp hp1 hq0
  unfold PeriodicGraph.wiredPercolationProbability
    freeDualPercolationProbability
  rw [dite_eq_left ⟨hpDual, hq0⟩, dite_eq_left ⟨⟨hp, hp1⟩, hq0⟩]
  exact congrArg ENNReal.toReal (D.wiredDual_percolationEvent hp hp1 hq)

lemma wiredPercolates_dualParam_iff
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.wiredPercolates (dualParam p q) q ↔
      D.FreeDualPercolates p q := by
  unfold PeriodicGraph.wiredPercolates FreeDualPercolates
  rw [D.wiredPercolationProbability_dualParam hp hp1 hq]

lemma dualSubcriticalCoverage_iff_freeDual
    (D : PeriodicPlanarDualPair P Pdual) {pc q : ℝ} (hq : 1 ≤ q) :
    DualSubcriticalCoverage
        (fun r => Pdual.wiredPercolates r q) pc q ↔
      ∀ p ∈ Ioo (0 : ℝ) 1, p < pc → D.FreeDualPercolates p q := by
  constructor
  · intro h p hp hpc
    exact (D.wiredPercolates_dualParam_iff hp.1 hp.2 hq).mp
      (h p hp hpc)
  · intro h p hp hpc
    exact (D.wiredPercolates_dualParam_iff hp.1 hp.2 hq).mpr
      (h p hp hpc)

lemma dualNoCoexistence_iff_freeDual
    (D : PeriodicPlanarDualPair P Pdual) {q : ℝ} (hq : 1 ≤ q) :
    DualNoCoexistence
        (fun p => P.wiredPercolates p q)
        (fun r => Pdual.wiredPercolates r q) q ↔
      ∀ p ∈ Ioo (0 : ℝ) 1,
        ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q) := by
  constructor
  · intro h p hp
    simpa only [D.wiredPercolates_dualParam_iff hp.1 hp.2 hq] using h p hp
  · intro h p hp
    simpa only [D.wiredPercolates_dualParam_iff hp.1 hp.2 hq] using h p hp

/-! ## E. The critical relation -/

/-- Conditional critical-point duality for a dual pair: free dual percolation below `pc` and
no-coexistence of wired primal and free dual percolation give `pc* = (pc)*` and
`pc / (1 - pc) · pc* / (1 - pc*) = q`. -/
theorem dualCritical_relation_of_freeDual
    (D : PeriodicPlanarDualPair P Pdual) {q : ℝ}
    (hpc : P.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q)
    (hcoverage : ∀ p ∈ Ioo (0 : ℝ) 1,
      p < P.criticalPoint q → D.FreeDualPercolates p q)
    (hnoCoexistence : ∀ p ∈ Ioo (0 : ℝ) 1,
      ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q)) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply P.dualCritical_relation_of_noCoexistence Pdual
    hpc hpcDual hq
  · exact (D.dualSubcriticalCoverage_iff_freeDual hq).mpr hcoverage
  · exact (D.dualNoCoexistence_iff_freeDual hq).mpr hnoCoexistence

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
