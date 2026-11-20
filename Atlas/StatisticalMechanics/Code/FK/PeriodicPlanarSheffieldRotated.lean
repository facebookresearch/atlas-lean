/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarSheffield

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



theorem matchedVerticalHorizontalCrossingEvents_disjoint
    (D : PeriodicPlanarDualPair P Pdual) {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    Disjoint
      (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)) := by
  rw [Set.disjoint_left]
  intro omega hV hH
  change D.primalEmbedding.rectRestrict (a + 4 * B) (b - 4 * B) c d omega ∈
    D.primalEmbedding.finiteVerticalCrossing
      (a + 4 * B) (b - 4 * B) c d at hV
  change D.dualEmbedding.rectRestrict a b (c + 4 * B) (d - 4 * B)
      (dualConfigEquiv D.edgeDual omega) ∈
    D.dualEmbedding.finiteHorizontalCrossing
      a b (c + 4 * B) (d - 4 * B) at hH
  rcases hV with ⟨xp, yp, hxp, hyp, hpReach⟩
  rcases hH with ⟨xd, yd, hxd, hyd, hdReach⟩
  obtain ⟨p⟩ := hpReach
  obtain ⟨q⟩ := hdReach
  obtain ⟨xb, hxb, hxbcoord⟩ := hxp
  obtain ⟨xt, hxt, hxtcoord⟩ := hyp
  obtain ⟨xl, hxl, hxlcoord⟩ := hxd
  obtain ⟨xr, hxr, hxrcoord⟩ := hyd
  let pfull : P.graph.Walk xp.1 yp.1 := p.map (D.primalEmbedding.openRectHom
    (a + 4 * B) (b - 4 * B) c d
      (D.primalEmbedding.rectRestrict
        (a + 4 * B) (b - 4 * B) c d omega))
  let qfull : Pdual.graph.Walk xd.1 yd.1 := q.map (D.dualEmbedding.openRectHom
    a b (c + 4 * B) (d - 4 * B)
      (D.dualEmbedding.rectRestrict a b (c + 4 * B) (d - 4 * B)
        (dualConfigEquiv D.edgeDual omega)))
  let eta0 := D.primalEmbedding.walkArc pfull
  let gamma0 := D.dualEmbedding.walkArc qfull
  let eta := (D.primalEmbedding.edgeArc hxb).symm.trans
    (eta0.trans (D.primalEmbedding.edgeArc hxt))
  let gamma := (D.dualEmbedding.edgeArc hxl).symm.trans
    (gamma0.trans (D.dualEmbedding.edgeArc hxr))
  have hxpNear := D.primalEmbedding.rectBottomBoundary_coord_lt hBp
    (show D.primalEmbedding.rectBottomBoundary
      (a + 4 * B) (b - 4 * B) c d xp from ⟨xb, hxb, hxbcoord⟩)
  have hypNear := D.primalEmbedding.rectTopBoundary_coord_gt hBp
    (show D.primalEmbedding.rectTopBoundary
      (a + 4 * B) (b - 4 * B) c d yp from ⟨xt, hxt, hxtcoord⟩)
  have hxdNear := D.dualEmbedding.rectLeftBoundary_coord_lt hBd
    (show D.dualEmbedding.rectLeftBoundary
      a b (c + 4 * B) (d - 4 * B) xd from ⟨xl, hxl, hxlcoord⟩)
  have hydNear := D.dualEmbedding.rectRightBoundary_coord_gt hBd
    (show D.dualEmbedding.rectRightBoundary
      a b (c + 4 * B) (d - 4 * B) yd from ⟨xr, hxr, hxrcoord⟩)
  have hpNotNil : ¬ pfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xp.1 ≠ yp.1
    intro heq
    rw [heq] at hxpNear
    linarith
  have hqNotNil : ¬ qfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xd.1 ≠ yd.1
    intro heq
    rw [heq] at hxdNear
    linarith
  have hetaRect : Set.range eta ⊆
      D.primalEmbedding.planeRect
        ((a + 4 * B) - B) ((b - 4 * B) + B) (c - B) (d + B) := by
    intro z hz
    dsimp only [eta] at hz
    rw [Path.trans_range] at hz
    rcases hz with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨t, rfl⟩ := hbottom
      exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxb xp.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact D.primalEmbedding.openRectWalkArc_range_subset
          hBpos.le hBp p hcore
      · obtain ⟨t, rfl⟩ := htop
        exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxt yp.2 t
  have hgammaRectDual : Set.range gamma ⊆
      D.dualEmbedding.planeRect
        (a - B) (b + B) ((c + 4 * B) - B) ((d - 4 * B) + B) := by
    intro z hz
    dsimp only [gamma] at hz
    rw [Path.trans_range] at hz
    rcases hz with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨t, rfl⟩ := hleft
      exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxl xd.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact D.dualEmbedding.openRectWalkArc_range_subset
          hBpos.le hBd q hcore
      · obtain ⟨t, rfl⟩ := hright
        exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxr yd.2 t
  let gammaC := gamma.map D.primalEmbedding.coordinates.continuous
  let etaC := eta.map D.primalEmbedding.coordinates.continuous
  have hgammaY : ∀ t : unitInterval,
      c < gammaC t 1 ∧ gammaC t 1 < d := by
    intro t
    have ht := hgammaRectDual ⟨t, rfl⟩
    rw [D.dual_planeRect_eq] at ht
    change c < D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 < d
    change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
      D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
      (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at ht
    constructor <;> linarith
  have hetaX : ∀ t : unitInterval,
      a < etaC t 0 ∧ etaC t 0 < b := by
    intro t
    have ht := hetaRect ⟨t, rfl⟩
    change a < D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 < b
    change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 ≤ (b - 4 * B) + B ∧
      c - B ≤ D.primalEmbedding.coordinates (eta t) 1 ∧
      D.primalEmbedding.coordinates (eta t) 1 ≤ d + B at ht
    constructor <;> linarith
  have hgammaLeft : D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xl) 0 < a := by
    rw [D.coordinates_eq]
    change D.dualEmbedding.vertexCoord xl 0 < a
    exact hxlcoord
  have hgammaRight : b < D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xr) 0 := by
    rw [D.coordinates_eq]
    change b < D.dualEmbedding.vertexCoord xr 0
    exact hxrcoord
  have hetaBottom : D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xb) 1 < c := by
    change D.primalEmbedding.vertexCoord xb 1 < c
    exact hxbcoord
  have hetaTop : d < D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xt) 1 := by
    change d < D.primalEmbedding.vertexCoord xt 1
    exact hxtcoord
  have hab0 : a < b := by linarith
  have hcd0 : c < d := by linarith
  obtain ⟨t, s, hcrossC⟩ :=
    ContinuousRectangleCrossing.strip_paths_intersect hab0 hcd0 gammaC etaC
      hgammaLeft hgammaRight hetaBottom hetaTop hgammaY hetaX
  have hcross : gamma t = eta s := by
    apply D.primalEmbedding.coordinates.injective
    simpa [gammaC, etaC] using hcrossC
  have htRect := hgammaRectDual ⟨t, rfl⟩
  rw [D.dual_planeRect_eq] at htRect
  have hsRect := hetaRect ⟨s, rfl⟩
  change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
    D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
    (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
    D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at htRect
  change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta s) 0 ∧
    D.primalEmbedding.coordinates (eta s) 0 ≤ (b - 4 * B) + B ∧
    c - B ≤ D.primalEmbedding.coordinates (eta s) 1 ∧
    D.primalEmbedding.coordinates (eta s) 1 ≤ d + B at hsRect
  have htCore : gamma t ∈ Set.range gamma0 := by
    have ht : gamma t ∈ Set.range gamma := ⟨t, rfl⟩
    dsimp only [gamma] at ht
    rw [Path.trans_range] at ht
    rcases ht with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨r, hr⟩ := hleft
      have hu := D.dualEmbedding.edgeArc_coord_le_vertex_add hBd hxl r 0
      rw [hr] at hu
      rw [← D.coordinates_eq] at hu
      rw [hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact hcore
      · obtain ⟨r, hr⟩ := hright
        have hu := D.dualEmbedding.vertex_sub_le_edgeArc_coord hBd hxr r 0
        rw [hr] at hu
        rw [← D.coordinates_eq] at hu
        rw [hcross] at hu
        linarith
  have hsCore : eta s ∈ Set.range eta0 := by
    have hs : eta s ∈ Set.range eta := ⟨s, rfl⟩
    dsimp only [eta] at hs
    rw [Path.trans_range] at hs
    rcases hs with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨r, hr⟩ := hbottom
      have hu := D.primalEmbedding.edgeArc_coord_le_vertex_add hBp hxb r 1
      rw [hr] at hu
      rw [← hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact hcore
      · obtain ⟨r, hr⟩ := htop
        have hu := D.primalEmbedding.vertex_sub_le_edgeArc_coord hBp hxt r 1
        rw [hr] at hu
        rw [← hcross] at hu
        linarith
  have hdisj := D.no_openRectWalkArc_crossing omega p q hpNotNil hqNotNil
  exact Set.disjoint_left.mp hdisj hsCore (hcross ▸ htCore)


theorem matchedVerticalHorizontalCrossing_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)) ≤ 1 := by
  let Vp := D.primalEmbedding.verticalCrossingEvent
    (a + 4 * B) (b - 4 * B) c d
  let Hd := (dualConfigEquiv D.edgeDual) ⁻¹'
    D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)
  have hdisj : Disjoint Vp Hd :=
    D.matchedVerticalHorizontalCrossingEvents_disjoint
      hBpos hBp hBd hab hcd
  have hHd : MeasurableSet Hd :=
    (D.dualEmbedding.horizontalCrossingEvent_measurableSet
      a b (c + 4 * B) (d - 4 * B)).preimage
        (continuous_dualConfigEquiv D.edgeDual).measurable
  have hu : mu.real (Vp ∪ Hd) ≤ 1 := measureReal_le_one
  rw [measureReal_union hdisj hHd] at hu
  exact hu





theorem primalCrossing_min_lt_of_dualCrossing_max_gt
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B a b c d epsilon : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hdual : 1 - epsilon < max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)))) :
    min
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)) < epsilon := by
  have hhorizontal := D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hvertical := D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  rw [lt_max_iff] at hdual
  rw [min_lt_iff]
  rcases hdual with hdualVertical | hdualHorizontal
  · left
    linarith
  · right
    linarith



theorem exists_buffer_primalCrossing_min_lt_of_dualCrossing_max_gt
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu] :
    ∃ B : ℝ, 0 < B ∧ ∀ {a b c d epsilon : ℝ},
      a + 5 * B < b - 5 * B → c + 5 * B < d - 5 * B →
      1 - epsilon < max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + 4 * B) (d - 4 * B))) →
      min
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d)) < epsilon := by
  obtain ⟨B, hBpos, hBp, hBd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  refine ⟨B, hBpos, ?_⟩
  intro a b c d epsilon hab hcd hdual
  exact D.primalCrossing_min_lt_of_dualCrossing_max_gt
    mu hBpos hBp hBd hab hcd hdual




theorem exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d : ℕ → ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (hspanX : ∀ n, a n + 5 * B < b n - 5 * B)
        (hspanY : ∀ n, c n + 5 * B < d n - 5 * B),
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a n + 4 * B) (b n - 4 * B) (c n) (d n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a n) (b n) (c n + 4 * B) (d n - 4 * B))))
        atTop (nhds 1) →
      Tendsto (fun n => min
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (d n - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (d n))))
        atTop (nhds 0) := by
  obtain ⟨B, hBpos, hBp, hBd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  refine ⟨B, hBpos, ?_⟩
  intro hspanX hspanY hdual
  apply min_tendsto_zero_of_matched_exclusion
  · intro n
    exact measureReal_nonneg
  · intro n
    exact measureReal_nonneg
  · intro n
    exact D.matchedCrossing_measureReal_add_le_one mu hBpos hBp hBd
      (hspanX n) (hspanY n)
  · intro n
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu hBpos hBp hBd (hspanX n) (hspanY n)
  · exact hdual






theorem balanced_aspect_contradiction_of_crossing_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (a b c d dNext : Nat → Real)
    (hspanX : ∀ n, a n + 5 * B < b n - 5 * B)
    (hspanY : ∀ n, c n + 5 * B < d n - 5 * B)
    (hspanYNext : ∀ n, c n + 5 * B < dNext n - 5 * B)
    (hbalance : ∀ n,
      mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (d n - 4 * B)) ≤
        mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (d n)))
    (hnext : ∀ n,
      mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (dNext n)) ≤
        mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (dNext n - 4 * B)))
    (hprimalMax : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a n) (b n) (c n + 4 * B) (d n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a n + 4 * B) (b n - 4 * B) (c n) (dNext n))))
      atTop (nhds 1))
    (hdualMax : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (d n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (d n - 4 * B))))
      atTop (nhds 1))
    (hdualMaxNext : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (dNext n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (dNext n - 4 * B))))
      atTop (nhds 1)) : False := by
  let h : Nat → Real := fun n =>
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a n) (b n) (c n + 4 * B) (d n - 4 * B))
  let v : Nat → Real := fun n =>
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (a n + 4 * B) (b n - 4 * B) (c n) (d n))
  let hN : Nat → Real := fun n =>
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a n) (b n) (c n + 4 * B) (dNext n - 4 * B))
  let vN : Nat → Real := fun n =>
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (a n + 4 * B) (b n - 4 * B) (c n) (dNext n))
  have hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0) := by
    have ht := min_tendsto_zero_of_matched_exclusion h v
      (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (d n)))
      (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (d n - 4 * B)))
      (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      (fun n => D.matchedCrossing_measureReal_add_le_one
        mu hBpos hBp hBd (hspanX n) (hspanY n))
      (fun n => D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
        mu hBpos hBp hBd (hspanX n) (hspanY n)) hdualMax
    simpa [h, v, min_comm] using ht
  have hminNext : Tendsto (fun n => min (vN n) (hN n))
      atTop (nhds 0) := by
    have ht := min_tendsto_zero_of_matched_exclusion hN vN
      (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + 4 * B) (b n - 4 * B) (c n) (dNext n)))
      (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + 4 * B) (dNext n - 4 * B)))
      (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      (fun n => D.matchedCrossing_measureReal_add_le_one
        mu hBpos hBp hBd (hspanX n) (hspanYNext n))
      (fun n => D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
        mu hBpos hBp hBd (hspanX n) (hspanYNext n)) hdualMaxNext
    simpa [hN, vN, min_comm] using ht
  apply balanced_aspect_crossing_contradiction_of_error
    h v hN vN (fun _ => 0)
  · intro n
    exact measureReal_nonneg
  · intro n
    exact measureReal_nonneg
  · intro n
    norm_num
  · simpa [h, v] using hbalance
  · simpa [hN, vN] using hnext
  · exact tendsto_const_nhds
  · simpa [h, vN] using hprimalMax
  · exact hmin
  · exact hminNext

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
