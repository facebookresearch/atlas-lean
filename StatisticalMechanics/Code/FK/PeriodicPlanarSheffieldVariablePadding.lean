/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



theorem PeriodicPlaneEmbedding.verticalCrossingEvent_mono_horizontal
    (E : PeriodicPlaneEmbedding P) {a' a b b' c d : Real}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.verticalCrossingEvent a b c d ⊆
      E.verticalCrossingEvent a' b' c d := by
  intro omega homega
  change E.rectRestrict a b c d omega ∈
    E.finiteVerticalCrossing a b c d at homega
  obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices a' b' c d :=
    ⟨ha.trans x.2.1, x.2.2.1.trans hb, x.2.2.2⟩
  have hy' : y.1 ∈ E.rectVertices a' b' c d :=
    ⟨ha.trans y.2.1, y.2.2.1.trans hb, y.2.2.2⟩
  have hxBottom' : E.rectBottomBoundary a' b' c d ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxBottom
    exact ⟨z, hxz, hz⟩
  have hyTop' : E.rectTopBoundary a' b' c d ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyTop
    exact ⟨z, hyz, hz⟩
  rw [E.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce (E.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices a' b' c d := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.rectVertices a b c d)).toHom).support := by
      exact hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨u, _hu, rfl⟩ := hv'
    exact ⟨ha.trans u.2.1, u.2.2.1.trans hb, u.2.2.2⟩
  have hxy' :
      ((P.openSubgraph omega).induce (E.rectVertices a' b' c d)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices a' b' c d) hpAmbient⟩
  change E.rectRestrict a' b' c d omega ∈
    E.finiteVerticalCrossing a' b' c d
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxBottom', hyTop', ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hxy'



theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_mono_vertical
    (E : PeriodicPlaneEmbedding P) {a b c' c d d' : Real}
    (hc : c' ≤ c) (hd : d ≤ d') :
    E.horizontalCrossingEvent a b c d ⊆
      E.horizontalCrossingEvent a b c' d' := by
  intro omega homega
  change E.rectRestrict a b c d omega ∈
    E.finiteHorizontalCrossing a b c d at homega
  obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices a b c' d' :=
    ⟨x.2.1, x.2.2.1, hc.trans x.2.2.2.1, x.2.2.2.2.trans hd⟩
  have hy' : y.1 ∈ E.rectVertices a b c' d' :=
    ⟨y.2.1, y.2.2.1, hc.trans y.2.2.2.1, y.2.2.2.2.trans hd⟩
  have hxLeft' : E.rectLeftBoundary a b c' d' ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxLeft
    exact ⟨z, hxz, hz⟩
  have hyRight' : E.rectRightBoundary a b c' d' ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyRight
    exact ⟨z, hyz, hz⟩
  rw [E.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce (E.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices a b c' d' := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.rectVertices a b c d)).toHom).support := by
      exact hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨u, _hu, rfl⟩ := hv'
    exact ⟨u.2.1, u.2.2.1, hc.trans u.2.2.2.1, u.2.2.2.2.trans hd⟩
  have hxy' :
      ((P.openSubgraph omega).induce (E.rectVertices a b c' d')).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices a b c' d') hpAmbient⟩
  change E.rectRestrict a b c' d' omega ∈
    E.finiteHorizontalCrossing a b c' d'
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxLeft', hyRight', ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hxy'



theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_mono_horizontal
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d a' b' : Nat -> Real)
    (ha : forall n, a' n <= a n) (hb : forall n, b n <= b' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n)))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => measureReal_mono
      (E.verticalCrossingEvent_mono_horizontal (ha n) (hb n)))
    (fun _ => measureReal_le_one)



theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_mono_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d c' d' : Nat -> Real)
    (hc : forall n, c' n <= c n) (hd : forall n, d n <= d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n)))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => measureReal_mono
      (E.horizontalCrossingEvent_mono_vertical (hc n) (hd n)))
    (fun _ => measureReal_le_one)



theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_pads
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B xPad yPad a b c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hxPad : 4 * B ≤ xPad) (hyPad : 4 * B ≤ yPad)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + yPad) (d - yPad)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + xPad) (b - xPad) c d) ≤ 1 := by
  have hH : D.primalEmbedding.horizontalCrossingEvent
      a b (c + yPad) (d - yPad) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B) :=
    D.primalEmbedding.horizontalCrossingEvent_mono_vertical
      (by linarith) (by linarith)
  have hV : D.dualEmbedding.verticalCrossingEvent
      (a + xPad) (b - xPad) c d ⊆
      D.dualEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d :=
    D.dualEmbedding.verticalCrossingEvent_mono_horizontal
      (by linarith) (by linarith)
  have hbase := D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hHm := measureReal_mono (h₂ := measure_ne_top mu _) hH
  have hVpre :
      (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + xPad) (b - xPad) c d ⊆
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d :=
    Set.preimage_mono hV
  have hVm := measureReal_mono (h₂ := measure_ne_top mu _)
    hVpre
  linarith



theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B xPad yPad a b c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hxPad : 4 * B ≤ xPad) (hyPad : 4 * B ≤ yPad)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + xPad) (b - xPad) c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b (c + yPad) (d - yPad)) ≤ 1 := by
  have hV : D.primalEmbedding.verticalCrossingEvent
      (a + xPad) (b - xPad) c d ⊆
      D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d :=
    D.primalEmbedding.verticalCrossingEvent_mono_horizontal
      (by linarith) (by linarith)
  have hH : D.dualEmbedding.horizontalCrossingEvent
      a b (c + yPad) (d - yPad) ⊆
      D.dualEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B) :=
    D.dualEmbedding.horizontalCrossingEvent_mono_vertical
      (by linarith) (by linarith)
  have hbase := D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hVm := measureReal_mono (h₂ := measure_ne_top mu _) hV
  have hHpre :
      (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + yPad) (d - yPad) ⊆
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + 4 * B) (d - 4 * B) :=
    Set.preimage_mono hH
  have hHm := measureReal_mono (h₂ := measure_ne_top mu _)
    hHpre
  linarith




structure PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) (B : Real) where
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  a1 : Nat → Real
  b1 : Nat → Real
  c1 : Nat → Real
  d1 : Nat → Real
  xPad0 : Nat → Real
  yPad0 : Nat → Real
  xPad1 : Nat → Real
  yPad1 : Nat → Real
  xPad0_ge : ∀ n, 4 * B ≤ xPad0 n
  yPad0_ge : ∀ n, 4 * B ≤ yPad0 n
  xPad1_ge : ∀ n, 4 * B ≤ xPad1 n
  yPad1_ge : ∀ n, 4 * B ≤ yPad1 n
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : ∀ n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : ∀ n, c1 n + 5 * B < d1 n - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
    atTop (nhds 1)
  primalAdjacent : Tendsto (fun n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualLevel0 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
    atTop (nhds 1)
  dualLevel1 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
    atTop (nhds 1)



theorem PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (data : D.VariablePadTwoLevelRectangleArray mu B) : False := by
  let horizontal : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.a0 n) (data.b0 n)
      (data.c0 n + data.yPad0 n) (data.d0 n - data.yPad0 n))
  else mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.a1 n) (data.b1 n)
      (data.c1 n + data.yPad1 n) (data.d1 n - data.yPad1 n))
  let vertical : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.a0 n + data.xPad0 n) (data.b0 n - data.xPad0 n)
      (data.c0 n) (data.d0 n))
  else mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.a1 n + data.xPad1 n) (data.b1 n - data.xPad1 n)
      (data.c1 n) (data.d1 n))
  let dualVertical : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a0 n + data.xPad0 n) (data.b0 n - data.xPad0 n)
        (data.c0 n) (data.d0 n))
  else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a1 n + data.xPad1 n) (data.b1 n - data.xPad1 n)
        (data.c1 n) (data.d1 n))
  let dualHorizontal : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a0 n) (data.b0 n)
        (data.c0 n + data.yPad0 n) (data.d0 n - data.yPad0 n))
  else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a1 n) (data.b1 n)
        (data.c1 n + data.yPad1 n) (data.d1 n - data.yPad1 n))
  let K : Nat → Nat := fun _ ↦ 0
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
  · intro n k
    by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_nonneg]
  · intro n k
    by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_nonneg]
  · intro n k
    by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_le_one]
  · intro n k
    by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_le_one]
  · simpa [vertical] using data.verticalStart
  · simpa [horizontal, K] using data.horizontalEnd
  · intro n k
    by_cases hk : k = 0
    · simpa [horizontal, dualVertical, hk] using
        D.matchedCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad0_ge n) (data.yPad0_ge n)
          (data.spanX0 n) (data.spanY0 n)
    · simpa [horizontal, dualVertical, hk] using
        D.matchedCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad1_ge n) (data.yPad1_ge n)
          (data.spanX1 n) (data.spanY1 n)
  · intro n k
    by_cases hk : k = 0
    · simpa [vertical, dualHorizontal, hk] using
        D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad0_ge n) (data.yPad0_ge n)
          (data.spanX0 n) (data.spanY0 n)
    · simpa [vertical, dualHorizontal, hk] using
        D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad1_ge n) (data.yPad1_ge n)
          (data.spanX1 n) (data.spanY1 n)
  · intro k hk
    have hk0 : ∀ n, k n = 0 := by
      intro n
      have h := hk n
      dsimp only [K] at h
      omega
    simpa [horizontal, vertical, hk0] using data.primalAdjacent
  · intro k _hk
    let q0 : Nat → Real := fun n ↦ max (dualVertical n 0)
      (dualHorizontal n 0)
    let q1 : Nat → Real := fun n ↦ max (dualVertical n 1)
      (dualHorizontal n 1)
    let q : Nat → Real := fun n ↦ if k n = 0 then q0 n else q1 n
    have hq0 : Tendsto q0 atTop (nhds 1) := by
      simpa [q0, dualVertical, dualHorizontal] using data.dualLevel0
    have hq1 : Tendsto q1 atTop (nhds 1) := by
      simpa [q1, dualVertical, dualHorizontal] using data.dualLevel1
    have hlower : ∀ n, min (q0 n) (q1 n) ≤ q n := by
      intro n
      by_cases hn : k n = 0 <;> simp [q, hn]
    have hupper : ∀ n, q n ≤ 1 := by
      intro n
      by_cases hn : k n = 0 <;>
        simp [q, q0, q1, dualVertical, dualHorizontal, hn,
          measureReal_le_one]
    have hq' := (hq0.min hq1).squeeze tendsto_const_nhds hlower
      (fun n ↦ by simpa using hupper n)
    have hq : Tendsto q atTop (nhds 1) := by simpa using hq'
    apply hq.congr'
    filter_upwards with n
    by_cases hn : k n = 0
    · simp [q, q0, hn]
    · have hk1 : k n = 1 := by
        have h := _hk n
        dsimp only [K] at h
        omega
      simp [q, q1, hn, hk1]

end StatMech.FK.PeriodicPlanar
