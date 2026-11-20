/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardGenericPolygonReduction










namespace StatMech.FrontierA

open scoped Convex
open Set

def kwRawEdge {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (i : Fin n) : ℂ :=
  vertex (i + 1) - vertex i

def kwRawClosedEdge {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (i : Fin n) : Set ℂ :=
  segment ℝ (vertex i) (vertex (i + 1))



theorem dist_lineMap_le_of_endpoint_dist_le
    {a b a' b' : ℂ} {t eps : ℝ} (ht : t ∈ Icc 0 1)
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps) :
    dist (AffineMap.lineMap a' b' t) (AffineMap.lineMap a b t) ≤ eps := by
  rw [dist_eq_norm, AffineMap.lineMap_apply_module,
    AffineMap.lineMap_apply_module]
  have heq : (1 - t) • a' + t • b' - ((1 - t) • a + t • b) =
      (1 - t) • (a' - a) + t • (b' - b) := by
    module
  rw [heq]
  calc
    ‖(1 - t) • (a' - a) + t • (b' - b)‖ ≤
        ‖(1 - t) • (a' - a)‖ + ‖t • (b' - b)‖ := norm_add_le _ _
    _ = (1 - t) * dist a' a + t * dist b' b := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2),
        dist_eq_norm, dist_eq_norm]
    _ ≤ (1 - t) * eps + t * eps := by
      gcongr <;> linarith [ht.1, ht.2]
    _ = eps := by ring



theorem exists_source_segment_point_dist_le
    {a b a' b' : ℂ} {eps : ℝ}
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps)
    {z : ℂ} (hz : z ∈ segment ℝ a' b') :
    ∃ w ∈ segment ℝ a b, dist z w ≤ eps := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨AffineMap.lineMap a b t, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  · exact dist_lineMap_le_of_endpoint_dist_le ht ha hb



theorem segment_disjoint_of_perturbation
    {a b c d a' b' c' d' : ℂ} {eps r : ℝ}
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps)
    (hc : dist c' c ≤ eps) (hd : dist d' d ≤ eps)
    (hsep : ∀ x ∈ segment ℝ a b, ∀ y ∈ segment ℝ c d,
      r < dist x y)
    (heps : 2 * eps < r) :
    Disjoint (segment ℝ a' b') (segment ℝ c' d') := by
  rw [Set.disjoint_left]
  intro z hzab hzcd
  obtain ⟨x, hx, hzx⟩ :=
    exists_source_segment_point_dist_le ha hb hzab
  obtain ⟨y, hy, hzy⟩ :=
    exists_source_segment_point_dist_le hc hd hzcd
  have hxy := hsep x hx y hy
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  rw [dist_comm x z] at htri
  linarith



structure KWRawSimplePolygonData
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) : Prop where
  three_le : 3 ≤ n
  vertex_injective : Function.Injective vertex
  cross_ne_zero : ∀ i : Fin n,
    kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0
  nonincident_disjoint : ∀ i j : Fin n, KWEdgesNonincident i j →
    Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)

noncomputable def KWRawSimplePolygonData.toFiniteSimplePolygon
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawSimplePolygonData vertex) : KWFiniteSimplePolygon n where
  vertex := vertex
  three_le := h.three_le
  vertex_injective := h.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    by_cases hprev : i = j + 1
    · have hzero := kwComplexCross_eq_zero_of_sbtw hs
      have hcross := h.cross_ne_zero j
      apply hcross
      unfold kwRawEdge
      rw [hprev] at hzero
      unfold kwComplexCross at hzero ⊢
      simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
      nlinarith
    · have hnon : KWEdgesNonincident i j := by
        exact ⟨hji.symm, hprev, hjs.symm⟩
      have hdis := h.nonincident_disjoint i j hnon
      apply Set.disjoint_left.mp hdis
      · exact mem_segment_iff_wbtw.mpr hs.1
      · exact left_mem_segment ℝ _ _
  edgeInteriors_disjoint := by
    intro i j hij
    by_cases hnon : KWEdgesNonincident i j
    · exact (h.nonincident_disjoint i j hnon).mono
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
    · have hadj : i = j + 1 ∨ i + 1 = j := by
        by_contra hnot
        apply hnon
        refine ⟨hij, ?_, ?_⟩
        · exact (not_or.mp hnot).1
        · exact (not_or.mp hnot).2
      rcases hadj with hprev | hnext
      · subst i
        have hcrossCommon : kwComplexCross
            (vertex (j + 1 + 1) - vertex (j + 1))
            (vertex j - vertex (j + 1)) ≠ 0 := by
          have hcross := h.cross_ne_zero j
          intro hzero
          apply hcross
          unfold kwRawEdge
          unfold kwComplexCross at hzero ⊢
          simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
          linear_combination hzero
        have hd := kw_openSegments_disjoint_of_common_left_cross_ne
          hcrossCommon
        rw [Set.disjoint_left]
        intro z hzFirst hzSecond
        exact Set.disjoint_left.mp hd hzFirst ((sbtw_comm).mpr hzSecond)
      · subst j
        have hcrossCommon : kwComplexCross
            (vertex i - vertex (i + 1))
            (vertex (i + 1 + 1) - vertex (i + 1)) ≠ 0 := by
          have hcross := h.cross_ne_zero i
          intro hzero
          apply hcross
          unfold kwRawEdge
          unfold kwComplexCross at hzero ⊢
          simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
          linear_combination -hzero
        have hd := kw_openSegments_disjoint_of_common_left_cross_ne
          hcrossCommon
        rw [Set.disjoint_left]
        intro z hzFirst hzSecond
        exact Set.disjoint_left.mp hd ((sbtw_comm).mpr hzFirst) hzSecond



theorem KWRawSimplePolygonData.of_vertex_perturbation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (vertex : Fin n → ℂ) {eps vertexRadius edgeRadius : ℝ}
    (hvertex : ∀ i : Fin n,
      dist (vertex i) (polygon.vertex i) ≤ eps)
    (hvertexSep : ∀ i j : Fin n, i ≠ j →
      vertexRadius < dist (polygon.vertex i) (polygon.vertex j))
    (hedgeSep : ∀ i j : Fin n, KWEdgesNonincident i j →
      ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
        edgeRadius < dist x y)
    (hepsVertex : 2 * eps < vertexRadius)
    (hepsEdge : 2 * eps < edgeRadius)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0) :
    KWRawSimplePolygonData vertex := by
  refine ⟨polygon.three_le, ?_, hcross, ?_⟩
  · intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri : dist (polygon.vertex i) (polygon.vertex j) ≤
        dist (polygon.vertex i) (vertex i) +
          dist (vertex i) (polygon.vertex j) := dist_triangle _ _ _
    have htri' : dist (vertex i) (polygon.vertex j) ≤
        dist (vertex i) (vertex j) +
          dist (vertex j) (polygon.vertex j) := dist_triangle _ _ _
    have hi : dist (polygon.vertex i) (vertex i) ≤ eps := by
      simpa only [dist_comm] using hvertex i
    have hj := hvertex j
    have hzero : dist (vertex i) (vertex j) = 0 := by rw [heq, dist_self]
    linarith
  · intro i j hij
    exact segment_disjoint_of_perturbation
      (hvertex i) (hvertex (i + 1))
      (hvertex j) (hvertex (j + 1))
      (hedgeSep i j hij) hepsEdge


def kwRatComplex (q : ℚ × ℚ) : ℂ :=
  (q.1 : ℝ) + (q.2 : ℝ) * Complex.I

theorem denseRange_kwRatComplex : DenseRange kwRatComplex := by
  let realPair : ℚ × ℚ → ℝ × ℝ :=
    Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  let toComplex : ℝ × ℝ → ℂ := fun p ↦ p.1 + p.2 * Complex.I
  have hpair : DenseRange realPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsurj : Function.Surjective toComplex := by
    intro z
    refine ⟨(z.re, z.im), ?_⟩
    apply Complex.ext <;> simp [toComplex]
  have hcontinuous : Continuous toComplex := by
    unfold toComplex
    fun_prop
  have hcomp := hsurj.denseRange.comp hpair hcontinuous
  simpa only [Function.comp_def, realPair, toComplex, kwRatComplex,
    Prod.map_apply] using hcomp

def kwRatVertex {n : ℕ} (q : Fin n → ℚ × ℚ) : Fin n → ℂ :=
  fun i ↦ kwRatComplex (q i)

theorem denseRange_kwRatVertex {n : ℕ} :
    DenseRange (@kwRatVertex n) := by
  have h := DenseRange.piMap (fun _ : Fin n ↦ denseRange_kwRatComplex)
  simpa only [kwRatVertex, Pi.map_apply] using h



theorem exists_cross_stability_radius
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ v : Fin n → ℂ,
      dist v vertex < eps → ∀ i : Fin n,
        kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1)) ≠ 0 := by
  let U : Set (Fin n → ℂ) := ⋂ i : Fin n,
    {v | kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1)) ≠ 0}
  have hopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    have hf : Continuous (fun v : Fin n → ℂ ↦
        kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1))) := by
      unfold kwRawEdge kwComplexCross
      fun_prop
    exact hf.isOpen_preimage {x : ℝ | x ≠ 0} isOpen_ne
  have hvertex : vertex ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    exact hcross
  obtain ⟨eps, heps, hball⟩ := (Metric.isOpen_iff.mp hopen) vertex hvertex
  refine ⟨eps, heps, ?_⟩
  intro v hv i
  exact Set.mem_iInter.mp (hball hv) i



structure KWPolygonPerturbationCertificate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) where
  radius : ℝ
  radius_pos : 0 < radius
  rawSimple : ∀ vertex : Fin n → ℂ,
    dist vertex polygon.vertex < radius → KWRawSimplePolygonData vertex



theorem KWFiniteSimplePolygon.exists_perturbationCertificate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    Nonempty (KWPolygonPerturbationCertificate polygon) := by
  obtain ⟨crossRadius, hcrossRadius, hcrossStable⟩ :=
    exists_cross_stability_radius polygon.vertex (by
      simpa only [kwRawEdge, KWFiniteSimplePolygon.edgeVector] using hcross)
  obtain ⟨vertexRadius, hvertexRadius, hvertexSep⟩ :=
    polygon.exists_uniform_vertex_separation
  obtain ⟨edgeRadius, hedgeRadius, hedgeSep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  let eps : ℝ := min (crossRadius / 2)
    (min ((vertexRadius : ℝ) / 4) ((edgeRadius : ℝ) / 4))
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (half_pos hcrossRadius)
      (lt_min (by positivity) (by positivity))
  refine ⟨{
    radius := eps
    radius_pos := heps
    rawSimple := ?_ }⟩
  intro vertex hvertex
  have hpoint (i : Fin n) :
      dist (vertex i) (polygon.vertex i) < eps :=
    (dist_pi_lt_iff heps).mp hvertex i
  have hinjective : Function.Injective vertex := by
    intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri := dist_triangle (polygon.vertex i) (vertex i)
      (polygon.vertex j)
    rw [heq] at htri
    have hepsVertex : eps ≤ (vertexRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hpath : dist (polygon.vertex i) (polygon.vertex j) <
        (vertexRadius : ℝ) / 2 := by
      calc
        dist (polygon.vertex i) (polygon.vertex j) ≤
            dist (polygon.vertex i) (vertex j) +
              dist (vertex j) (polygon.vertex j) := htri
        _ < eps + eps := add_lt_add (by
              simpa only [heq, dist_comm] using hpoint i) (hpoint j)
        _ ≤ (vertexRadius : ℝ) / 2 := by linarith
    linarith
  have hcross' : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0 := by
    apply hcrossStable vertex
    exact hvertex.trans_le (by
      dsimp only [eps]
      have hhalf : crossRadius / 2 ≤ crossRadius := by linarith
      exact (min_le_left _ _).trans hhalf)
  have hnonincident : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge vertex i)
        (kwRawClosedEdge vertex j) := by
    intro i j hij
    apply segment_disjoint_of_perturbation
      (le_of_lt (hpoint i)) (le_of_lt (hpoint (i + 1)))
      (le_of_lt (hpoint j)) (le_of_lt (hpoint (j + 1)))
      (hedgeSep i j hij)
    have hepsEdge : eps ≤ (edgeRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  exact {
    three_le := polygon.three_le
    vertex_injective := hinjective
    cross_ne_zero := hcross'
    nonincident_disjoint := hnonincident }





theorem KWFiniteSimplePolygon.exists_close_rational_polygon
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n),
      rational.vertex = kwRatVertex q ∧
      (∀ i : Fin n, dist (rational.vertex i) (polygon.vertex i) < 1) := by
  obtain ⟨crossRadius, hcrossRadius, hcrossStable⟩ :=
    exists_cross_stability_radius polygon.vertex (by
      simpa only [kwRawEdge, KWFiniteSimplePolygon.edgeVector] using hcross)
  obtain ⟨vertexRadius, hvertexRadius, hvertexSep⟩ :=
    polygon.exists_uniform_vertex_separation
  obtain ⟨edgeRadius, hedgeRadius, hedgeSep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  let eps : ℝ := min (1 / 2 : ℝ)
    (min (crossRadius / 2)
      (min ((vertexRadius : ℝ) / 4) ((edgeRadius : ℝ) / 4)))
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (by norm_num) (lt_min (half_pos hcrossRadius)
      (lt_min (by positivity) (by positivity)))
  obtain ⟨q, hq⟩ := (denseRange_kwRatVertex (n := n)).exists_mem_open
    (s := Metric.ball polygon.vertex eps) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr heps)
  have hqdist : dist (kwRatVertex q) polygon.vertex < eps := by
    simpa only [Metric.mem_ball] using hq
  have hqpoint (i : Fin n) :
      dist (kwRatVertex q i) (polygon.vertex i) < eps :=
    (dist_pi_lt_iff heps).mp hqdist i
  have hqinjective : Function.Injective (kwRatVertex q) := by
    intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri := dist_triangle (polygon.vertex i) (kwRatVertex q i)
      (polygon.vertex j)
    rw [heq] at htri
    have hcloseJ := hqpoint j
    have hepsVertex : eps ≤ (vertexRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _))
    have hpath : dist (polygon.vertex i) (polygon.vertex j) <
        (vertexRadius : ℝ) / 2 := by
      calc
        dist (polygon.vertex i) (polygon.vertex j) ≤
            dist (polygon.vertex i) (kwRatVertex q j) +
              dist (kwRatVertex q j) (polygon.vertex j) := htri
        _ < eps + eps := add_lt_add (by
              simpa only [heq, dist_comm] using hqpoint i) hcloseJ
        _ ≤ (vertexRadius : ℝ) / 2 := by linarith
    linarith
  have hqcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge (kwRatVertex q) i)
        (kwRawEdge (kwRatVertex q) (i + 1)) ≠ 0 := by
    apply hcrossStable (kwRatVertex q)
    exact hqdist.trans_le (by
      dsimp only [eps]
      have hhalf : crossRadius / 2 ≤ crossRadius := by linarith
      exact (min_le_right _ _).trans ((min_le_left _ _).trans hhalf))
  have hqnonincident : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge (kwRatVertex q) i)
        (kwRawClosedEdge (kwRatVertex q) j) := by
    intro i j hij
    apply segment_disjoint_of_perturbation
      (le_of_lt (hqpoint i)) (le_of_lt (hqpoint (i + 1)))
      (le_of_lt (hqpoint j)) (le_of_lt (hqpoint (j + 1)))
      (hedgeSep i j hij)
    have hepsEdge : eps ≤ (edgeRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_right _ _))
    linarith
  let data : KWRawSimplePolygonData (kwRatVertex q) :=
    { three_le := polygon.three_le
      vertex_injective := hqinjective
      cross_ne_zero := hqcross
      nonincident_disjoint := hqnonincident }
  let rational := data.toFiniteSimplePolygon
  refine ⟨q, rational, rfl, ?_⟩
  intro i
  exact (hqpoint i).trans_le (by
    dsimp only [eps]
    exact (min_le_left _ _).trans (by norm_num))

end StatMech.FrontierA
