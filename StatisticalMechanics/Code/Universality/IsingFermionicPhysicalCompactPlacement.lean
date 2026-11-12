/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointAnalyticAssembly











namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

private theorem abs_le_abs_of_mem_uIcc_zero
    {t h : Real} (ht : t ∈ Set.uIcc 0 h) : |t| ≤ |h| := by
  rcases Set.mem_uIcc.mp ht with ht | ht
  · rw [abs_of_nonneg ht.1, abs_of_nonneg (ht.1.trans ht.2)]
    exact ht.2
  · rw [abs_of_nonpos ht.2, abs_of_nonpos (ht.1.trans ht.2)]
    linarith

private theorem diagonal_displacement_le_two_abs
    (z : Complex) (t : Real) (sgn : Bool) :
    dist
        (z + (t : Complex) *
          (if sgn then 1 + Complex.I else 1 - Complex.I)) z ≤
      2 * |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real]
  have hdiag :
      ‖(if sgn then (1 + Complex.I : Complex) else 1 - Complex.I)‖ ≤ 2 := by
    cases sgn
    · calc
        ‖(1 - Complex.I : Complex)‖ ≤ ‖(1 : Complex)‖ + ‖Complex.I‖ :=
          norm_sub_le _ _
        _ = 2 := by norm_num
    · calc
        ‖(1 + Complex.I : Complex)‖ ≤ ‖(1 : Complex)‖ + ‖Complex.I‖ :=
          norm_add_le _ _
        _ = 2 := by norm_num
  rw [Real.norm_eq_abs]
  calc
    |t| * ‖(if sgn then (1 + Complex.I : Complex) else 1 - Complex.I)‖ ≤
        |t| * 2 := mul_le_mul_of_nonneg_left hdiag (abs_nonneg t)
    _ = 2 * |t| := by ring



theorem diagonalSegment_mapsTo_cthickening
    (K : Set Complex) (epsilon : Real) (z : Complex) (hz : z ∈ K) (h : Real)
    (hmesh : 2 * |h| ≤ epsilon) (sgn : Bool) :
    Set.MapsTo
      (fun t : Real => z + (t : Complex) *
        (if sgn then 1 + Complex.I else 1 - Complex.I))
      (Set.uIcc 0 h) (Metric.cthickening epsilon K) := by
  intro t ht
  apply Metric.mem_cthickening_of_dist_le _ z epsilon K hz
  exact (diagonal_displacement_le_two_abs z t sgn).trans
    ((mul_le_mul_of_nonneg_left
      (abs_le_abs_of_mem_uIcc_zero ht) (by norm_num)).trans hmesh)



theorem diagonalSegment_mapsTo_of_cthickening
    (U K : Set Complex) (epsilon : Real)
    (hKU : Metric.cthickening epsilon K ⊆ U)
    (z : Complex) (hz : z ∈ K) (h : Real)
    (hmesh : 2 * |h| ≤ epsilon) (sgn : Bool) :
    Set.MapsTo
      (fun t : Real => z + (t : Complex) *
        (if sgn then 1 + Complex.I else 1 - Complex.I))
      (Set.uIcc 0 h) U :=
  (diagonalSegment_mapsTo_cthickening K epsilon z hz h hmesh sgn).mono_right hKU





noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real)
    (hcollar : Metric.cthickening epsilon K ⊆ U)
    (hmesh : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    U (Metric.cthickening epsilon K) hU hK.cthickening hcollar hPhi
  · intro k x hfixed hghost hendpoint
    let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
    have hz : z ∈ K := hvertex k x hfixed hghost hendpoint
    exact ⟨
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) false,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) false⟩
  · intro k c hfixed hghost hendpoint
    let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
    have hz : z ∈ K := hface k c hfixed hghost hendpoint
    exact ⟨
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) false,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) false⟩



theorem exists_positive_compactAnalyticCollar
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ epsilon : Real, 0 < epsilon ∧
      Metric.cthickening epsilon K ⊆ U :=
  hK.exists_cthickening_subset_open hU hKU



theorem exists_shift_two_abs_mesh_le
    (mesh : Nat -> Real) (hmesh : Tendsto mesh atTop (nhds 0))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k0 : Nat, forall k, 2 * |mesh (k + k0)| ≤ epsilon := by
  have hscaled : Tendsto (fun k => 2 * |mesh k|) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmesh.abs
  have heventually : ∀ᶠ k in atTop, 2 * |mesh k| < epsilon :=
    (tendsto_order.1 hscaled).2 epsilon hepsilon
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨k0, fun k => (hk0 (k + k0) ?_).le⟩
  omega





noncomputable def PhysicalEndpointLayerIncrementData.ofLipschitzOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S K : Set Complex) (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ S)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius := by
  have hepsilon : 0 ≤ epsilon :=
    (mul_nonneg (by norm_num) (abs_nonneg (mesh 0))).trans
      (hmesh_collar 0)
  apply PhysicalEndpointLayerIncrementData.ofLipschitzOn
    S L hPhi hmesh_nonneg
  · intro k x hfixed hghost hendpoint
    have hx := hvertex k x hfixed hghost hendpoint
    constructor
    · exact hcollar (Metric.mem_cthickening_of_dist_le _ _ epsilon K hx
        (by simpa using hepsilon))
    · intro y hxy
      apply hcollar
      apply Metric.mem_cthickening_of_dist_le _
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) epsilon K hx
      exact (fullSquareScaledVertexEmbedding_dist_le_two_abs
        (N k) (mesh k) x y hxy).trans (hmesh_collar k)
  · intro k c hfixed hghost hendpoint
    have hc := hface k c hfixed hghost hendpoint
    constructor
    · exact hcollar (Metric.mem_cthickening_of_dist_le _ _ epsilon K hc
        (by simpa using hepsilon))
    · intro d hcd
      apply hcollar
      apply Metric.mem_cthickening_of_dist_le _
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) epsilon K hc
      exact (fullSquareScaledFaceEmbedding_dist_le_two_abs
        (N k) (mesh k) c d hcd).trans (hmesh_collar k)



theorem exists_fderiv_im_norm_bound_on_compact
    (Phi : Complex -> Complex) (U K : Set Complex)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U) :
    ∃ L : NNReal, forall w, w ∈ K ->
      ‖fderiv Real (fun z => (Phi z).im) w‖ ≤ L := by
  have hsmooth : ContDiffOn Real 1 (fun z => (Phi z).im) U :=
    contDiffOn_im_of_analyticOnNhd 1 Phi U hPhi
  have hcontinuous : ContinuousOn
      (fderiv Real (fun z => (Phi z).im)) K :=
    (hsmooth.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcontinuous
  let L : NNReal := ⟨max C 0, le_max_right C 0⟩
  refine ⟨L, fun w hw => (hC w hw).trans ?_⟩
  exact le_max_left C 0




noncomputable def PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ U)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius := by
  let K' := Metric.cthickening epsilon K
  let hex := exists_fderiv_im_norm_bound_on_compact
    Phi U K' hU hK.cthickening hcollar hPhi
  let L : NNReal := Classical.choose hex
  have hL : forall w, w ∈ K' ->
      ‖fderiv Real (fun z => (Phi z).im) w‖ ≤ L :=
    Classical.choose_spec hex
  have hsmooth : ContDiffOn Real 1 (fun z => (Phi z).im) U :=
    contDiffOn_im_of_analyticOnNhd 1 Phi U hPhi
  have hepsilon : 0 ≤ epsilon :=
    (mul_nonneg (by norm_num) (abs_nonneg (mesh 0))).trans
      (hmesh_collar 0)
  have hdifferentiable (w : Complex) (hw : w ∈ K') :
      DifferentiableAt Real (fun z => (Phi z).im) w :=
    (hsmooth.differentiableOn (by norm_num) w (hcollar hw)).differentiableAt
      (hU.mem_nhds (hcollar hw))
  refine
    { constant := 2 * L
      vertex := ?_
      face := ?_ }
  · intro k x hfixed hghost hendpoint y hxy
    let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
    let w := fullSquareScaledVertexEmbedding (N k) (mesh k) y
    have hz : z ∈ K := hvertex k x hfixed hghost hendpoint
    have hd : dist w z ≤ epsilon :=
      (fullSquareScaledVertexEmbedding_dist_le_two_abs
        (N k) (mesh k) x y hxy).trans (hmesh_collar k)
    have hball : Metric.closedBall z epsilon ⊆ K' :=
      Metric.closedBall_subset_cthickening hz epsilon
    have hdiff : ‖(Phi w).im - (Phi z).im‖ ≤
        (L : Real) * ‖w - z‖ :=
      (convex_closedBall z epsilon).norm_image_sub_le_of_norm_fderiv_le
        (fun q hq => hdifferentiable q (hball hq))
        (fun q hq => hL q (hball hq))
        (by simp [hepsilon]) (by simpa [Metric.mem_closedBall] using hd)
    change |(Phi w).im - (Phi z).im| ≤ (2 * L : NNReal) * mesh k
    rw [← Real.norm_eq_abs]
    calc
      ‖(Phi w).im - (Phi z).im‖ ≤ (L : Real) * ‖w - z‖ := hdiff
      _ = (L : Real) * dist w z := by rw [dist_eq_norm]
      _ ≤ (L : Real) * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh_nonneg k)]
        norm_num
        ring
  · intro k c hfixed hghost hendpoint d hcd
    let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
    let w := fullSquareScaledFaceEmbedding (N k) (mesh k) d
    have hz : z ∈ K := hface k c hfixed hghost hendpoint
    have hd : dist w z ≤ epsilon :=
      (fullSquareScaledFaceEmbedding_dist_le_two_abs
        (N k) (mesh k) c d hcd).trans (hmesh_collar k)
    have hball : Metric.closedBall z epsilon ⊆ K' :=
      Metric.closedBall_subset_cthickening hz epsilon
    have hdiff : ‖(Phi w).im - (Phi z).im‖ ≤
        (L : Real) * ‖w - z‖ :=
      (convex_closedBall z epsilon).norm_image_sub_le_of_norm_fderiv_le
        (fun q hq => hdifferentiable q (hball hq))
        (fun q hq => hL q (hball hq))
        (by simp [hepsilon]) (by simpa [Metric.mem_closedBall] using hd)
    change |(Phi w).im - (Phi z).im| ≤ (2 * L : NNReal) * mesh k
    rw [← Real.norm_eq_abs]
    calc
      ‖(Phi w).im - (Phi z).im‖ ≤ (L : Real) * ‖w - z‖ := hdiff
      _ = (L : Real) * dist w z := by rw [dist_eq_norm]
      _ ≤ (L : Real) * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh_nonneg k)]
        norm_num
        ring



def isingFermionicClosedUnitStrip : Set Complex :=
  {z | 0 ≤ z.im ∧ z.im ≤ 1}



def physicalFullSquareSampleCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      z = fullSquareScaledVertexEmbedding (N k) (mesh k) x) ∨
    (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      z = fullSquareScaledFaceEmbedding (N k) (mesh k) c)}



def physicalFullSquareLowerTraceCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      fkIsingSquareFullVertexFixedBoundary (N k) x ∧
        z = fullSquareScaledVertexEmbedding (N k) (mesh k) x) ∨
    (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ∧
        z = fullSquareScaledFaceEmbedding (N k) (mesh k) c)}



def physicalFullSquareUpperTraceCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      fkIsingSquareFullFaceFixedBoundary (N k) c ∧
        z = fullSquareScaledFaceEmbedding (N k) (mesh k) c) ∨
    (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ∧
        z = fullSquareScaledVertexEmbedding (N k) (mesh k) x)}




structure PhysicalStripMapTraceRangeData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) : Prop where
  range : Set.MapsTo Phi
    (physicalFullSquareSampleCarrier N mesh)
    isingFermionicClosedUnitStrip
  lowerTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
    (physicalFullSquareLowerTraceCarrier N mesh)
  upperTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
    (physicalFullSquareUpperTraceCarrier N mesh)

theorem PhysicalStripMapTraceRangeData.vertexRange
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k)) :
    0 ≤ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ∧
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ≤ 1 := by
  exact H.range (Or.inl ⟨k, x, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceRange
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k)) :
    0 ≤ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ∧
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ≤ 1 := by
  exact H.range (Or.inr ⟨k, c, rfl⟩)

theorem PhysicalStripMapTraceRangeData.vertexFixed
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hx : fkIsingSquareFullVertexFixedBoundary (N k) x) :
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0 :=
  H.lowerTrace (Or.inl ⟨k, x, hx, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceFixed
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hc : fkIsingSquareFullFaceFixedBoundary (N k) c) :
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1 :=
  H.upperTrace (Or.inl ⟨k, c, hc, rfl⟩)

theorem PhysicalStripMapTraceRangeData.vertexFree
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) :
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1 :=
  H.upperTrace (Or.inr ⟨k, x, hfixed, hghost, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceFree
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) :
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0 :=
  H.lowerTrace (Or.inr ⟨k, c, hfixed, hghost, rfl⟩)




theorem PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (Hstrip : PhysicalStripMapTraceRangeData N Phi mesh)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
  apply PhysicalEndpointLocalizedRobinInputs.ofLocalizedSegmentFourthOrderAndRange
    (fun k => 4 * Hlayer.constant * mesh k) Hfourth hmesh_nonneg
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) Hlayer.constant.2)
      (hmesh_nonneg k)
  · exact Hstrip.vertexFixed
  · exact Hstrip.faceFixed
  · exact Hstrip.vertexFree
  · exact Hstrip.faceFree
  · exact Hlayer.vertexLaplacian hmesh_nonneg
  · exact Hlayer.faceLaplacian hmesh_nonneg
  · exact Hstrip.vertexRange
  · exact Hstrip.faceRange
  · exact hscaledFourth_tendsto
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hmesh_tendsto





noncomputable def
    PhysicalEndpointLocalizedRobinInputs.ofAnalyticOnCompactCentersAndStripMap
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ U)
    (Hstrip : PhysicalStripMapTraceRangeData N Phi mesh)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        let H :=
          PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
            U K hU hK hPhi epsilon hcollar hmesh_collar
              (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
              (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k =>
        let H :=
          PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
            U K hU hK hPhi epsilon hcollar hmesh_nonneg hmesh_collar
              (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
              (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
        4 * H.constant * mesh k)
      (fun _ => 4) := by
  let Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius :=
    PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
      U K hU hK hPhi epsilon hcollar hmesh_collar
        (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
        (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
  let Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius :=
    PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
      U K hU hK hPhi epsilon hcollar hmesh_nonneg hmesh_collar
        (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
        (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
  exact PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap
    Hfourth Hlayer Hstrip hmesh_nonneg hscaledFourth_tendsto hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
