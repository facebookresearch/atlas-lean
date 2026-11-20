/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointInputAssembly
import Code.Universality.IsingFermionicAnalyticFourthOrder
import Code.Universality.IsingFermionicLocalFourthOrder








namespace StatMech.Universality

open Filter Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



structure LocalDiagonalFourthOrderAnalyticData
    (Phi : Complex -> Complex) (z : Complex) (h boundOne boundTwo : Real) :
    Prop where
  one : CenteredFourthOrderSegmentData
    (fun t : Real =>
      (Phi (z + (t : Complex) * (1 + Complex.I))).im) h boundOne
  two : CenteredFourthOrderSegmentData
    (fun t : Real =>
      (Phi (z + (t : Complex) * (1 - Complex.I))).im) h boundTwo
  analytic : AnalyticAt Complex Phi z



theorem LocalDiagonalFourthOrderAnalyticData.stencil
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (H : LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo) :
    |complexDirectionalFourNeighborStencil (fun w => (Phi w).im) z
      (1 + Complex.I) (1 - Complex.I) h| <=
        (boundOne + boundTwo) * |h| ^ 4 / 12 := by
  apply complexDirectionalFourNeighborStencil_le_of_segmentData
    (fun w => (Phi w).im) z (1 + Complex.I) (1 - Complex.I)
      h boundOne boundTwo H.one H.two
  exact harmonicAt_diagonal_iteratedDeriv_add_eq_zero
    (fun w => (Phi w).im) z H.analytic.harmonicAt_im




theorem LocalDiagonalFourthOrderAnalyticData.ofOpenLineData
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hsmoothOne : ContDiffOn Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 + Complex.I))).im) UOne)
    (hsmoothTwo : ContDiffOn Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 - Complex.I))).im) UTwo)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo where
  one := CenteredFourthOrderSegmentData.ofContDiffOn
    hUOne hzeroOne hpositiveOne hnegativeOne hsmoothOne hboundOne
  two := CenteredFourthOrderSegmentData.ofContDiffOn
    hUTwo hzeroTwo hpositiveTwo hnegativeTwo hsmoothTwo hboundTwo
  analytic := hanalytic




theorem LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo := by
  apply LocalDiagonalFourthOrderAnalyticData.ofOpenLineData
    UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo
  · exact contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 + Complex.I) UOne hsmooth hmapsOne
  · exact contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 - Complex.I) UTwo hsmooth hmapsTwo
  · exact hboundOne
  · exact hboundTwo
  · exact hanalytic




theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hPhi : AnalyticOnNhd Complex Phi U) (hz : z ∈ U)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo := by
  apply LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData
    U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo hmapsOne hmapsTwo
  · exact contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  · exact hboundOne
  · exact hboundTwo
  · exact hPhi z hz



theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hU : IsOpen U) (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hPhi : AnalyticOnNhd Complex Phi U) (hz : z ∈ U)
    (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  have hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U :=
    contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd
    U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo hmapsOne hmapsTwo hPhi hz
  · intro t ht
    have hbound := abs_iteratedDeriv_complexLine_four_le_tensorNormOn
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hmapsOne ht) htensor
    simpa [norm_one_add_I_pow_four, mul_comm] using hbound
  · intro t ht
    have hbound := abs_iteratedDeriv_complexLine_four_le_tensorNormOn
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hmapsTwo ht) htensor
    simpa [norm_one_sub_I_pow_four, mul_comm] using hbound





theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (hU : IsOpen U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) U)
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) U)
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) U)
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) U) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  let lineOne : Real -> Complex :=
    fun t => z + (t : Complex) * (1 + Complex.I)
  let lineTwo : Real -> Complex :=
    fun t => z + (t : Complex) * (1 - Complex.I)
  let UOne : Set Real := lineOne ⁻¹' U
  let UTwo : Set Real := lineTwo ⁻¹' U
  have hlineOne : Continuous lineOne := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 + Complex.I)
    simpa [lineOne, g] using (continuous_const.add g.continuous)
  have hlineTwo : Continuous lineTwo := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 - Complex.I)
    simpa [lineTwo, g] using (continuous_const.add g.continuous)
  have hUOne : IsOpen UOne := hU.preimage hlineOne
  have hUTwo : IsOpen UTwo := hU.preimage hlineTwo
  have hzeroOne : 0 ∈ UOne := by
    exact hpositiveOne Set.left_mem_uIcc
  have hzeroTwo : 0 ∈ UTwo := by
    exact hpositiveTwo Set.left_mem_uIcc
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn
    U UOne UTwo hU hUOne hUTwo hzeroOne hzeroTwo
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo
  · exact Set.mapsTo_preimage lineOne U
  · exact Set.mapsTo_preimage lineTwo U
  · exact hPhi
  · simpa using hpositiveOne Set.left_mem_uIcc
  · exact htensor




theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U K : Set Complex) (hU : IsOpen U) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ K ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) K)
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) K)
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) K)
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) K) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  let lineOne : Real -> Complex :=
    fun t => z + (t : Complex) * (1 + Complex.I)
  let lineTwo : Real -> Complex :=
    fun t => z + (t : Complex) * (1 - Complex.I)
  let UOne : Set Real := lineOne ⁻¹' U
  let UTwo : Set Real := lineTwo ⁻¹' U
  have hlineOne : Continuous lineOne := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 + Complex.I)
    simpa [lineOne, g] using (continuous_const.add g.continuous)
  have hlineTwo : Continuous lineTwo := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 - Complex.I)
    simpa [lineTwo, g] using (continuous_const.add g.continuous)
  have hUOne : IsOpen UOne := hU.preimage hlineOne
  have hUTwo : IsOpen UTwo := hU.preimage hlineTwo
  have hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U :=
    contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  have hsmoothOne : ContDiffOn Real 4
      (fun t : Real => (Phi (lineOne t)).im) UOne :=
    contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 + Complex.I) UOne hsmooth
        (Set.mapsTo_preimage lineOne U)
  have hsmoothTwo : ContDiffOn Real 4
      (fun t : Real => (Phi (lineTwo t)).im) UTwo :=
    contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 - Complex.I) UTwo hsmooth
        (Set.mapsTo_preimage lineTwo U)
  have hzK : z ∈ K := by
    simpa [lineOne] using hpositiveOne Set.left_mem_uIcc
  refine {
    one := {
      atZero := ?_
      positive := ?_
      negative := ?_
      fourthPositive := ?_
      fourthNegative := ?_ }
    two := {
      atZero := ?_
      positive := ?_
      negative := ?_
      fourthPositive := ?_
      fourthNegative := ?_ }
    analytic := hPhi z (hKU hzK) }
  · simpa [lineOne] using
      hsmoothOne.contDiffAt (hUOne.mem_nhds (show (0 : Real) ∈ UOne by
        exact hKU (hpositiveOne Set.left_mem_uIcc)))
  · exact hsmoothOne.mono (fun t ht => hKU (hpositiveOne ht))
  · exact hsmoothOne.mono (fun t ht => hKU (hnegativeOne ht))
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hKU (hpositiveOne ht)) (htensor _ (hpositiveOne ht))
    simpa [lineOne, norm_one_add_I_pow_four, mul_comm] using hb
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hKU (hnegativeOne ht)) (htensor _ (hnegativeOne ht))
    simpa [lineOne, norm_one_add_I_pow_four, mul_comm] using hb
  · simpa [lineTwo] using
      hsmoothTwo.contDiffAt (hUTwo.mem_nhds (show (0 : Real) ∈ UTwo by
        exact hKU (hpositiveTwo Set.left_mem_uIcc)))
  · exact hsmoothTwo.mono (fun t ht => hKU (hpositiveTwo ht))
  · exact hsmoothTwo.mono (fun t ht => hKU (hnegativeTwo ht))
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hKU (hpositiveTwo ht)) (htensor _ (hpositiveTwo ht))
    simpa [lineTwo, norm_one_sub_I_pow_four, mul_comm] using hb
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hKU (hnegativeTwo ht)) (htensor _ (hnegativeTwo ht))
    simpa [lineTwo, norm_one_sub_I_pow_four, mul_comm] using hb



theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnConvex
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (hUOpen : IsOpen U) (hUConvex : Convex Real U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hz : z ∈ U)
    (hpositiveOne : z + (h : Complex) * (1 + Complex.I) ∈ U)
    (hnegativeOne : z + ((-h : Real) : Complex) *
      (1 + Complex.I) ∈ U)
    (hpositiveTwo : z + (h : Complex) * (1 - Complex.I) ∈ U)
    (hnegativeTwo : z + ((-h : Real) : Complex) *
      (1 - Complex.I) ∈ U) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    U hUOpen hPhi M htensor
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 + Complex.I) h hz hpositiveOne
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 + Complex.I) (-h) hz hnegativeOne
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 - Complex.I) h hz hpositiveTwo
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 - Complex.I) (-h) hz hnegativeTwo



structure PhysicalEndpointSegmentFourthOrderBulkData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  boundOne : Real
  boundTwo : Real
  boundSum_nonneg : 0 <= boundOne + boundTwo
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      LocalDiagonalFourthOrderAnalyticData Phi
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        (mesh k) boundOne boundTwo
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      LocalDiagonalFourthOrderAnalyticData Phi
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        (mesh k) boundOne boundTwo



noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Set Complex) (hU : IsOpen U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) U)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) U) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius where
  boundOne := 4 * (M : Real)
  boundTwo := 4 * (M : Real)
  boundSum_nonneg := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      U hU hPhi M htensor hpositiveOne hnegativeOne
        hpositiveTwo hnegativeTwo
  face k c hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      U hU hPhi M htensor hpositiveOne hnegativeOne
        hpositiveTwo hnegativeTwo




noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  let hex :=
    exists_iteratedFDeriv_norm_bound_on_compact Phi U K hU hK hKU hPhi
  let M : NNReal := Classical.choose hex
  have hM : forall w, w ∈ K ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M :=
    Classical.choose_spec hex
  exact {
    boundOne := 4 * (M : Real)
    boundTwo := 4 * (M : Real)
    boundSum_nonneg := by positivity
    vertex := fun k x hfixed hghost hendpoint => by
      obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
        hvertex k x hfixed hghost hendpoint
      exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
        U K hU hKU hPhi M hM hpositiveOne hnegativeOne
          hpositiveTwo hnegativeTwo
    face := fun k c hfixed hghost hendpoint => by
      obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
        hface k c hfixed hghost hendpoint
      exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
        U K hU hKU hPhi M hM hpositiveOne hnegativeOne
          hpositiveTwo hnegativeTwo }



noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hKConvex : Convex Real K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      z ∈ K ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ K ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      z ∈ K ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ K ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    U K hU hK hKU hPhi
  · intro k x hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeTwo⟩
  · intro k c hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeTwo⟩




noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Set Complex) (hUOpen : IsOpen U) (hUConvex : Convex Real U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      z ∈ U ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ U ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ U)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      z ∈ U ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ U ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ U) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    U hUOpen hPhi M htensor
  · intro k x hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeTwo⟩
  · intro k c hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeTwo⟩

theorem PhysicalEndpointSegmentFourthOrderBulkData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) x
      heast hnorth hwest hsouth]
  exact (H.vertex k x hfixed hghost hendpoint).stencil

theorem PhysicalEndpointSegmentFourthOrderBulkData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) c
      heast hnorth hwest hsouth]
  exact (H.face k c hfixed hghost hendpoint).stencil



theorem PhysicalEndpointLocalizedRobinInputs.ofLocalizedSegmentFourthOrderAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} (layerRate : Nat -> Real)
    (Hfourth : PhysicalEndpointSegmentFourthOrderBulkData
      N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hlayer_nonneg : forall k, 0 <= layerRate k)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hvertexLayer : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
          (fun y => (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| <= layerRate k)
    (hfaceLayer : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
          (fun d => (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| <= layerRate k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2)
      atTop (nhds 0))
    (hlayer_tendsto : Tendsto layerRate atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      layerRate (fun _ => 4) := by
  refine
    { mesh_nonneg := hmesh_nonneg
      bulk_nonneg := ?_
      layer_nonneg := hlayer_nonneg
      endpoint_nonneg := fun _ => by norm_num
      vertexFixed := hvertexFixed
      faceFixed := hfaceFixed
      vertexFree := hvertexFree
      faceFree := hfaceFree
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := hvertexLayer
      faceLayer := hfaceLayer
      vertexEndpoint := ?_
      faceEndpoint := ?_
      scaledBulk_tendsto := ?_
      layer_tendsto := hlayer_tendsto
      mesh_tendsto := hmesh_tendsto }
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · exact fun k x hfixed hghost hendpoint =>
      Hfourth.vertexLaplacian k x hfixed hghost hendpoint
  · exact fun k c hfixed hghost hendpoint =>
      Hfourth.faceLaplacian k c hfixed hghost hendpoint
  · intro k x _hfixed _hendpoint
    exact fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k))
      Phi (hvertexRange k) x
  · intro k c _hfixed _hendpoint
    exact fullSquareFace_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k))
      Phi (hfaceRange k) c
  · have hconstant : Tendsto
        (fun _ : Nat => (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct



noncomputable def PhysicalEndpointFourthOrderBulkData.ofAnalyticTensorNorm
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (M : NNReal)
    (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
    (htensor : forall w,
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        AnalyticAt Complex Phi
          (fullSquareScaledVertexEmbedding (N k) (mesh k) x))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        AnalyticAt Complex Phi
          (fullSquareScaledFaceEmbedding (N k) (mesh k) c)) :
    PhysicalEndpointFourthOrderBulkData N Phi mesh radius where
  boundOne := 4 * M
  boundTwo := 4 * M
  boundSum_nonneg := by positivity
  vertex k x hfixed hghost hendpoint :=
    DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm
      Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x) M
      hsmooth htensor (hvertex k x hfixed hghost hendpoint)
  face k c hfixed hghost hendpoint :=
    DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm
      Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c) M
      hsmooth htensor (hface k c hfixed hghost hendpoint)

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
