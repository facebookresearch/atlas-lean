/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicAxisStaircaseApproximation





namespace StatMech.Universality

open Filter Set Topology

noncomputable section



private theorem axisTwoEdgeStaircaseBaseSet_near_axisSnap_mem_closedBall
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {mesh : Real} (hmesh : 0 < mesh) (hmeshOne : mesh ≤ 1)
    {a q : Complex}
    (ha : a ∈ axisTwoEdgeStaircaseBaseSet
      (reflectedRadialAxisSnap mesh z).re
      (reflectedRadialAxisSnap mesh z).im mesh
      (reflectedRadialAxisSnapWidth mesh z w)
      (reflectedRadialAxisSnapHeight mesh z w))
    (hqa : norm (q - a) ≤ 2 * mesh) :
    q ∈ Metric.closedBall z
      (w.re - z.re + (w.im - z.im) + 6) := by
  have hwidth := reflectedRadialAxisSnapWidth_mul_mesh_le
    mesh z w hmesh hre
  have hheight := reflectedRadialAxisSnapHeight_mul_mesh_le
    mesh z w hmesh him
  have hbaseGeom := axisTwoEdgeStaircase_base_norm_le
    (reflectedRadialAxisSnap mesh z).re
    (reflectedRadialAxisSnap mesh z).im mesh
    (reflectedRadialAxisSnapWidth mesh z w)
    (reflectedRadialAxisSnapHeight mesh z w) hmesh.le
  have hap : norm (a - reflectedRadialAxisSnap mesh z) ≤
      (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh +
        (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh := by
    rcases ha with ⟨k, hk, rfl⟩ | ⟨⟨k, hk, rfl⟩ |
        ⟨⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩⟩⟩
    · simpa [Complex.re_add_im] using hbaseGeom.1 k hk
    · simpa [Complex.re_add_im] using hbaseGeom.2.1 k hk
    · simpa [Complex.re_add_im] using hbaseGeom.2.2.1 k hk
    · simpa [Complex.re_add_im] using hbaseGeom.2.2.2 k hk
  have hsnapDist := reflectedRadialAxisSnap_dist_lt mesh z hmesh
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    norm (q - z) ≤ norm (q - a) +
        norm (a - reflectedRadialAxisSnap mesh z) +
        norm (reflectedRadialAxisSnap mesh z - z) := by
      have h := norm_add_le (q - a)
        ((a - reflectedRadialAxisSnap mesh z) +
          (reflectedRadialAxisSnap mesh z - z))
      have h' := norm_add_le (a - reflectedRadialAxisSnap mesh z)
        (reflectedRadialAxisSnap mesh z - z)
      calc
        norm (q - z) = norm ((q - a) +
            ((a - reflectedRadialAxisSnap mesh z) +
              (reflectedRadialAxisSnap mesh z - z))) := by congr 1 <;> abel
        _ ≤ norm (q - a) + norm ((a - reflectedRadialAxisSnap mesh z) +
              (reflectedRadialAxisSnap mesh z - z)) := h
        _ ≤ norm (q - a) +
            (norm (a - reflectedRadialAxisSnap mesh z) +
              norm (reflectedRadialAxisSnap mesh z - z)) :=
          by nlinarith [h']
        _ = _ := by ring
    _ ≤ 2 * mesh +
        ((reflectedRadialAxisSnapWidth mesh z w : Real) * mesh +
          (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh) +
        2 * mesh := by
      gcongr
      simpa [dist_eq_norm] using hsnapDist.le
    _ ≤ w.re - z.re + (w.im - z.im) + 6 := by
      linarith


private theorem axisTwoEdgeStaircaseBaseSet_axisSnap_mem_closedBall
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {mesh : Real} (hmesh : 0 < mesh) (hmeshOne : mesh ≤ 1)
    {a : Complex}
    (ha : a ∈ axisTwoEdgeStaircaseBaseSet
      (reflectedRadialAxisSnap mesh z).re
      (reflectedRadialAxisSnap mesh z).im mesh
      (reflectedRadialAxisSnapWidth mesh z w)
      (reflectedRadialAxisSnapHeight mesh z w)) :
    a ∈ Metric.closedBall z
      (w.re - z.re + (w.im - z.im) + 6) := by
  apply axisTwoEdgeStaircaseBaseSet_near_axisSnap_mem_closedBall
    z w hre him hmesh hmeshOne ha
  simp [hmesh.le]



private theorem norm_axisMacroDirectContour_le_of_axisStaircase_eq_zero
    (F f : Complex -> Complex) (hF : Continuous F) (hf : Continuous f)
    (x y mesh epsilon : Real) (width height : Nat)
    (hmesh : 0 < mesh) (hepsilon : 0 ≤ epsilon)
    (hosc : ∀ a, a ∈ axisTwoEdgeStaircaseBaseSet
        x y mesh width height -> ∀ q,
      norm (q - a) ≤ 2 * mesh -> norm (f q - f a) ≤ epsilon)
    (hfield : ∀ a, a ∈ axisTwoEdgeStaircaseBaseSet
        x y mesh width height -> ∀ q,
      norm (q - a) ≤ 2 * mesh -> norm (F q - f q) ≤ epsilon)
    (hzero : axisTwoEdgeStaircasePathIntegral F
      x y mesh width height = 0) :
    norm (axisMacroDirectContour f x y mesh width height) ≤
      12 * epsilon * mesh * ((width + height : Nat) : Real) := by
  have hdetour :=
    norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation
      f hf x y mesh epsilon width height hmesh hepsilon hosc
  have hfieldPath :=
    norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_baseError
      F f hF hf x y mesh width height epsilon hmesh hepsilon hfield
  calc
    norm (axisMacroDirectContour f x y mesh width height) ≤
        norm (axisMacroDirectContour f x y mesh width height -
          axisTwoEdgeStaircasePathIntegral f x y mesh width height) +
        norm (axisTwoEdgeStaircasePathIntegral f x y mesh width height -
          axisTwoEdgeStaircasePathIntegral F x y mesh width height) := by
      rw [hzero, sub_zero]
      have htri := norm_add_le
        (axisMacroDirectContour f x y mesh width height -
          axisTwoEdgeStaircasePathIntegral f x y mesh width height)
        (axisTwoEdgeStaircasePathIntegral f x y mesh width height)
      convert htri using 1 <;> abel_nf
    _ ≤ 8 * epsilon * mesh * ((width + height : Nat) : Real) +
        4 * epsilon * mesh * ((width + height : Nat) : Real) := by
      gcongr
      · simpa [norm_sub_rev] using hdetour
      · simpa [norm_sub_rev] using hfieldPath
    _ = 12 * epsilon * mesh * ((width + height : Nat) : Real) := by ring

set_option maxHeartbeats 800000 in




private theorem fkIsingExpandingBoundarySquare_axisMacroDirectContour_tendsto_zero
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn
      (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
        (sigma r)) f atTop Set.univ)
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    Tendsto (fun r =>
      axisMacroDirectContour f
        (reflectedRadialAxisSnap (fkIsingExpandingSquareScale (sigma r)) z).re
        (reflectedRadialAxisSnap (fkIsingExpandingSquareScale (sigma r)) z).im
        (fkIsingExpandingSquareScale (sigma r))
        (reflectedRadialAxisSnapWidth
          (fkIsingExpandingSquareScale (sigma r)) z w)
        (reflectedRadialAxisSnapHeight
          (fkIsingExpandingSquareScale (sigma r)) z w))
      atTop (nhds 0) := by
  let mesh : Nat -> Real := fun r => fkIsingExpandingSquareScale (sigma r)
  let side : Nat -> Nat := fun r => fkIsingExpandingSquareSide (sigma r)
  let F : Nat -> Complex -> Complex := fun r =>
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant (sigma r)
  let snap : Nat -> Complex -> Complex := fun r q =>
    reflectedRadialAxisSnap (mesh r) q
  let width : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapWidth (mesh r) z w
  let height : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapHeight (mesh r) z w
  let i0 : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapBaseI (side r) (mesh r) z w
  let j0 : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapBaseJ (side r) (mesh r) z
  let spanBound : Real := w.re - z.re + (w.im - z.im) + 2
  let radius : Real := w.re - z.re + (w.im - z.im) + 6
  let K : Set Complex := Metric.closedBall z radius
  have hmeshPos : ∀ r, 0 < mesh r := fun r =>
    fkIsingExpandingSquareScale_pos (sigma r)
  have hmeshZero : Tendsto mesh atTop (nhds 0) := by
    exact fkIsingExpandingSquareScale_tendsto_zero.comp hsigma
  have hf : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall fun r =>
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
        (sigma r)).continuousOn))
  have hKcompact : IsCompact K := isCompact_closedBall z radius
  have hKuniform : TendstoUniformlyOn F f atTop K := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      hKcompact).mp
    simpa [F] using hlimit.mono (subset_univ K)
  have hfuniform : UniformContinuousOn f K :=
    hKcompact.uniformContinuousOn_of_continuous hf.continuousOn
  have haxisTendsto : Tendsto (fun r =>
      axisMacroDirectContour f (snap r z).re (snap r z).im
        (mesh r) (width r) (height r)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let eta : Real := epsilon / (24 * (spanBound + 1))
    have hspanNonneg : 0 ≤ spanBound := by
      dsimp only [spanBound]
      linarith
    have heta : 0 < eta := by
      dsimp only [eta]
      positivity
    obtain ⟨delta, hdelta, hmod⟩ :=
      (Metric.uniformContinuousOn_iff.mp hfuniform) eta heta
    have hsmall : ∀ᶠ r in atTop, mesh r < min 1 (delta / 2) :=
      (tendsto_order.1 hmeshZero).2 _ (by positivity)
    have huniform : ∀ᶠ r in atTop, ∀ q ∈ K,
        dist (f q) (F r q) < eta := by
      rw [Metric.tendstoUniformlyOn_iff] at hKuniform
      exact hKuniform eta heta
    have hinterior : ∀ᶠ r in atTop,
        0 ≤ (side r : Int) + ⌊z.re / mesh r - 1 / 2⌋ -
            ⌊w.im / mesh r⌋ ∧
        0 ≤ (side r : Int) + ⌊z.re / mesh r - 1 / 2⌋ +
            ⌊z.im / mesh r⌋ ∧
        i0 r + width r + height r + 1 < 2 * side r ∧
        j0 r + width r + height r + 1 < 2 * side r := by
      simpa [side, mesh, i0, j0, width, height] using
        hsigma.eventually
          (fkIsingExpandingSquare_eventually_axisSnap_interior z w hre him)
    have hzero : ∀ᶠ r in atTop,
        reflectedRadialAxisStaircasePathIntegral
            (F r) (mesh r) (side r) (i0 r) (j0 r)
            (width r) (height r) = 0 := by
      simpa [F, side, mesh, i0, j0, width, height] using
        hsigma.eventually
          (fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero
            z w hre him)
    apply Filter.eventually_atTop.mp
    filter_upwards [hsmall, huniform, hinterior, hzero] with r
      hrsmall hruniform hrinterior hrzero
    have hm1 : mesh r ≤ 1 := (lt_min_iff.mp hrsmall).1.le
    have hmDelta : 2 * mesh r < delta := by
      have := (lt_min_iff.mp hrsmall).2
      linarith
    have hwidth := reflectedRadialAxisSnapWidth_mul_mesh_le
      (mesh r) z w (hmeshPos r) hre
    have hheight := reflectedRadialAxisSnapHeight_mul_mesh_le
      (mesh r) z w (hmeshPos r) him
    have hspan : (width r : Real) * mesh r +
        (height r : Real) * mesh r ≤ spanBound := by
      dsimp only [width, height, spanBound]
      linarith
    have hnearK : ∀ a,
        a ∈ axisTwoEdgeStaircaseBaseSet
          (snap r z).re (snap r z).im (mesh r) (width r) (height r) ->
        ∀ q, norm (q - a) ≤ 2 * mesh r -> q ∈ K := by
      intro a ha q hqa
      simpa [K, radius, snap, width, height] using
        axisTwoEdgeStaircaseBaseSet_near_axisSnap_mem_closedBall
          z w hre him (hmeshPos r) hm1 ha hqa
    have hbaseK : ∀ a,
        a ∈ axisTwoEdgeStaircaseBaseSet
          (snap r z).re (snap r z).im (mesh r) (width r) (height r) ->
        a ∈ K := by
      intro a ha
      simpa [K, radius, snap, width, height] using
        axisTwoEdgeStaircaseBaseSet_axisSnap_mem_closedBall
          z w hre him (hmeshPos r) hm1 ha
    have hosc : ∀ a,
        a ∈ axisTwoEdgeStaircaseBaseSet
          (snap r z).re (snap r z).im (mesh r) (width r) (height r) ->
        ∀ q, norm (q - a) ≤ 2 * mesh r ->
          norm (f q - f a) ≤ eta := by
      intro a ha q hqa
      have haq : dist a q < delta := by
        rw [dist_eq_norm, norm_sub_rev]
        exact hqa.trans_lt hmDelta
      have h := hmod a (hbaseK a ha) q (hnearK a ha q hqa) haq
      simpa [dist_eq_norm, norm_sub_rev] using h.le
    have hfield : ∀ a,
        a ∈ axisTwoEdgeStaircaseBaseSet
          (snap r z).re (snap r z).im (mesh r) (width r) (height r) ->
        ∀ q, norm (q - a) ≤ 2 * mesh r ->
          norm (F r q - f q) ≤ eta := by
      intro a ha q hqa
      have h := hruniform q (hnearK a ha q hqa)
      simpa [dist_eq_norm, norm_sub_rev] using h.le
    have hbasePosition :=
      isingReflectedCenteredRadialGridPosition_axisSnapBase
        (side r) (mesh r) z w (hmeshPos r) him
        hrinterior.1 hrinterior.2.1
    have haxisZero :
        axisTwoEdgeStaircasePathIntegral (F r)
          (snap r z).re (snap r z).im (mesh r) (width r) (height r) = 0 := by
      have hpath := reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge
        (F r) (mesh r) (side r) (i0 r) (j0 r) (width r) (height r)
      dsimp only at hpath
      rw [hbasePosition] at hpath
      rw [← hpath]
      exact hrzero
    have hbound := norm_axisMacroDirectContour_le_of_axisStaircase_eq_zero
      (F r) f
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
        (sigma r)) hf
      (snap r z).re (snap r z).im (mesh r) eta
      (width r) (height r) (hmeshPos r) heta.le hosc hfield haxisZero
    calc
      dist (axisMacroDirectContour f (snap r z).re (snap r z).im
          (mesh r) (width r) (height r)) 0 =
        norm (axisMacroDirectContour f (snap r z).re (snap r z).im
          (mesh r) (width r) (height r)) := by simp [dist_eq_norm]
      _ ≤ 12 * eta * mesh r * (width r + height r : Nat) := hbound
      _ < epsilon := by
        have hlen : mesh r * (width r + height r : Nat) ≤ spanBound := by
          push_cast
          nlinarith
        dsimp only [eta]
        have hden : 0 < spanBound + 1 := by linarith
        have hcoef : 0 ≤ 12 * (epsilon / (24 * (spanBound + 1))) := by
          positivity
        calc
          12 * (epsilon / (24 * (spanBound + 1))) * mesh r *
                (width r + height r : Nat) =
              12 * (epsilon / (24 * (spanBound + 1))) *
                (mesh r * (width r + height r : Nat)) := by ring
          _ ≤ 12 * (epsilon / (24 * (spanBound + 1))) * spanBound :=
            mul_le_mul_of_nonneg_left hlen hcoef
          _ < epsilon := by
            field_simp
            nlinarith
  simpa [mesh, snap, width, height] using haxisTendsto



private theorem axisMacroDirectContour_reflectedRadialAxisSnap_eq_wedgeContour
    (f : Complex -> Complex) (hf : Continuous f) (z w : Complex)
    {mesh : Real} (hmesh : 0 < mesh)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    axisMacroDirectContour f
        (reflectedRadialAxisSnap mesh z).re
        (reflectedRadialAxisSnap mesh z).im mesh
        (reflectedRadialAxisSnapWidth mesh z w)
        (reflectedRadialAxisSnapHeight mesh z w) =
      Complex.wedgeIntegral (reflectedRadialAxisSnap mesh z)
          (reflectedRadialAxisSnap mesh w) f +
        Complex.wedgeIntegral (reflectedRadialAxisSnap mesh w)
          (reflectedRadialAxisSnap mesh z) f := by
  rw [axisMacroDirectContour_eq_wedgeContour f hf]
  have hopposite := reflectedRadialAxisSnap_oppositeCorner
    mesh z w hmesh hre him
  rw [Complex.re_add_im]
  rw [← hopposite]
  simp [reflectedRadialAxisSnap]

set_option maxHeartbeats 300000 in



private theorem reflectedRadialAxisSnap_wedgeContour_tendsto
    (f : Complex -> Complex) (hf : Continuous f)
    (mesh : Nat -> Real) (hmeshPos : ∀ r, 0 < mesh r)
    (hmeshZero : Tendsto mesh atTop (nhds 0))
    (z w : Complex) :
    Tendsto (fun r =>
      Complex.wedgeIntegral (reflectedRadialAxisSnap (mesh r) z)
          (reflectedRadialAxisSnap (mesh r) w) f +
        Complex.wedgeIntegral (reflectedRadialAxisSnap (mesh r) w)
          (reflectedRadialAxisSnap (mesh r) z) f) atTop
      (nhds (Complex.wedgeIntegral z w f +
        Complex.wedgeIntegral w z f)) := by
  have hsnapZ := reflectedRadialAxisSnap_tendsto mesh hmeshPos hmeshZero z
  have hsnapW := reflectedRadialAxisSnap_tendsto mesh hmeshPos hmeshZero w
  have hendpoints : Tendsto (fun r =>
      (reflectedRadialAxisSnap (mesh r) z,
        reflectedRadialAxisSnap (mesh r) w)) atTop (nhds (z, w)) :=
    hsnapZ.prodMk_nhds hsnapW
  have h := (continuous_wedgeContour f hf).continuousAt.tendsto.comp hendpoints
  simpa only [Prod.fst, Prod.snd] using h



private theorem reflectedRadialAxisSnap_wedgeContour_tendsto_zero
    (f : Complex -> Complex) (hf : Continuous f)
    (mesh : Nat -> Real) (hmeshPos : ∀ r, 0 < mesh r)
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (haxis : Tendsto (fun r =>
      axisMacroDirectContour f
        (reflectedRadialAxisSnap (mesh r) z).re
        (reflectedRadialAxisSnap (mesh r) z).im (mesh r)
        (reflectedRadialAxisSnapWidth (mesh r) z w)
        (reflectedRadialAxisSnapHeight (mesh r) z w))
      atTop (nhds 0)) :
    Tendsto (fun r =>
      Complex.wedgeIntegral (reflectedRadialAxisSnap (mesh r) z)
          (reflectedRadialAxisSnap (mesh r) w) f +
        Complex.wedgeIntegral (reflectedRadialAxisSnap (mesh r) w)
          (reflectedRadialAxisSnap (mesh r) z) f) atTop (nhds 0) := by
  apply haxis.congr'
  filter_upwards with r
  exact axisMacroDirectContour_reflectedRadialAxisSnap_eq_wedgeContour
    f hf z w (hmeshPos r) hre him



private theorem ordered_wedgeContour_eq_zero_of_axisMacroDirectContour_tendsto
    (f : Complex -> Complex) (hf : Continuous f)
    (mesh : Nat -> Real) (hmeshPos : ∀ r, 0 < mesh r)
    (hmeshZero : Tendsto mesh atTop (nhds 0))
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (haxis : Tendsto (fun r =>
      axisMacroDirectContour f
        (reflectedRadialAxisSnap (mesh r) z).re
        (reflectedRadialAxisSnap (mesh r) z).im (mesh r)
        (reflectedRadialAxisSnapWidth (mesh r) z w)
        (reflectedRadialAxisSnapHeight (mesh r) z w))
      atTop (nhds 0)) :
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0 := by
  exact tendsto_nhds_unique
    (reflectedRadialAxisSnap_wedgeContour_tendsto
      f hf mesh hmeshPos hmeshZero z w)
    (reflectedRadialAxisSnap_wedgeContour_tendsto_zero
      f hf mesh hmeshPos z w hre him haxis)



theorem fkIsingExpandingBoundarySquare_orderedRectangleContour_eq_zero
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn
      (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
        (sigma r)) f atTop Set.univ)
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0 := by
  let mesh : Nat -> Real := fun r => fkIsingExpandingSquareScale (sigma r)
  let snap : Nat -> Complex -> Complex := fun r q =>
    reflectedRadialAxisSnap (mesh r) q
  let width : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapWidth (mesh r) z w
  let height : Nat -> Nat := fun r =>
    reflectedRadialAxisSnapHeight (mesh r) z w
  have hmeshPos : ∀ r, 0 < mesh r := fun r =>
    fkIsingExpandingSquareScale_pos (sigma r)
  have hmeshZero : Tendsto mesh atTop (nhds 0) := by
    exact fkIsingExpandingSquareScale_tendsto_zero.comp hsigma
  have hf : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall fun r =>
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
        (sigma r)).continuousOn))
  have haxisTendsto : Tendsto (fun r =>
      axisMacroDirectContour f (snap r z).re (snap r z).im
        (mesh r) (width r) (height r)) atTop (nhds 0) := by
    simpa [mesh, snap, width, height] using
      fkIsingExpandingBoundarySquare_axisMacroDirectContour_tendsto_zero
        hsigma hlimit z w hre him
  exact ordered_wedgeContour_eq_zero_of_axisMacroDirectContour_tendsto
    f hf mesh hmeshPos hmeshZero z w hre him (by
      simpa [snap, width, height] using haxisTendsto)



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn
      (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
        (sigma r)) f atTop Set.univ) :
    Complex.IsConservativeOn f Set.univ := by
  apply isConservativeOn_univ_of_ordered_wedgeContour_eq_zero f
  intro z w hre him
  exact fkIsingExpandingBoundarySquare_orderedRectangleContour_eq_zero
    hsigma hlimit z w hre him



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_differentiable_subsequentialLimit
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn
      (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
        (sigma r)) f atTop Set.univ) :
    Differentiable Complex f := by
  have hf : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall fun r =>
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
        (sigma r)).continuousOn))
  apply differentiableOn_univ.mp
  exact (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    isOpen_univ).1
      ⟨fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit
        hsigma hlimit, hf.continuousOn⟩

end

end StatMech.Universality
