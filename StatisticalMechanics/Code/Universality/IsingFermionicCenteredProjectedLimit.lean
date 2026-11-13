/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredDiagonalScalingLimit
import Code.Universality.IsingFermionicProjectedFullMedialInterpolation










open Filter Metric Set Topology

namespace StatMech.Universality

noncomputable section



theorem tendsto_apply_of_tendstoLocallyUniformlyOn_of_tendsto
    {F : Nat -> Complex -> Complex} {f : Complex -> Complex}
    {x : Nat -> Complex} {z : Complex}
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (hf : ContinuousAt f z) (hx : Tendsto x atTop (nhds z)) :
    Tendsto (fun n => F n (x n)) atTop (nhds (f z)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let K : Set Complex := Metric.closedBall z 1
  have hK : IsCompact K := isCompact_closedBall z 1
  have huniform : TendstoUniformlyOn F f atTop K := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    exact hlimit.mono (subset_univ K)
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  have hnear : ∀ᶠ n in atTop, x n ∈ K := by
    have hball : Metric.ball z 1 ∈ nhds z := Metric.ball_mem_nhds z zero_lt_one
    filter_upwards [hx.eventually hball] with n hn
    exact Metric.ball_subset_closedBall hn
  have hfield : Tendsto (fun n => f (x n)) atTop (nhds (f z)) :=
    hf.tendsto.comp hx
  have hfieldNear : ∀ᶠ n in atTop,
      dist (f (x n)) (f z) < epsilon / 2 :=
    (Metric.tendsto_nhds.1 hfield) (epsilon / 2) (by positivity)
  have hmeshNear : ∀ᶠ n in atTop, ∀ q ∈ K,
      dist (F n q) (f q) < epsilon / 2 :=
    by simpa [dist_comm] using huniform (epsilon / 2) (by positivity)
  filter_upwards [hnear, hfieldNear, hmeshNear] with n hxn hfn hFn
  calc
    dist (F n (x n)) (f z) <=
        dist (F n (x n)) (f (x n)) + dist (f (x n)) (f z) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add (hFn (x n) hxn) hfn
    _ = epsilon := by ring



theorem tendsto_of_dist_tendsto_zero_of_tendsto
    {X Y : Type*} [PseudoMetricSpace Y] {l : Filter X}
    {f g : X -> Y} {y : Y}
    (hfg : Tendsto (fun x => dist (f x) (g x)) l (nhds 0))
    (hg : Tendsto g l (nhds y)) :
    Tendsto f l (nhds y) := by
  rw [Metric.tendsto_nhds] at hg ⊢
  intro epsilon hepsilon
  have hclose : ∀ᶠ x in l, dist (f x) (g x) < epsilon / 2 :=
    hfg.eventually (Iio_mem_nhds (by positivity))
  have hnear : ∀ᶠ x in l, dist (g x) y < epsilon / 2 :=
    hg (epsilon / 2) (by positivity)
  filter_upwards [hclose, hnear] with x hx hxy
  calc
    dist (f x) y <= dist (f x) (g x) + dist (g x) y := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hx hxy
    _ = epsilon := by ring



theorem
    fkIsingExpandingBoundarySquareCenteredFullObservable_tendsto_of_locallyUniform
    (target : Complex -> Complex)
    (hlimit : TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      Set.univ)
    (htarget : Continuous target)
    (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
    (z : Complex)
    (hposition : Tendsto
      (fun k => (starRingEnd Complex)
        (isingCenteredRadialGridPosition
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
          (i k).1 (j k).1)) atTop (nhds z)) :
    Tendsto
      (fun k =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) (i k) (j k) /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      atTop (nhds (target z)) := by
  have hsample := tendsto_apply_of_tendstoLocallyUniformlyOn_of_tendsto
    hlimit (htarget.continuousAt) hposition
  apply hsample.congr'
  filter_upwards [] with k
  exact
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
      (fkIsingExpandingSquareScale_pos k).ne' (i k) (j k)




theorem
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform
    (target : Complex -> Complex)
    (hlimit : TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      Set.univ)
    (htarget : Continuous target)
    (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
    (side : FKIsingMedialSide) (z : Complex)
    (hposition : Tendsto
      (fun k => (starRingEnd Complex)
        (isingCenteredRadialGridPosition
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
          (i k).1 (j k).1)) atTop (nhds z))
    (hinterior : ∀ k,
      (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉
          fkIsingSquarePerimeterPrimalEdgeFinset
            (fkIsingExpandingSquareSide k)) :
    Tendsto
      (fun k => dist
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
          (fkIsingExpandingSquareMesh k)
          (.dart (fkIsingSquareCenteredRadialPatchEdge
            (fkIsingExpandingSquareSide k) (i k) (j k), side)))
        (isingProj
          (fkIsingSquareWiredDirectedTangent
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)))
          (target z)))
      atTop (nhds 0) := by
  let full : Nat -> Complex := fun k =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) (i k) (j k) /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  let tangent : Nat -> Complex := fun k =>
    fkIsingSquareWiredDirectedTangent
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (.dart (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k), side))
  have hfull : Tendsto full atTop (nhds (target z)) := by
    exact
      fkIsingExpandingBoundarySquareCenteredFullObservable_tendsto_of_locallyUniform
        target hlimit htarget i j z hposition
  have hdist : Tendsto (fun k => dist (full k) (target z)) atTop (nhds 0) := by
    have hconstant : Tendsto (fun _ : Nat => target z) atTop (nhds (target z)) :=
      tendsto_const_nhds
    simpa using hfull.dist hconstant
  apply squeeze_zero (fun _ => dist_nonneg) _ hdist
  intro k
  have htangent : Complex.normSq (tangent k) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [tangent, fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  have hproj_div (u w : Complex) (r : Real) :
      isingProj u (w / (r : Complex)) = isingProj u w / (r : Complex) := by
    unfold isingProj
    simp
    ring
  have hproject :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
        (fkIsingExpandingSquareMesh k)
        (.dart (fkIsingSquareCenteredRadialPatchEdge
          (fkIsingExpandingSquareSide k) (i k) (j k), side)) =
      isingProj (tangent k) (full k) := by
    unfold FKIsingDobrushinDomain.normalizedFermionicObservable full tangent
    have hraw :
      isingProj
          (fkIsingSquareWiredDirectedTangent
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)))
          (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) (i k) (j k)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k)).fermionicObservable
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)) := by
      exact fkIsingSquareBoundaryFullMedialObservable_projection
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (fkIsingSquareCenteredRadialPatchEdge
          (fkIsingExpandingSquareSide k) (i k) (j k)) (hinterior k) side
    rw [← hraw]
    symm
    exact hproj_div _ _ _
  rw [hproject]
  exact isingProj_dist_le (tangent k) (full k) (target z) htangent



theorem
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_tangent
    (target : Complex -> Complex)
    (hlimit : TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      Set.univ)
    (htarget : Continuous target)
    (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
    (side : FKIsingMedialSide) (z u : Complex)
    (hposition : Tendsto
      (fun k => (starRingEnd Complex)
        (isingCenteredRadialGridPosition
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
          (i k).1 (j k).1)) atTop (nhds z))
    (hinterior : ∀ k,
      (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉
          fkIsingSquarePerimeterPrimalEdgeFinset
            (fkIsingExpandingSquareSide k))
    (htangent : Tendsto
      (fun k => fkIsingSquareWiredDirectedTangent
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (.dart (fkIsingSquareCenteredRadialPatchEdge
          (fkIsingExpandingSquareSide k) (i k) (j k), side)))
      atTop (nhds u)) :
    Tendsto
      (fun k =>
        (fkIsingSquareBoundaryRestrictedDobrushinDomain
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
            (fkIsingExpandingSquareMesh k)
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)))
      atTop (nhds (isingProj u (target z))) := by
  let tangent : Nat -> Complex := fun k =>
    fkIsingSquareWiredDirectedTangent
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (.dart (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k), side))
  have hclose :=
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform
      target hlimit htarget i j side z hposition hinterior
  have hproject : Tendsto (fun k => isingProj (tangent k) (target z))
      atTop (nhds (isingProj u (target z))) := by
    have hcontinuous : Continuous (fun v : Complex => isingProj v (target z)) := by
      unfold isingProj
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp (by simpa [tangent] using htangent)
  exact tendsto_of_dist_tendsto_zero_of_tendsto hclose hproject




theorem
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths
    {bulkRate layerRate : Nat -> Real}
    (target Phi : Complex -> Complex)
    (L : FKIsingCanonicalDensePrimitiveLocalInputs
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi
        fkIsingExpandingSquareScale bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hbase : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0)))
    (i j : forall k, Fin (2 * fkIsingExpandingSquareSide k))
    (side : FKIsingMedialSide) (z : Complex)
    (hposition : Tendsto
      (fun k => (starRingEnd Complex)
        (isingCenteredRadialGridPosition
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
          (i k).1 (j k).1)) atTop (nhds z))
    (hinterior : forall k,
      (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉
          fkIsingSquarePerimeterPrimalEdgeFinset
            (fkIsingExpandingSquareSide k)) :
    Tendsto
      (fun k => dist
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
          (fkIsingExpandingSquareMesh k)
          (.dart (fkIsingSquareCenteredRadialPatchEdge
            (fkIsingExpandingSquareSide k) (i k) (j k), side)))
        (isingProj
          (fkIsingSquareWiredDirectedTangent
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)))
          (target z)))
      atTop (nhds 0) := by
  have hlimitU :=
    FKIsingCaratheodoryApproximation.scalingLimit_of_centeredFullCarrierTV_canonicalRationalPaths
      target Phi L Hrobin lipschitzConstant hPhiLip htarget htarget_ne
      hPhi hPhideriv E hbase
  have hlimit : TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      Set.univ := by
    simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hlimitU
  have htargetContinuous : Continuous target := by
    exact (differentiableOn_univ.mp (by
      simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using
        htarget)).continuous
  exact
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform
      target hlimit htargetContinuous i j side z hposition hinterior



theorem
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths_of_tangent
    {bulkRate layerRate : Nat -> Real}
    (target Phi : Complex -> Complex)
    (L : FKIsingCanonicalDensePrimitiveLocalInputs
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi
        fkIsingExpandingSquareScale bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hbase : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0)))
    (i j : forall k, Fin (2 * fkIsingExpandingSquareSide k))
    (side : FKIsingMedialSide) (z u : Complex)
    (hposition : Tendsto
      (fun k => (starRingEnd Complex)
        (isingCenteredRadialGridPosition
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
          (i k).1 (j k).1)) atTop (nhds z))
    (hinterior : forall k,
      (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉
          fkIsingSquarePerimeterPrimalEdgeFinset
            (fkIsingExpandingSquareSide k))
    (htangent : Tendsto
      (fun k => fkIsingSquareWiredDirectedTangent
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (.dart (fkIsingSquareCenteredRadialPatchEdge
          (fkIsingExpandingSquareSide k) (i k) (j k), side)))
      atTop (nhds u)) :
    Tendsto
      (fun k =>
        (fkIsingSquareBoundaryRestrictedDobrushinDomain
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
            (fkIsingExpandingSquareMesh k)
            (.dart (fkIsingSquareCenteredRadialPatchEdge
              (fkIsingExpandingSquareSide k) (i k) (j k), side)))
      atTop (nhds (isingProj u (target z))) := by
  have hclose :=
    fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths
      target Phi L Hrobin lipschitzConstant hPhiLip htarget htarget_ne
      hPhi hPhideriv E hbase i j side z hposition hinterior
  let tangent : Nat -> Complex := fun k =>
    fkIsingSquareWiredDirectedTangent
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (.dart (fkIsingSquareCenteredRadialPatchEdge
        (fkIsingExpandingSquareSide k) (i k) (j k), side))
  have hproject : Tendsto (fun k => isingProj (tangent k) (target z))
      atTop (nhds (isingProj u (target z))) := by
    have hcontinuous : Continuous (fun v : Complex => isingProj v (target z)) := by
      unfold isingProj
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp (by simpa [tangent] using htangent)
  exact tendsto_of_dist_tendsto_zero_of_tendsto hclose hproject

end

end StatMech.Universality
