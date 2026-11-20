/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Code.Universality.IsingFermionicPhysicalCompactPlacement
import Code.Universality.IsingFermionicVariableFourthOrderBulk
import Code.Universality.IsingFermionicSpatialResidualComparison
import Code.Universality.IsingFermionicEndpointRadialShellCardinality










open Metric

noncomputable section

set_option maxHeartbeats 1800000 in

theorem isingFermionic_verticalOscillation_cauchy_fourth
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= C) :
    ‖iteratedDeriv 4 Phi c‖ <= 768 * C / d ^ 4 := by
  let shift : Complex -> Complex := fun t => Phi (c + t)
  have hmap : Set.MapsTo (fun t : Complex => c + t) (ball 0 d) (ball c d) := by
    intro t ht
    simpa [Metric.mem_ball, dist_eq_norm] using ht
  have hshift : DifferentiableOn Complex shift (ball 0 d) := by
    exact hPhi.comp ((differentiableOn_const c).add differentiableOn_id) hmap
  let g : Complex -> Complex := fun t => -Complex.I * (shift t - shift 0)
  have hg : DifferentiableOn Complex g (ball 0 d) := by
    exact (differentiableOn_const (-Complex.I)).mul
      (hshift.sub (differentiableOn_const (shift 0)))
  have hgre : Set.MapsTo g (ball 0 d) {z | z.re <= C} := by
    intro t ht
    have htOsc := hosc (c + t) (hmap ht)
    change (-Complex.I * (shift t - shift 0)).re <= C
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero,
      zero_mul, Complex.neg_im, Complex.I_im, neg_one_mul, zero_sub,
      Complex.sub_im, shift]
    simpa using (le_of_abs_le htOsc)
  have hgzero : g 0 = 0 := by simp [g]
  have hB : forall t, t ∈ sphere 0 (d / 2) ->
      ‖shift t - shift 0‖ <= 2 * C := by
    intro t ht
    have hnorm : ‖t‖ = d / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ht
    have htball : t ∈ ball 0 d := by
      simp only [_root_.Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
      linarith
    have hb := Complex.borelCaratheodory_zero
      (f := g) (R := d) (M := C) (z := t)
      hC hg hgre hd htball hgzero
    have hgnorm : ‖g t‖ = ‖shift t - shift 0‖ := by
      simp [g]
    rw [hgnorm, hnorm] at hb
    calc
      ‖shift t - shift 0‖ <= 2 * C * (d / 2) / (d - d / 2) := hb
      _ = 2 * C := by
        field_simp [hd.ne']
        ring
  have hgSmall : DiffContOnCl Complex g (ball 0 (d / 2)) := by
    constructor
    · exact hg.mono (Metric.ball_subset_ball (by linarith))
    · apply hg.continuousOn.mono
      rw [closure_ball 0 (by positivity)]
      exact Metric.closedBall_subset_ball (by linarith)
  have hBg : forall t, t ∈ sphere 0 (d / 2) -> ‖g t‖ <= 2 * C := by
    intro t ht
    have hgnorm : ‖g t‖ = ‖shift t - shift 0‖ := by simp [g]
    rw [hgnorm]
    exact hB t ht
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := g) 4 (by positivity : 0 < d / 2) hgSmall hBg
  have hgfun : g = fun t => Complex.I * shift 0 + (-Complex.I) * shift t := by
    funext t
    simp only [g]
    ring
  have hgderiv : iteratedDeriv 4 g 0 =
      -Complex.I * iteratedDeriv 4 shift 0 := by
    rw [hgfun, iteratedDeriv_const_add (by norm_num)]
    exact iteratedDeriv_const_mul_field (-Complex.I) shift
  have hnormderiv : ‖iteratedDeriv 4 g 0‖ =
      ‖iteratedDeriv 4 shift 0‖ := by
    rw [hgderiv]
    simp
  rw [hnormderiv, iteratedDeriv_comp_const_add 4 Phi c] at hc
  dsimp [shift] at hc
  have hscale : (Nat.factorial 4 : Real) * (2 * C) / (d / 2) ^ 4 =
      768 * C / d ^ 4 := by
    norm_num
    field_simp [hd.ne']
    ring
  rw [hscale] at hc
  simpa using hc


theorem isingFermionic_strip_cauchy_fourth
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    ‖iteratedDeriv 4 Phi c‖ <= 768 / d ^ 4 := by
  have hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= 1 := by
    intro z hz
    have hzRange := hrange z hz
    have hcRange := hrange c (Metric.mem_ball_self hd)
    rw [abs_le]
    constructor <;> linarith
  simpa using isingFermionic_verticalOscillation_cauchy_fourth
    Phi c d 1 hd one_pos hPhi hosc



theorem isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    (Phi : Complex -> Complex) (c : Complex)
    (hPhi : ContDiffAt Complex 4 Phi c) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      ‖iteratedDeriv 4 Phi c‖ := by
  have hreal : ContDiffAt Real 4 Phi c := hPhi.restrict_scalars Real
  have him := Complex.imCLM.norm_iteratedFDeriv_comp_left
    (n := 4) (N := 4) hreal (by norm_num)
  rw [Complex.imCLM_norm, one_mul] at him
  change ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <= _ at him
  rw [← hPhi.restrictScalars_iteratedFDeriv (𝕜 := Real)] at him
  simp only [Function.comp_apply] at him
  rw [ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at him
  exact him


theorem isingFermionic_verticalOscillation_im_fourth_tensor
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= C) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      768 * C / d ^ 4 := by
  have hPhiAt : ContDiffAt Complex 4 Phi c :=
    (hPhi.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))
  exact (isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    Phi c hPhiAt).trans
    (isingFermionic_verticalOscillation_cauchy_fourth
      Phi c d C hd hC hPhi hosc)


theorem isingFermionic_strip_im_fourth_tensor
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      768 / d ^ 4 := by
  have hPhiAt : ContDiffAt Complex 4 Phi c :=
    (hPhi.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))
  exact (isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    Phi c hPhiAt).trans
    (isingFermionic_strip_cauchy_fourth Phi c d hd hPhi hrange)

theorem isingFermionic_ball_half_subset_ball_of_mem
    {c w : Complex} {d : Real} (hw : w ∈ ball c (d / 2)) :
    ball w (d / 2) ⊆ ball c d := by
  intro z hz
  rw [Metric.mem_ball] at hw hz ⊢
  calc
    dist z c <= dist z w + dist w c := dist_triangle _ _ _
    _ < d / 2 + d / 2 := add_lt_add hz hw
    _ = d := by ring



theorem isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d -> forall w, w ∈ ball c d ->
      |(Phi z).im - (Phi w).im| <= C) :
    forall w, w ∈ ball c (d / 2) ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <=
        12288 * C / d ^ 4 := by
  intro w hw
  have hsub := isingFermionic_ball_half_subset_ball_of_mem hw
  have hlocal := isingFermionic_verticalOscillation_im_fourth_tensor
    Phi w (d / 2) C (by positivity) hC (hPhi.mono hsub)
      (fun z hz => hosc z (hsub hz) w (hsub (Metric.mem_ball_self (by positivity))))
  convert hlocal using 1
  field_simp [hd.ne']
  ring


theorem isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    forall w, w ∈ ball c (d / 2) ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <=
        12288 / d ^ 4 := by
  intro w hw
  have hsub := isingFermionic_ball_half_subset_ball_of_mem hw
  have hlocal := isingFermionic_strip_im_fourth_tensor
    Phi w (d / 2) (by positivity)
    (hPhi.mono hsub) (fun z hz => hrange z (hsub hz))
  convert hlocal using 1
  field_simp [hd.ne']
  ring

end

namespace StatMech.Universality

open Metric

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def unitStripHalfBallFourthTensorBound (d : Real) : NNReal :=
  ⟨12288 / d ^ 4, by positivity⟩

noncomputable def verticalOscillationHalfBallFourthTensorBound
    (C : NNReal) (d : Real) : NNReal :=
  ⟨12288 * (C : Real) / d ^ 4, by positivity⟩



noncomputable def unitStripCenteredBallFourthOrderResidualBound
    (h d : Real) : Real :=
  ((4 * (unitStripHalfBallFourthTensorBound d : Real)) +
      4 * (unitStripHalfBallFourthTensorBound d : Real)) * |h| ^ 4 / 12

noncomputable def verticalOscillationCenteredBallFourthOrderResidualBound
    (C : NNReal) (h d : Real) : Real :=
  ((4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) +
      4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) *
    |h| ^ 4 / 12

theorem unitStripCenteredBallFourthOrderResidualBound_eq
    (h d : Real) :
    unitStripCenteredBallFourthOrderResidualBound h d =
      8192 * |h| ^ 4 / d ^ 4 := by
  unfold unitStripCenteredBallFourthOrderResidualBound
  change ((4 * (12288 / d ^ 4) + 4 * (12288 / d ^ 4)) *
    |h| ^ 4 / 12) = 8192 * |h| ^ 4 / d ^ 4
  ring



theorem unitStripCenteredBallFourthOrderResidualBound_distanceScale
    (h rho : Real) (hh : h ≠ 0) (hrho : rho ≠ 0) :
    unitStripCenteredBallFourthOrderResidualBound h (|h| * rho) =
      8192 / rho ^ 4 := by
  rw [unitStripCenteredBallFourthOrderResidualBound_eq]
  field_simp [abs_ne_zero.mpr hh, hrho]

theorem verticalOscillationCenteredBallFourthOrderResidualBound_eq
    (C : NNReal) (h d : Real) :
    verticalOscillationCenteredBallFourthOrderResidualBound C h d =
      8192 * (C : Real) * |h| ^ 4 / d ^ 4 := by
  unfold verticalOscillationCenteredBallFourthOrderResidualBound
  change ((4 * (12288 * (C : Real) / d ^ 4) +
    4 * (12288 * (C : Real) / d ^ 4)) * |h| ^ 4 / 12) = _
  ring

theorem verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
    (C : NNReal) (h rho : Real) (hh : h ≠ 0) (hrho : rho ≠ 0) :
    verticalOscillationCenteredBallFourthOrderResidualBound
        C h (|h| * rho) =
      8192 * (C : Real) / rho ^ 4 := by
  rw [verticalOscillationCenteredBallFourthOrderResidualBound_eq]
  field_simp [abs_ne_zero.mpr hh, hrho]



theorem LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall
    {Phi : Complex -> Complex} {c z : Complex} {h d : Real}
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall w, w ∈ ball c d ->
      0 <= (Phi w).im /\ (Phi w).im <= 1)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2)))
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2))) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (unitStripHalfBallFourthTensorBound d : Real))
      (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    (ball c (d / 2)) Metric.isOpen_ball
    ((hPhi.mono (Metric.ball_subset_ball (by linarith))).analyticOnNhd
      Metric.isOpen_ball)
    (unitStripHalfBallFourthTensorBound d)
  · intro w hw
    exact isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall
      Phi c d hd hPhi hrange w hw
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo




theorem LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall
    {Phi : Complex -> Complex} {c z : Complex} {h d : Real}
    (C : NNReal) (hC : 0 < (C : Real)) (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall u, u ∈ ball c d -> forall v, v ∈ ball c d ->
      |(Phi u).im - (Phi v).im| <= (C : Real))
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2)))
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2))) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real))
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    (ball c (d / 2)) Metric.isOpen_ball
    ((hPhi.mono (Metric.ball_subset_ball (by linarith))).analyticOnNhd
      Metric.isOpen_ball)
    (verticalOscillationHalfBallFourthTensorBound C d)
  · intro w hw
    exact isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall
      Phi c d (C : Real) hd hC hPhi hosc w hw
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo




theorem LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    {Phi : Complex -> Complex} {z : Complex} {h d : Real}
    (hd : 0 < d)
    (hmesh : 2 * |h| < d / 2)
    (hPhi : DifferentiableOn Complex Phi (ball z d))
    (hrange : forall w, w ∈ ball z d ->
      0 <= (Phi w).im /\ (Phi w).im <= 1) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (unitStripHalfBallFourthTensorBound d : Real))
      (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
  have hcollar : Metric.cthickening (2 * |h|) ({z} : Set Complex) ⊆
      ball z (d / 2) := by
    rw [Metric.cthickening_singleton z (by positivity)]
    exact Metric.closedBall_subset_ball hmesh
  apply LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall
    hd hPhi hrange
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) false
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) false



theorem LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
    {Phi : Complex -> Complex} {z : Complex} {h d : Real}
    (C : NNReal) (hC : 0 < (C : Real)) (hd : 0 < d)
    (hmesh : 2 * |h| < d / 2)
    (hPhi : DifferentiableOn Complex Phi (ball z d))
    (hosc : forall u, u ∈ ball z d -> forall v, v ∈ ball z d ->
      |(Phi u).im - (Phi v).im| <= (C : Real)) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real))
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
  have hcollar : Metric.cthickening (2 * |h|) ({z} : Set Complex) ⊆
      ball z (d / 2) := by
    rw [Metric.cthickening_singleton z (by positivity)]
    exact Metric.closedBall_subset_ball hmesh
  apply LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall
    C hC hd hPhi hosc
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) false
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) false



theorem fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (d : Real)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledVertexEmbedding n mesh x) d))
    (hrange : forall w,
      w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
        0 <= (Phi w).im /\ (Phi w).im <= 1) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        unitStripCenteredBallFourthOrderResidualBound mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions n x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) x heast hnorth hwest hsouth]
  have H := LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    hd hmesh hPhi hrange
  simpa [unitStripCenteredBallFourthOrderResidualBound] using H.stencil



theorem fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (d : Real)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledFaceEmbedding n mesh c) d))
    (hrange : forall w,
      w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
        0 <= (Phi w).im /\ (Phi w).im <= 1) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        unitStripCenteredBallFourthOrderResidualBound mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates n c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) c heast hnorth hwest hsouth]
  have H := LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    hd hmesh hPhi hrange
  simpa [unitStripCenteredBallFourthOrderResidualBound] using H.stencil



theorem fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (d : Real)
    (C : NNReal) (hC : 0 < (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledVertexEmbedding n mesh x) d))
    (hosc : forall u,
      u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
      forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
        |(Phi u).im - (Phi v).im| <= (C : Real)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions n x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) x heast hnorth hwest hsouth]
  have H :=
    LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
      C hC hd hmesh hPhi hosc
  simpa [verticalOscillationCenteredBallFourthOrderResidualBound] using H.stencil


theorem fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (d : Real)
    (C : NNReal) (hC : 0 < (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledFaceEmbedding n mesh c) d))
    (hosc : forall u,
      u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
      forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
        |(Phi u).im - (Phi v).im| <= (C : Real)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates n c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) c heast hnorth hwest hsouth]
  have H :=
    LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
      C hC hd hmesh hPhi hosc
  simpa [verticalOscillationCenteredBallFourthOrderResidualBound] using H.stencil





theorem fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        8192 / (((r + 1 : Nat) : Real) ^ 4) := by
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hrange⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall
        n mesh Phi x (|mesh| * rho) hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hrange
    rw [unitStripCenteredBallFourthOrderResidualBound_distanceScale
      mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledVertexEmbedding n mesh) Phi hsampleRange x
    interval_cases r <;> apply hfour.trans <;> norm_num


theorem fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        8192 / (((r + 1 : Nat) : Real) ^ 4) := by
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hrange⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall
        n mesh Phi c (|mesh| * rho) hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hrange
    rw [unitStripCenteredBallFourthOrderResidualBound_distanceScale
      mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareFace_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledFaceEmbedding n mesh) Phi hsampleRange c
    interval_cases r <;> apply hfour.trans <;> norm_num



theorem fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
          forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
  have hC : 0 < (C : Real) := one_pos.trans_le hCOne
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hosc⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall
        n mesh Phi x (|mesh| * rho) C hC hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hosc
    rw [verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
      C mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledVertexEmbedding n mesh) Phi hsampleRange x
    interval_cases r <;> apply hfour.trans <;> norm_num <;> nlinarith


theorem fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
          forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
  have hC : 0 < (C : Real) := one_pos.trans_le hCOne
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hosc⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall
        n mesh Phi c (|mesh| * rho) C hC hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hosc
    rw [verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
      C mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareFace_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledFaceEmbedding n mesh) Phi hsampleRange c
    interval_cases r <;> apply hfour.trans <;> norm_num <;> nlinarith



theorem vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) =
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| := by
  have hsampled : vertexSampledImaginaryTarget n
      (fullSquareScaledVertexEmbedding n mesh) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold vertexSpatialTargetResidual vertexDirichletBoundary
    vertexGhostConductance
  simp only [isingFiniteGhostBoundaryWith, hfixed, ↓reduceIte]
  rw [isingFiniteGhostLaplacian_some]
  simp [isingFermionicGhostRate, hghost]


theorem faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) =
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| := by
  have hsampled : faceSampledImaginaryTarget n
      (fullSquareScaledFaceEmbedding n mesh) Phi =
      isingFiniteGhostExtension 0
        (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold faceSpatialTargetResidual faceDirichletBoundary faceGhostConductance
  simp only [isingFiniteGhostBoundaryWith, hfixed, ↓reduceIte]
  rw [isingFiniteGhostLaplacian_some]
  simp [isingFermionicGhostRate, hghost]




theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
      8192 / (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
  rw [vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi x hfixed hghost]
  exact fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic
    n (vertexEndpointRadialShell n (some x)) mesh Phi x hfixed hghost
      hmesh_ne hsampleRange hball


theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
      8192 / (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
  rw [faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi c hfixed hghost]
  exact fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic
    n (faceEndpointRadialShell n (some c)) mesh Phi c hfixed hghost
      hmesh_ne hsampleRange hball



theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
          forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
      8192 * (C : Real) /
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
  rw [vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi x hfixed hghost]
  exact
    fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
      n (vertexEndpointRadialShell n (some x)) mesh Phi x C hCOne
        hfixed hghost hmesh_ne hsampleRange hball


theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
          forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
      8192 * (C : Real) /
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
  rw [faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi c hfixed hghost]
  exact
    fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
      n (faceEndpointRadialShell n (some c)) mesh Phi c C hCOne
        hfixed hghost hmesh_ne hsampleRange hball




theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hghostResidual : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x ≠ 0 ->
      vertexSpatialTargetResidual n
          (vertexSampledImaginaryTarget n
            (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
        8192 /
          (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4)) :
    forall z,
      vertexSpatialTargetResidual n
          (vertexSampledImaginaryTarget n
            (fullSquareScaledVertexEmbedding n mesh) Phi) z <=
        8192 / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
  intro z
  cases z with
  | none =>
      simp [vertexSpatialTargetResidual, vertexDirichletBoundary,
        isingFiniteGhostBoundaryWith]
  | some x =>
      by_cases hfixed : fkIsingSquareFullVertexFixedBoundary n x
      · have hzero : vertexSpatialTargetResidual n
            (vertexSampledImaginaryTarget n
              (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) = 0 := by
          simp [vertexSpatialTargetResidual, vertexDirichletBoundary,
            isingFiniteGhostBoundaryWith, hfixed]
        rw [hzero]
        positivity
      · by_cases hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0
        · exact
            vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
              n mesh Phi x hfixed hghost hmesh_ne hsampleRange
                (hball x hfixed hghost)
        · exact hghostResidual x hfixed hghost



theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall c,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh c)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh c)).im <= 1)
    (hball : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hghostResidual : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c ≠ 0 ->
      faceSpatialTargetResidual n
          (faceSampledImaginaryTarget n
            (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
        8192 /
          (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4)) :
    forall z,
      faceSpatialTargetResidual n
          (faceSampledImaginaryTarget n
            (fullSquareScaledFaceEmbedding n mesh) Phi) z <=
        8192 / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
  intro z
  cases z with
  | none =>
      simp [faceSpatialTargetResidual, faceDirichletBoundary,
        isingFiniteGhostBoundaryWith]
  | some c =>
      by_cases hfixed : fkIsingSquareFullFaceFixedBoundary n c
      · have hzero : faceSpatialTargetResidual n
            (faceSampledImaginaryTarget n
              (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) = 0 := by
          simp [faceSpatialTargetResidual, faceDirichletBoundary,
            isingFiniteGhostBoundaryWith, hfixed]
        rw [hzero]
        positivity
      · by_cases hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0
        · exact
            faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
              n mesh Phi c hfixed hghost hmesh_ne hsampleRange
                (hball c hfixed hghost)
        · exact hghostResidual c hfixed hghost



noncomputable def
    PhysicalEndpointVariableFourthOrderBulkData.ofUnitStripCenteredBalls
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (d : Nat -> Real) (hd : forall k, 0 < d k)
    (hmesh : forall k, 2 * |mesh k| < d k / 2)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      DifferentiableOn Complex Phi (ball z (d k)) /\
        (forall w, w ∈ ball z (d k) ->
          0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      DifferentiableOn Complex Phi (ball z (d k)) /\
        (forall w, w ∈ ball z (d k) ->
          0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius where
  boundOne k := 4 * (unitStripHalfBallFourthTensorBound (d k) : Real)
  boundTwo k := 4 * (unitStripHalfBallFourthTensorBound (d k) : Real)
  boundSum_nonneg k := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hPhi, hrange⟩ := hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
      (hd k) (hmesh k) hPhi hrange
  face k c hfixed hghost hendpoint := by
    obtain ⟨hPhi, hrange⟩ := hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
      (hd k) (hmesh k) hPhi hrange

end FKIsingSquareBoundaryLayerCoordinateOneForm

end StatMech.Universality
