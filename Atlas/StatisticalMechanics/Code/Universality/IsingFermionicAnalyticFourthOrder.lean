/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRobinCompatibility
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Group.Bounded








namespace StatMech.Universality

open InnerProductSpace

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

private noncomputable def complexLineCLM (d : Complex) :
    Real →L[Real] Complex :=
  Complex.ofRealCLM.smulRight d



theorem contDiffOn_complexLine_of_contDiffOn
    (n : Nat) (f : Complex -> Real) (U : Set Complex)
    (z d : Complex) (s : Set Real)
    (hf : ContDiffOn Real n f U)
    (hline : Set.MapsTo
      (fun t : Real => z + (t : Complex) * d) s U) :
    ContDiffOn Real n
      (fun t : Real => f (z + (t : Complex) * d)) s := by
  let g : Real →L[Real] Complex := Complex.ofRealCLM.smulRight d
  have hg : ContDiff Real n (fun t : Real => z + g t) := by
    fun_prop
  have hmaps : Set.MapsTo (fun t : Real => z + g t) s U := by
    simpa [g] using hline
  simpa [Function.comp_def, g] using
    hf.comp hg.contDiffOn hmaps



theorem contDiffOn_im_of_analyticOnNhd
    (n : Nat) (Phi : Complex -> Complex) (U : Set Complex)
    (hPhi : AnalyticOnNhd Complex Phi U) :
    ContDiffOn Real n (fun z => (Phi z).im) U := by
  have hreal : ContDiffOn Real n Phi U :=
    hPhi.restrictScalars.contDiffOn_of_completeSpace
  simpa [Function.comp_def] using
    Complex.imCLM.contDiff.contDiffOn.comp hreal
      (Set.mapsTo_univ Phi U)



theorem exists_iteratedFDeriv_norm_bound_on_compact
    (Phi : Complex -> Complex) (U K : Set Complex)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U) :
    exists M : NNReal, forall w, w ∈ K ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M := by
  have hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U :=
    contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  have hcont : ContinuousOn
      (iteratedFDeriv Real 4 (fun w => (Phi w).im)) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hsmooth hU (by norm_num)).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  let M : NNReal := ⟨max C 0, le_max_right C 0⟩
  refine ⟨M, ?_⟩
  intro w hw
  apply (hC w hw).trans
  change C <= max C 0
  exact le_max_left C 0



theorem complexLine_mapsTo_uIcc_of_convex
    (U : Set Complex) (hU : Convex Real U)
    (z d : Complex) (h : Real) (hz : z ∈ U)
    (hend : z + (h : Complex) * d ∈ U) :
    Set.MapsTo (fun t : Real => z + (t : Complex) * d)
      (Set.uIcc 0 h) U := by
  let f : Real →ᵃ[Real] Complex :=
    { toFun := fun t => z + (t : Complex) * d
      linear := (Complex.ofRealCLM.smulRight d).toLinearMap
      map_vadd' := by
        intro p v
        simp
        ring }
  intro t ht
  have hmem : f t ∈ f '' segment Real 0 h := by
    refine ⟨t, ?_, rfl⟩
    simpa [segment_eq_uIcc] using ht
  rw [image_segment Real f 0 h] at hmem
  have hmem' : z + (t : Complex) * d ∈
      segment Real z (z + (h : Complex) * d) := by
    simpa [f] using hmem
  exact hU.segment_subset hz hend hmem'



theorem iteratedDeriv_complexLine_eq
    (n : Nat) (f : Complex -> Real) (z d : Complex) (t : Real)
    (hf : ContDiff Real n f) :
    iteratedDeriv n (fun s : Real => f (z + (s : Complex) * d)) t =
      iteratedFDeriv Real n f (z + (t : Complex) * d) (fun _ => d) := by
  let g : Real →L[Real] Complex := complexLineCLM d
  have hshift : ContDiff Real n (fun w : Complex => f (z + w)) := by
    fun_prop
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv Real n
      (Function.comp (fun w : Complex => f (z + w)) g) t)
      (fun _ => 1) = _
  rw [g.iteratedFDeriv_comp_right hshift t le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  have hgt : g t = (t : Complex) * d := by
    simp [g, complexLineCLM]
  have hg1 : g 1 = d := by
    simp [g, complexLineCLM]
  rw [hgt, hg1]



theorem iteratedDeriv_complexLine_eq_of_contDiffOn
    (n : Nat) (f : Complex -> Real) (U : Set Complex)
    (z d : Complex) (t : Real) (hU : IsOpen U)
    (hf : ContDiffOn Real n f U)
    (ht : z + (t : Complex) * d ∈ U) :
    iteratedDeriv n (fun s : Real => f (z + (s : Complex) * d)) t =
      iteratedFDeriv Real n f (z + (t : Complex) * d)
        (fun _ => d) := by
  let g : Real →L[Real] Complex := complexLineCLM d
  let a : Complex -> Complex := fun w => z + w
  let S : Set Complex := a ⁻¹' U
  let T : Set Real := g ⁻¹' S
  have haCont : Continuous a := by
    dsimp [a]
    fun_prop
  have haDiff : ContDiff Real n a := by
    dsimp [a]
    fun_prop
  have hSopen : IsOpen S := hU.preimage haCont
  have hmapsA : Set.MapsTo a S U := Set.mapsTo_preimage a U
  have hshift : ContDiffOn Real n (fun w : Complex => f (z + w)) S := by
    simpa [Function.comp_def, a] using
      hf.comp haDiff.contDiffOn hmapsA
  have hTopen : IsOpen T := hSopen.preimage g.continuous
  have hgt : g t ∈ S := by
    change z + g t ∈ U
    simpa [g, complexLineCLM] using ht
  have htT : t ∈ T := hgt
  have hcomp := g.iteratedFDerivWithin_comp_right hshift
    hSopen.uniqueDiffOn hTopen.uniqueDiffOn hgt (i := n) le_rfl
  have hshiftAt : ContDiffAt Real n
      (fun w : Complex => f (z + w)) (g t) :=
    hshift.contDiffAt (hSopen.mem_nhds hgt)
  have hcompOn : ContDiffOn Real n
      ((fun w : Complex => f (z + w)) ∘ g) T :=
    hshift.comp_continuousLinearMap g
  have hcompAt : ContDiffAt Real n
      ((fun w : Complex => f (z + w)) ∘ g) t :=
    hcompOn.contDiffAt (hTopen.mem_nhds htT)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv Real n
      ((fun w : Complex => f (z + w)) ∘ g) t) (fun _ => 1) = _
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv
      hTopen.uniqueDiffOn hcompAt htT,
    hcomp,
    iteratedFDerivWithin_eq_iteratedFDeriv
      hSopen.uniqueDiffOn hshiftAt hgt]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  have hgt' : g t = (t : Complex) * d := by
    simp [g, complexLineCLM]
  have hg1 : g 1 = d := by
    simp [g, complexLineCLM]
  rw [hgt', hg1]



theorem abs_iteratedDeriv_complexLine_four_le_tensorNorm
    (f : Complex -> Real) (z d : Complex) (t M : Real)
    (hf : ContDiff Real 4 f)
    (hbound : forall w, ‖iteratedFDeriv Real 4 f w‖ <= M) :
    |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * d)) t| <=
      M * ‖d‖ ^ 4 := by
  rw [iteratedDeriv_complexLine_eq 4 f z d t hf, <- Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv Real 4 f (z + (t : Complex) * d) (fun _ => d)‖ <=
        ‖iteratedFDeriv Real 4 f (z + (t : Complex) * d)‖ *
          ∏ _ : Fin 4, ‖d‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ <= M * ∏ _ : Fin 4, ‖d‖ := by
      gcongr
      exact hbound _
    _ = M * ‖d‖ ^ 4 := by simp



theorem abs_iteratedDeriv_complexLine_four_le_tensorNormAt
    (f : Complex -> Real) (U : Set Complex) (z d : Complex) (t M : Real)
    (hU : IsOpen U) (hf : ContDiffOn Real 4 f U)
    (ht : z + (t : Complex) * d ∈ U)
    (hbound : ‖iteratedFDeriv Real 4 f
      (z + (t : Complex) * d)‖ <= M) :
    |iteratedDeriv 4
      (fun s : Real => f (z + (s : Complex) * d)) t| <=
        M * ‖d‖ ^ 4 := by
  rw [iteratedDeriv_complexLine_eq_of_contDiffOn
    4 f U z d t hU hf ht, <- Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv Real 4 f (z + (t : Complex) * d)
        (fun _ => d)‖ <=
        ‖iteratedFDeriv Real 4 f (z + (t : Complex) * d)‖ *
          ∏ _ : Fin 4, ‖d‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ <= M * ∏ _ : Fin 4, ‖d‖ := by
      gcongr
    _ = M * ‖d‖ ^ 4 := by simp


theorem abs_iteratedDeriv_complexLine_four_le_tensorNormOn
    (f : Complex -> Real) (U : Set Complex) (z d : Complex) (t M : Real)
    (hU : IsOpen U) (hf : ContDiffOn Real 4 f U)
    (ht : z + (t : Complex) * d ∈ U)
    (hbound : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 f w‖ <= M) :
    |iteratedDeriv 4
      (fun s : Real => f (z + (s : Complex) * d)) t| <=
        M * ‖d‖ ^ 4 := by
  exact abs_iteratedDeriv_complexLine_four_le_tensorNormAt
    f U z d t M hU hf ht (hbound _ ht)

theorem norm_one_add_I_pow_four :
    ‖(1 + Complex.I : Complex)‖ ^ 4 = 4 := by
  calc
    ‖(1 + Complex.I : Complex)‖ ^ 4 =
        (‖(1 + Complex.I : Complex)‖ ^ 2) ^ 2 := by ring
    _ = Complex.normSq (1 + Complex.I) ^ 2 := by
      rw [Complex.sq_norm]
    _ = 4 := by norm_num [Complex.normSq_apply]

theorem norm_one_sub_I_pow_four :
    ‖(1 - Complex.I : Complex)‖ ^ 4 = 4 := by
  calc
    ‖(1 - Complex.I : Complex)‖ ^ 4 =
        (‖(1 - Complex.I : Complex)‖ ^ 2) ^ 2 := by ring
    _ = Complex.normSq (1 - Complex.I) ^ 2 := by
      rw [Complex.sq_norm]
    _ = 4 := by norm_num [Complex.normSq_apply]



theorem iteratedDeriv_complexLine_two_eq
    (f : Complex -> Real) (z d : Complex) (hf : ContDiffAt Real 2 f z) :
    iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * d)) 0 =
      iteratedFDeriv Real 2 f z ![d, d] := by
  let g : Real →L[Real] Complex := complexLineCLM d
  let a : Real -> Complex := fun t => z + g t
  have ha : ContDiffAt Real 2 a 0 := by
    dsimp [a]
    fun_prop
  have hfz : ContDiffAt Real 2 f (a 0) := by
    simpa [a] using hf
  change iteratedDeriv 2 (Function.comp f a) 0 = _
  rw [iteratedDeriv_vcomp_two hfz ha]
  have ha0 : a 0 = z := by simp [a]
  rw [ha0]
  have hderiv : deriv a 0 = d := by
    calc
      deriv a 0 = g 1 :=
        ((g.hasFDerivAt.hasDerivAt.const_add z).deriv)
      _ = d := by simp [g, complexLineCLM]
  have hsecond : iteratedDeriv 2 a 0 = 0 := by
    change iteratedDeriv 2 (fun t => z + g t) 0 = 0
    rw [iteratedDeriv_const_add (n := 2) (by norm_num)]
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hderivg : deriv (g : Real -> Complex) = fun _ => g 1 := by
      funext x
      exact g.hasFDerivAt.hasDerivAt.deriv
    rw [hderivg]
    simp
  rw [hderiv, hsecond]
  simp only [map_zero, add_zero]
  change (iteratedFDeriv Real 2 f z fun _ => d) = _
  congr 1
  funext i
  fin_cases i <;> rfl



theorem harmonicAt_diagonal_iteratedDeriv_add_eq_zero
    (f : Complex -> Real) (z : Complex) (hharmonic : HarmonicAt f z) :
    iteratedDeriv 2
        (fun t : Real => f (z + (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2
        (fun t : Real => f (z + (t : Complex) * (1 - Complex.I))) 0 = 0 := by
  rw [iteratedDeriv_complexLine_two_eq f z (1 + Complex.I) hharmonic.1,
    iteratedDeriv_complexLine_two_eq f z (1 - Complex.I) hharmonic.1]
  have hlap : (Laplacian.laplacian f) z = 0 :=
    hharmonic.2.self_of_nhds
  rw [laplacian_eq_iteratedFDeriv_complexPlane] at hlap
  let B := bilinearIteratedFDerivTwo Real f z
  rw [<- bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    <- bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change B (1 + Complex.I) (1 + Complex.I) +
    B (1 - Complex.I) (1 - Complex.I) = 0
  change iteratedFDeriv Real 2 f z ![1, 1] +
    iteratedFDeriv Real 2 f z ![Complex.I, Complex.I] = 0 at hlap
  rw [<- bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    <- bilinearIteratedFDerivTwo_eq_iteratedFDeriv] at hlap
  change B 1 1 + B Complex.I Complex.I = 0 at hlap
  simp only [map_add, map_sub]
  change ((B 1 1 + B Complex.I 1) +
      (B 1 Complex.I + B Complex.I Complex.I)) +
    ((B 1 1 - B Complex.I 1) -
      (B 1 Complex.I - B Complex.I Complex.I)) = 0
  linarith



theorem DirectionalFourthOrderHarmonicData.ofContDiffHarmonic
    (f : Complex -> Real) (z : Complex) (boundOne boundTwo : Real)
    (hf : ContDiff Real 4 f)
    (hfourthOne : forall t,
      |iteratedDeriv 4
        (fun s : Real => f (z + (s : Complex) * (1 + Complex.I))) t| <=
          boundOne)
    (hfourthTwo : forall t,
      |iteratedDeriv 4
        (fun s : Real => f (z + (s : Complex) * (1 - Complex.I))) t| <=
          boundTwo)
    (hharmonic : HarmonicAt f z) :
    DirectionalFourthOrderHarmonicData f z boundOne boundTwo where
  contDiffOne := by
    have hshift : ContDiff Real 4 (fun w : Complex => f (z + w)) := by
      fun_prop
    simpa [Function.comp_def, complexLineCLM] using
      hshift.comp (complexLineCLM (1 + Complex.I)).contDiff
  contDiffTwo := by
    have hshift : ContDiff Real 4 (fun w : Complex => f (z + w)) := by
      fun_prop
    simpa [Function.comp_def, complexLineCLM] using
      hshift.comp (complexLineCLM (1 - Complex.I)).contDiff
  fourthOne := hfourthOne
  fourthTwo := hfourthTwo
  harmonic := harmonicAt_diagonal_iteratedDeriv_add_eq_zero f z hharmonic



theorem DirectionalFourthOrderHarmonicData.ofLineContDiffAnalyticIm
    (Phi : Complex -> Complex) (z : Complex) (boundOne boundTwo : Real)
    (hcontOne : ContDiff Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 + Complex.I))).im))
    (hcontTwo : ContDiff Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 - Complex.I))).im))
    (hfourthOne : forall t,
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hfourthTwo : forall t,
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z
      boundOne boundTwo where
  contDiffOne := hcontOne
  contDiffTwo := hcontTwo
  fourthOne := hfourthOne
  fourthTwo := hfourthTwo
  harmonic := harmonicAt_diagonal_iteratedDeriv_add_eq_zero
    (fun w => (Phi w).im) z hanalytic.harmonicAt_im



theorem DirectionalFourthOrderHarmonicData.ofContDiffAnalyticIm
    (Phi : Complex -> Complex) (z : Complex) (boundOne boundTwo : Real)
    (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
    (hfourthOne : forall t,
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hfourthTwo : forall t,
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z
      boundOne boundTwo :=
  DirectionalFourthOrderHarmonicData.ofContDiffHarmonic
    (fun w => (Phi w).im) z boundOne boundTwo hsmooth
    hfourthOne hfourthTwo hanalytic.harmonicAt_im



theorem DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm
    (Phi : Complex -> Complex) (z : Complex) (M : Real)
    (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
    (htensor : forall w,
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hanalytic : AnalyticAt Complex Phi z) :
    DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z
      (4 * M) (4 * M) := by
  apply DirectionalFourthOrderHarmonicData.ofContDiffAnalyticIm
    Phi z (4 * M) (4 * M) hsmooth
  · intro t
    calc
      |iteratedDeriv 4
          (fun s : Real =>
            (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <=
          M * ‖(1 + Complex.I : Complex)‖ ^ 4 :=
        abs_iteratedDeriv_complexLine_four_le_tensorNorm
          (fun w => (Phi w).im) z (1 + Complex.I) t M hsmooth htensor
      _ = 4 * M := by rw [norm_one_add_I_pow_four]; ring
  · intro t
    calc
      |iteratedDeriv 4
          (fun s : Real =>
            (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <=
          M * ‖(1 - Complex.I : Complex)‖ ^ 4 :=
        abs_iteratedDeriv_complexLine_four_le_tensorNorm
          (fun w => (Phi w).im) z (1 - Complex.I) t M hsmooth htensor
      _ = 4 * M := by rw [norm_one_sub_I_pow_four]; ring
  · exact hanalytic

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
