/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStripCauchyFourthOrder











open Metric Set

noncomputable section

set_option maxHeartbeats 1800000 in



theorem isingFermionic_verticalOscillation_cauchy_first
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= C) :
    ‖iteratedDeriv 1 Phi c‖ <= 4 * C / d := by
  let shift : Complex -> Complex := fun t => Phi (c + t)
  have hmap : Set.MapsTo (fun t : Complex => c + t) (ball 0 d) (ball c d) := by
    intro t ht
    simpa [Metric.mem_ball, dist_eq_norm] using ht
  have hshift : DifferentiableOn Complex shift (ball 0 d) :=
    hPhi.comp ((differentiableOn_const c).add differentiableOn_id) hmap
  let g : Complex -> Complex := fun t => -Complex.I * (shift t - shift 0)
  have hg : DifferentiableOn Complex g (ball 0 d) :=
    (differentiableOn_const (-Complex.I)).mul
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
  have hBg : forall t, t ∈ sphere 0 (d / 2) -> ‖g t‖ <= 2 * C := by
    intro t ht
    have hnorm : ‖t‖ = d / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ht
    have htball : t ∈ ball 0 d := by
      simp only [_root_.Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
      linarith
    have hb := Complex.borelCaratheodory_zero
      (f := g) (R := d) (M := C) (z := t)
      hC hg hgre hd htball hgzero
    rw [hnorm] at hb
    calc
      ‖g t‖ <= 2 * C * (d / 2) / (d - d / 2) := hb
      _ = 2 * C := by
        field_simp [hd.ne']
        ring
  have hgSmall : DiffContOnCl Complex g (ball 0 (d / 2)) := by
    constructor
    · exact hg.mono (Metric.ball_subset_ball (by linarith))
    · apply hg.continuousOn.mono
      rw [closure_ball 0 (by positivity)]
      exact Metric.closedBall_subset_ball (by linarith)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := g) 1 (by positivity : 0 < d / 2) hgSmall hBg
  have hgfun : g = fun t => Complex.I * shift 0 + (-Complex.I) * shift t := by
    funext t
    simp only [g]
    ring
  have hgderiv : iteratedDeriv 1 g 0 =
      -Complex.I * iteratedDeriv 1 shift 0 := by
    rw [hgfun, iteratedDeriv_const_add (by norm_num)]
    exact iteratedDeriv_const_mul_field (-Complex.I) shift
  have hnormderiv : ‖iteratedDeriv 1 g 0‖ =
      ‖iteratedDeriv 1 shift 0‖ := by
    rw [hgderiv]
    simp
  rw [hnormderiv, iteratedDeriv_comp_const_add 1 Phi c] at hc
  dsimp [shift] at hc
  have hc' : ‖iteratedDeriv 1 Phi c‖ <= 2 * C / (d / 2) := by
    simpa using hc
  calc
    ‖iteratedDeriv 1 Phi c‖ <= 2 * C / (d / 2) := hc'
    _ = 4 * C / d := by
      field_simp [hd.ne']
      ring



theorem isingFermionic_norm_fderiv_real_im_le_iteratedDeriv_first
    (Phi : Complex -> Complex) (c : Complex)
    (hPhi : ContDiffAt Complex 1 Phi c) :
    ‖fderiv Real (fun u => (Phi u).im) c‖ <=
      ‖iteratedDeriv 1 Phi c‖ := by
  have hreal : ContDiffAt Real 1 Phi c := hPhi.restrict_scalars Real
  have him := Complex.imCLM.norm_iteratedFDeriv_comp_left
    (n := 1) (N := 1) hreal (by norm_num)
  rw [Complex.imCLM_norm, one_mul] at him
  change ‖iteratedFDeriv Real 1 (fun u => (Phi u).im) c‖ <= _ at him
  rw [← hPhi.restrictScalars_iteratedFDeriv (𝕜 := Real)] at him
  simp only [Function.comp_apply] at him
  rw [ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    norm_iteratedFDeriv_one] at him
  exact him



theorem isingFermionic_verticalOscillation_im_fderiv_le_on_halfBall
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d -> forall w, w ∈ ball c d ->
      |(Phi z).im - (Phi w).im| <= C) :
    forall w, w ∈ ball c (d / 2) ->
      ‖fderiv Real (fun u => (Phi u).im) w‖ <= 8 * C / d := by
  intro w hw
  have hsub := isingFermionic_ball_half_subset_ball_of_mem hw
  have hPhiLocal := hPhi.mono hsub
  have hPhiAt : ContDiffAt Complex 1 Phi w :=
    (hPhiLocal.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by positivity : 0 < d / 2)))
  have hcomplex := isingFermionic_verticalOscillation_cauchy_first
    Phi w (d / 2) C (by positivity) hC hPhiLocal
      (fun z hz => hosc z (hsub hz) w
        (hsub (Metric.mem_ball_self (by positivity))))
  calc
    ‖fderiv Real (fun u => (Phi u).im) w‖ <=
        ‖iteratedDeriv 1 Phi w‖ :=
      isingFermionic_norm_fderiv_real_im_le_iteratedDeriv_first Phi w hPhiAt
    _ <= 4 * C / (d / 2) := hcomplex
    _ = 8 * C / d := by
      field_simp [hd.ne']
      ring





theorem isingFermionic_verticalOscillation_lipschitzOn_carrier_of_balls
    (Phi : Complex -> Complex) (K : Set Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : forall c, c ∈ K ->
      DifferentiableOn Complex Phi (ball c d))
    (hoscBall : forall c, c ∈ K -> forall z, z ∈ ball c d ->
      forall w, w ∈ ball c d -> |(Phi z).im - (Phi w).im| <= C)
    (hoscCarrier : forall z, z ∈ K -> forall w, w ∈ K ->
      |(Phi z).im - (Phi w).im| <= C) :
    LipschitzOnWith ⟨8 * C / d, by positivity⟩
      (fun z => (Phi z).im) K := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  by_cases hxy : dist x y < d / 2
  · have hyBall : y ∈ ball x (d / 2) := by
      rw [Metric.mem_ball, dist_comm]
      exact hxy
    have hxBall : x ∈ ball x (d / 2) := Metric.mem_ball_self (by positivity)
    have hdiff : forall z, z ∈ ball x (d / 2) ->
        DifferentiableAt Real (fun u => (Phi u).im) z := by
      intro z hz
      have hzPhi : DifferentiableAt Complex Phi z :=
        (hPhi x hx).differentiableAt
          (Metric.isOpen_ball.mem_nhds
            (isingFermionic_ball_half_subset_ball_of_mem hz
              (Metric.mem_ball_self (by positivity))))
      exact (Complex.imCLM.hasFDerivAt.comp z
        (hzPhi.restrictScalars Real).hasFDerivAt).differentiableAt
    have hbound : forall z, z ∈ ball x (d / 2) ->
        ‖fderiv Real (fun u => (Phi u).im) z‖₊ <=
          (⟨8 * C / d, by positivity⟩ : NNReal) := by
      intro z hz
      exact_mod_cast
        isingFermionic_verticalOscillation_im_fderiv_le_on_halfBall
          Phi x d C hd hC (hPhi x hx) (hoscBall x hx) z hz
    have hLip : LipschitzOnWith ⟨8 * C / d, by positivity⟩
        (fun z => (Phi z).im) (ball x (d / 2)) :=
      (convex_ball x (d / 2)).lipschitzOnWith_of_nnnorm_fderiv_le
        hdiff hbound
    exact hLip.norm_sub_le hxBall hyBall
  · have hsep : d / 2 <= dist x y := le_of_not_gt hxy
    have hsep' : d / 2 <= ‖x - y‖ := by
      simpa [dist_eq_norm] using hsep
    have hosc := hoscCarrier x hx y hy
    rw [Real.norm_eq_abs]
    calc
      |(Phi x).im - (Phi y).im| <= C := hosc
      _ <= (8 * C / d) * ‖x - y‖ := by
        have hone : 1 <= (8 / d) * ‖x - y‖ := by
          calc
            1 <= 4 := by norm_num
            _ = (8 / d) * (d / 2) := by
              field_simp [hd.ne']
              ring
            _ <= (8 / d) * ‖x - y‖ :=
              mul_le_mul_of_nonneg_left hsep' (by positivity)
        calc
          C = C * 1 := by ring
          _ <= C * ((8 / d) * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left hone hC.le
          _ = (8 * C / d) * ‖x - y‖ := by ring
      _ = (⟨8 * C / d, by positivity⟩ : NNReal) * ‖x - y‖ := rfl


theorem isingFermionic_unitStrip_lipschitzOn_carrier_of_balls
    (Phi : Complex -> Complex) (K : Set Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : forall c, c ∈ K ->
      DifferentiableOn Complex Phi (ball c d))
    (hrangeBall : forall c, c ∈ K -> forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1)
    (hrangeCarrier : forall z, z ∈ K ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    LipschitzOnWith ⟨8 / d, by positivity⟩
      (fun z => (Phi z).im) K := by
  simpa only [mul_one] using
    (isingFermionic_verticalOscillation_lipschitzOn_carrier_of_balls
      Phi K d 1 hd one_pos hPhi
        (fun c hc z hz w hw => by
          have hz' := hrangeBall c hc z hz
          have hw' := hrangeBall c hc w hw
          rw [abs_le]
          constructor <;> linarith)
        (fun z hz w hw => by
          have hz' := hrangeCarrier z hz
          have hw' := hrangeCarrier w hw
          rw [abs_le]
          constructor <;> linarith))

end
