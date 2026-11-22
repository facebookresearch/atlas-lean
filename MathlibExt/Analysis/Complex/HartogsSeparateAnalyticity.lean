/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.JensenFormula

import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.TietzeExtension

/-!
# Hartogs' theorem on separate analyticity

This file proves that a scalar-valued function on finite-dimensional complex Euclidean space is
holomorphic when it is holomorphic in each coordinate separately.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.HartogsWanted

open Set Metric Filter ContinuousLinearMap
open MeasureTheory
open scoped Topology

/-- The positive logarithm of the norm of a holomorphic function satisfies the circle
sub-mean-value inequality. -/
theorem hartogs_posLog_norm_le_circleAverage {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) :
    Real.posLog ‖f c‖ ≤ Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) c R := by
  have hf_abs : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hR] using hf
  by_cases hc : ‖f c‖ ≤ 1
  · rw [(Real.posLog_eq_zero_iff _).2 (by simpa using hc)]
    exact Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.posLog_nonneg
  have hfc : f c ≠ 0 := fun h ↦ hc (by simp [h])
  have hlog : Real.log ‖f c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖f z‖) c R := by
    rw [hf_abs.circleAverage_log_norm hR.ne' hfc]
    simp only [le_add_iff_nonneg_left]
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · refine mul_nonneg ?_ ?_
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_abs u
      by_cases huc : u = c
      · simp [huc]
      apply Real.log_nonneg
      have hnorm_pos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
      apply (le_mul_inv_iff₀ hnorm_pos).2
      simpa [Metric.mem_closedBall, dist_eq_norm', abs_of_pos hR] using hu
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, hu]
  rw [Real.posLog_eq_log (by simpa using le_of_not_ge hc)]
  exact hlog.trans (Real.circleAverage_mono
    (hf_abs.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    (hf_abs.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_posLog_norm
    (fun z _ ↦ by rw [Real.posLog_apply]; exact le_max_right _ _))

private theorem hartogs_exists_interior_uniform_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace F] {f : E → F → ℂ} {K : Set F} (hK : IsCompact K)
    (hz : ∀ w ∈ K, Continuous (fun z ↦ f z w))
    (hw : ∀ z, ContinuousOn (f z) K) :
    ∃ m : ℕ, (interior {z | ∀ w ∈ K, ‖f z w‖ ≤ m}).Nonempty := by
  let S : ℕ → Set E := fun m ↦ {z | ∀ w ∈ K, ‖f z w‖ ≤ m}
  have hclosed : ∀ m, IsClosed (S m) := by
    intro m
    rw [show S m = ⋂ w ∈ K, {z | ‖f z w‖ ≤ m} by ext; simp [S]]
    apply isClosed_biInter
    intro w hwK
    exact isClosed_Iic.preimage (hz w hwK).norm
  have hcover : ⋃ m, S m = univ := by
    apply Set.eq_univ_iff_forall.2
    intro z
    rcases hK.bddAbove_image (hw z).norm with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    apply Set.mem_iUnion.2 ⟨m, ?_⟩
    intro w hwK
    exact (hC (Set.mem_image_of_mem _ hwK)).trans hm
  simpa [S] using nonempty_interior_of_iUnion_of_closed hclosed hcover

private theorem half_ball_subset_unit_ball
    {F : Type*} [NormedAddCommGroup F]
    {x : F} (hx : x ∈ closedBall 0 (1 / 2 : ℝ)) :
    closedBall x (1 / 2 : ℝ) ⊆ closedBall 0 1 := by
  intro y hy
  rw [mem_closedBall] at hx hy ⊢
  calc
    dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hy hx
    _ = 1 := by norm_num

private theorem quarter_ball_subset_half_ball
    {F : Type*} [NormedAddCommGroup F]
    {x : F} (hx : x ∈ closedBall 0 (1 / 4 : ℝ)) :
    x ∈ closedBall 0 (1 / 2 : ℝ) := by
  exact mem_closedBall'.2 ((mem_closedBall'.1 hx).trans (by norm_num))

private theorem continuousAt_of_hartogs_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {D : E × ℂ → F} {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ z ∈ closedBall 0 (1 / 4 : ℝ), ∀ w ∈ closedBall 0 (1 / 4 : ℝ),
      ‖D (z, w) - D (0, 0)‖ ≤ 8 * M * (‖z‖ + ‖w‖)) : ContinuousAt D (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A : ℝ := 8 * M
  let δ : ℝ := min (1 / 4) (ε / (2 * (A + 1)))
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hM
  have hden : 0 < 2 * (A + 1) := mul_pos (by norm_num) (by linarith)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hpmax : max ‖p.1‖ ‖p.2‖ < δ := by
    simpa only [Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, dist_zero_right] using hp
  have hp₁lt : ‖p.1‖ < δ := (le_max_left _ _).trans_lt hpmax
  have hp₂lt : ‖p.2‖ < δ := (le_max_right _ _).trans_lt hpmax
  have hp₁ : p.1 ∈ closedBall 0 (1 / 4 : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact hp₁lt.le.trans (min_le_left _ _)
  have hp₂ : p.2 ∈ closedBall 0 (1 / 4 : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact hp₂lt.le.trans (min_le_left _ _)
  have hδε : δ * (2 * (A + 1)) ≤ ε :=
    (le_div_iff₀ hden).1 (min_le_right _ _)
  rw [dist_eq_norm]
  refine (hD p.1 hp₁ p.2 hp₂).trans_lt ?_
  change A * (‖p.1‖ + ‖p.2‖) < ε
  nlinarith

/-- A separately holomorphic function whose values are bounded on the product of the unit
balls is jointly complex differentiable at the center. -/
theorem differentiableAt_uncurry_of_separately_differentiable_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ → ℂ} {M : ℝ}
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ closedBall 0 1, ∀ w ∈ closedBall 0 1, ‖f z w‖ ≤ M) :
    DifferentiableAt ℂ (Function.uncurry f) (0, 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0 0)).trans (hM 0 (by simp) 0 (by simp))
  have hzeroE : (0 : E) ∈ closedBall 0 (1 / 2 : ℝ) := by simp
  have hzeroC : (0 : ℂ) ∈ closedBall 0 (1 / 2 : ℝ) := by simp
  have hline (a v : E) : HasDerivAt (fun t : ℂ ↦ a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const v).const_add a
  have hlineDeriv (a v : E) (w : ℂ) :
      deriv (fun t : ℂ ↦ f (a + t • v) w) 0 =
        fderiv ℂ (fun z ↦ f z w) a v := by
    change deriv ((fun z ↦ f z w) ∘ fun t : ℂ ↦ a + t • v) 0 = _
    simpa only [zero_smul, add_zero] using
      ((hf₁ w (a + (0 : ℂ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hline a v)).deriv
  have hfderiv₁ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖fderiv ℂ (fun x ↦ f x w) z‖ ≤ 2 * M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM0)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    have hdiff : Differentiable ℂ (fun t : ℂ ↦ f (z + t • u) w) :=
      (hf₁ w).comp (by fun_prop)
    have hbound : ‖deriv (fun t : ℂ ↦ f (z + t • u) w) 0‖ ≤ 2 * M := by
      calc
        _ ≤ M / (1 / 2 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
            hdiff.diffContOnCl fun t ht ↦ by
              apply hM (z + t • u)
              · apply half_ball_subset_unit_ball hz
                have htq : ‖t‖ = 1 / 2 := by
                  simpa [mem_sphere, dist_zero_right] using ht
                simp [mem_closedBall, dist_eq_norm, norm_smul, hunorm, htq]
              · exact half_ball_subset_unit_ball hw (by simp)
        _ = 2 * M := by ring
    rw [hlineDeriv] at hbound
    have hscale : fderiv ℂ (fun x ↦ f x w) z v =
        (‖v‖ : ℂ) • fderiv ℂ (fun x ↦ f x w) z u := by
      calc
        _ = fderiv ℂ (fun x ↦ f x w) z ((‖v‖ : ℂ) • u) := congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    calc
      ‖fderiv ℂ (fun x ↦ f x w) z v‖ =
          ‖(‖v‖ : ℂ)‖ * ‖fderiv ℂ (fun x ↦ f x w) z u‖ := by
        rw [hscale, norm_smul]
      _ = ‖v‖ * ‖fderiv ℂ (fun x ↦ f x w) z u‖ := by simp
      _ ≤ ‖v‖ * (2 * M) := mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
      _ = 2 * M * ‖v‖ := by ring
  have hderiv₂ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖deriv (f z) w‖ ≤ 2 * M := by
    calc
      ‖deriv (f z) w‖ ≤ M / (1 / 2 : ℝ) :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
          (hf₂ z).diffContOnCl fun x hx ↦ hM z (half_ball_subset_unit_ball hz (by simp)) x
            (half_ball_subset_unit_ball hw (sphere_subset_closedBall hx))
      _ = 2 * M := by ring
  have hvalue₁ {z z' : E} {w : ℂ}
      (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hz' : z' ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖f z w - f z' w‖ ≤ 2 * M * ‖z - z'‖ := by
    exact (convex_closedBall (0 : E) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ ↦ hf₁ w x) (fun x hx ↦ hfderiv₁ hx hw) hz' hz
  have hvalue₂ {z : E} {w w' : ℂ}
      (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ))
      (hw' : w' ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖f z w - f z w'‖ ≤ 2 * M * ‖w - w'‖ := by
    simpa [dist_eq_norm] using
      (convex_closedBall (0 : ℂ) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_deriv_le
        (f := f z) (x := w') (y := w) (fun x _ ↦ hf₂ z x)
        (fun x hx ↦ hderiv₂ hz hx) hw' hw
  have hD₁ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 4 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 4 : ℝ)) :
      ‖fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0‖ ≤
        8 * M * (‖z‖ + ‖w‖) := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num) hM0) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    let g : ℂ → ℂ := fun t ↦ f (z + t • u) w - f (t • u) 0
    have hg : Differentiable ℂ g := by
      dsimp [g]
      exact ((hf₁ w).comp (by fun_prop)).sub ((hf₁ 0).comp (by fun_prop))
    have hgbound (t : ℂ) (ht : t ∈ sphere 0 (1 / 4 : ℝ)) :
        ‖g t‖ ≤ 2 * M * (‖z‖ + ‖w‖) := by
      have htq : ‖t‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using ht
      have htu : t • u ∈ closedBall (0 : E) (1 / 4 : ℝ) := by
        rw [mem_closedBall, dist_zero_right, norm_smul, hunorm, mul_one, htq]
      have hztu : z + t • u ∈ closedBall (0 : E) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right] at hz ⊢
        calc
          ‖z + t • u‖ ≤ ‖z‖ + ‖t • u‖ := norm_add_le _ _
          _ ≤ (1 / 4 : ℝ) + 1 / 4 := add_le_add hz (by simpa [mem_closedBall] using htu)
          _ = 1 / 2 := by norm_num
      have htu' := quarter_ball_subset_half_ball htu
      have hw' := quarter_ball_subset_half_ball hw
      calc
        ‖g t‖ ≤ ‖f (z + t • u) w - f (z + t • u) 0‖ +
            ‖f (z + t • u) 0 - f (t • u) 0‖ := by
          dsimp [g]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * M * ‖w‖ + 2 * M * ‖z‖ := by
          gcongr
          · simpa using hvalue₂ hztu hw' hzeroC
          · simpa using hvalue₁ hztu htu' hzeroC
        _ = 2 * M * (‖z‖ + ‖w‖) := by ring
    have hderiv : ‖deriv g 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
      calc
        _ ≤ (2 * M * (‖z‖ + ‖w‖)) / (1 / 4 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (by norm_num)
            hg.diffContOnCl hgbound
        _ = 8 * M * (‖z‖ + ‖w‖) := by ring
    have hgderiv : deriv g 0 =
        (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) u := by
      rw [show deriv g 0 = deriv (fun t : ℂ ↦ f (z + t • u) w) 0 -
          deriv (fun t : ℂ ↦ f (t • u) 0) 0 by
        exact deriv_sub (((hf₁ w).comp (by fun_prop)) 0) (((hf₁ 0).comp (by fun_prop)) 0)]
      rw [hlineDeriv z u w]
      simpa using hlineDeriv (0 : E) u 0
    rw [hgderiv] at hderiv
    have hscale :
        (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) v =
          (‖v‖ : ℂ) • (fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u := by
      calc
        _ = (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0)
            ((‖v‖ : ℂ) • u) := congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    calc
      ‖(fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) v‖ =
          ‖(‖v‖ : ℂ)‖ * ‖(fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u‖ := by
        rw [hscale, norm_smul]
      _ = ‖v‖ * ‖(fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u‖ := by simp
      _ ≤ ‖v‖ * (8 * M * (‖z‖ + ‖w‖)) :=
        mul_le_mul_of_nonneg_left hderiv (norm_nonneg v)
      _ = 8 * M * (‖z‖ + ‖w‖) * ‖v‖ := by ring
  have hD₂ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 4 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 4 : ℝ)) :
      ‖deriv (f z) w - deriv (f 0) 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
    let g : ℂ → ℂ := fun t ↦ f z (w + t) - f 0 t
    have hg : Differentiable ℂ g := by
      dsimp [g]
      exact ((hf₂ z).comp (by fun_prop)).sub (hf₂ 0)
    have hgbound (t : ℂ) (ht : t ∈ sphere 0 (1 / 4 : ℝ)) :
        ‖g t‖ ≤ 2 * M * (‖z‖ + ‖w‖) := by
      have htq : ‖t‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using ht
      have ht' : t ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right, htq]
        norm_num
      have hwt : w + t ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right] at hw ⊢
        calc
          ‖w + t‖ ≤ ‖w‖ + ‖t‖ := norm_add_le _ _
          _ ≤ (1 / 4 : ℝ) + 1 / 4 := add_le_add hw htq.le
          _ = 1 / 2 := by norm_num
      have hz' := quarter_ball_subset_half_ball hz
      calc
        ‖g t‖ ≤ ‖f z (w + t) - f z t‖ + ‖f z t - f 0 t‖ := by
          dsimp [g]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * M * ‖w‖ + 2 * M * ‖z‖ := by
          gcongr
          · simpa using hvalue₂ hz' hwt ht'
          · simpa using hvalue₁ hz' hzeroE ht'
        _ = 2 * M * (‖z‖ + ‖w‖) := by ring
    have hderiv : ‖deriv g 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
      calc
        _ ≤ (2 * M * (‖z‖ + ‖w‖)) / (1 / 4 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (by norm_num)
            hg.diffContOnCl hgbound
        _ = 8 * M * (‖z‖ + ‖w‖) := by ring
    have hgderiv : deriv g 0 = deriv (f z) w - deriv (f 0) 0 := by
      rw [show deriv g 0 = deriv (fun t : ℂ ↦ f z (w + t)) 0 - deriv (f 0) 0 by
        exact deriv_sub (((hf₂ z).comp (by fun_prop)) 0) (hf₂ 0 0)]
      have hlinew : HasDerivAt (fun t : ℂ ↦ w + t) 1 0 :=
        (hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_add w
      have hcomp := (hf₂ z (w + 0)).hasDerivAt.comp 0 hlinew
      have hcomp' : deriv (fun t : ℂ ↦ f z (w + t)) 0 = deriv (f z) w := by
        change deriv ((f z) ∘ fun t : ℂ ↦ w + t) 0 = _
        simpa only [add_zero, mul_one] using hcomp.deriv
      rw [hcomp']
    rwa [hgderiv] at hderiv
  let f₁ : E → ℂ → E →L[ℂ] ℂ := fun z w ↦ fderiv ℂ (fun x ↦ f x w) z
  let D₂ : E × ℂ → ℂ := fun p ↦ deriv (f p.1) p.2
  let f₂ : E → ℂ → ℂ →L[ℂ] ℂ := fun z w ↦ fderiv ℂ (f z) w
  have hf₁c : ContinuousAt (Function.uncurry f₁) (0, 0) := by
    apply continuousAt_of_hartogs_bound hM0
    intro z hz w hw
    exact hD₁ hz hw
  have hD₂c : ContinuousAt D₂ (0, 0) := by
    apply continuousAt_of_hartogs_bound hM0
    intro z hz w hw
    exact hD₂ hz hw
  have hf₂c : ContinuousAt (Function.uncurry f₂) (0, 0) := by
    rw [show Function.uncurry f₂ = fun p ↦ toSpanSingleton ℂ (D₂ p) by
      funext p
      exact (toSpanSingleton_deriv (f := f p.1) (x := p.2)).symm]
    exact (toSpanSingletonLIE ℂ ℂ).continuous.continuousAt.comp' hD₂c
  exact (hasStrictFDerivAt_uncurry_coprod
    (f₁ := f₁) (f₂ := f₂)
    (Eventually.of_forall fun p ↦ (hf₁ p.2 p.1).hasFDerivAt)
    (Eventually.of_forall fun p ↦ (hf₂ p.1 p.2).hasFDerivAt)
    hf₁c hf₂c).differentiableAt

/-- A separately holomorphic function that is bounded on a product of open neighborhoods is
jointly complex differentiable at every point of that product. -/
theorem differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ → ℂ} {U : Set E} {V : Set ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ U, ∀ w ∈ V, ‖f z w‖ ≤ M)
    {z₀ : E} (hz₀ : z₀ ∈ U) {w₀ : ℂ} (hw₀ : w₀ ∈ V) :
    DifferentiableAt ℂ (Function.uncurry f) (z₀, w₀) := by
  obtain ⟨az, haz, hballz⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  obtain ⟨aw, haw, hballw⟩ := Metric.isOpen_iff.1 hV w₀ hw₀
  let rz : ℝ := az / 2
  let rw : ℝ := aw / 2
  have hrz : 0 < rz := div_pos haz (by norm_num)
  have hrw : 0 < rw := div_pos haw (by norm_num)
  let g : E → ℂ → ℂ := fun z w ↦
    f (z₀ + (rz : ℂ) • z) (w₀ + (rw : ℂ) * w)
  have hg₁ : ∀ w, Differentiable ℂ (fun z ↦ g z w) := by
    intro w
    apply (hf₁ _).comp
    fun_prop
  have hg₂ : ∀ z, Differentiable ℂ (g z) := by
    intro z
    apply (hf₂ _).comp
    fun_prop
  have hgM : ∀ z ∈ closedBall 0 1, ∀ w ∈ closedBall 0 1, ‖g z w‖ ≤ M := by
    intro z hz w hw
    apply hM
    · apply hballz
      rw [mem_ball, dist_eq_norm]
      have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
      have hscaled : rz * ‖z‖ ≤ rz := by
        simpa using mul_le_mul_of_nonneg_left hz' hrz.le
      have hlt : rz * ‖z‖ < az :=
        hscaled.trans_lt (by dsimp [rz]; linarith)
      simpa [g, rz, norm_smul, abs_of_pos haz] using hlt
    · apply hballw
      rw [mem_ball, dist_eq_norm]
      have hw' : ‖w‖ ≤ 1 := by simpa [mem_closedBall] using hw
      have hscaled : rw * ‖w‖ ≤ rw := by
        simpa using mul_le_mul_of_nonneg_left hw' hrw.le
      have hlt : rw * ‖w‖ < aw :=
        hscaled.trans_lt (by dsimp [rw]; linarith)
      simpa [g, rw, norm_mul, abs_of_pos haw] using hlt
  have hg :=
    differentiableAt_uncurry_of_separately_differentiable_of_bounded hg₁ hg₂ hgM
  let H : E × ℂ → E × ℂ := fun p ↦
    (((rz : ℂ)⁻¹ • (p.1 - z₀)), (rw : ℂ)⁻¹ * (p.2 - w₀))
  have hH : Differentiable ℂ H := by
    dsimp [H]
    fun_prop
  have hH₀ : H (z₀, w₀) = (0, 0) := by simp [H]
  have hgH : DifferentiableAt ℂ (Function.uncurry g) (H (z₀, w₀)) := by
    rw [hH₀]
    exact hg
  have hcomp := hgH.comp (z₀, w₀) (hH (z₀, w₀))
  convert hcomp using 1
  funext p
  dsimp [Function.uncurry, g, H]
  simp only [ne_eq, Complex.ofReal_eq_zero, hrw.ne', not_false_eq_true,
    mul_inv_cancel_left₀, add_sub_cancel]
  rw [← IsScalarTower.smul_assoc]
  simp [Algebra.smul_def, hrz.ne']

/-- On a bounded product, the Cauchy coefficients in the scalar variable are holomorphic in the
finite-dimensional block variable on a smaller ball. -/
theorem differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E → ℂ → ℂ} {z₀ : E} {w₀ : ℂ} {A B M : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ closedBall z₀ A, ∀ w ∈ closedBall w₀ B, ‖f z w‖ ≤ M)
    (k : ℕ) :
    DifferentiableOn ℂ
      (fun z ↦ (cauchyPowerSeries (f z) w₀ (B / 2) k) (fun _ ↦ 1))
      (ball z₀ (A / 2)) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hM0 : 0 ≤ M :=
    (norm_nonneg (f z₀ w₀)).trans
      (hM z₀ (by simp [hA.le]) w₀ (by simp [hB.le]))
  let S : Set (E × ℂ) :=
    closedBall z₀ (A / 2) ×ˢ closedBall w₀ (3 * B / 4)
  have hSclosed : IsClosed S := isClosed_closedBall.prod isClosed_closedBall
  have hjoint : DifferentiableOn ℂ (Function.uncurry f)
      (ball z₀ A ×ˢ ball w₀ B) := by
    intro p hp
    exact
      (differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
        isOpen_ball isOpen_ball hf₁ hf₂
        (fun z hz w hw ↦ hM z (ball_subset_closedBall hz) w
          (ball_subset_closedBall hw)) hp.1 hp.2).differentiableWithinAt
  have hSsub : S ⊆ ball z₀ A ×ˢ ball w₀ B := by
    intro p hp
    constructor
    · exact (mem_closedBall.1 hp.1).trans_lt (by linarith)
    · exact (mem_closedBall.1 hp.2).trans_lt (by linarith)
  have hcontS : ContinuousOn (Function.uncurry f) S :=
    hjoint.continuousOn.mono hSsub
  let fc : C(S, ℂ) := ⟨S.domRestrict (Function.uncurry f), hcontS.domRestrict⟩
  let fre : C(S, ℝ) :=
    ⟨fun p ↦ (fc p).re, Complex.continuous_re.comp fc.continuous⟩
  let fim : C(S, ℝ) :=
    ⟨fun p ↦ (fc p).im, Complex.continuous_im.comp fc.continuous⟩
  obtain ⟨gre, hgre⟩ := ContinuousMap.exists_restrict_eq hSclosed fre
  obtain ⟨gim, hgim⟩ := ContinuousMap.exists_restrict_eq hSclosed fim
  let G : E × ℂ → ℂ := fun p ↦
    (gre p : ℂ) + Complex.I * (gim p : ℂ)
  have hGc : Continuous G := by
    dsimp [G]
    fun_prop
  have hGeq : ∀ p ∈ S, G p = Function.uncurry f p := by
    intro p hp
    apply Complex.ext
    · have h := DFunLike.congr_fun hgre ⟨p, hp⟩
      simpa [G, fre, fc] using h
    · have h := DFunLike.congr_fun hgim ⟨p, hp⟩
      simpa [G, fim, fc] using h
  let s : ℝ := B / 2
  have hs : 0 < s := div_pos hB (by norm_num)
  have hcircle_ne (t : ℝ) : circleMap 0 s t ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_circleMap_zero, abs_of_pos hs]
    exact hs.ne'
  let weight : ℝ → ℂ := fun t ↦
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (circleMap 0 s t * Complex.I) *
      ((circleMap 0 s t)⁻¹ ^ k * (circleMap 0 s t)⁻¹)
  have hweight : Continuous weight := by
    dsimp [weight]
    fun_prop (disch := aesop)
  let b : E → ℂ := fun z ↦
    (cauchyPowerSeries (fun w ↦ G (z, w)) w₀ s k) (fun _ ↦ 1)
  have hb_eq (z : E) : b z =
      ∫ t in Icc 0 (2 * Real.pi), weight t * G (z, circleMap w₀ s t) := by
    dsimp [b]
    rw [cauchyPowerSeries_apply, circleIntegral_def_Icc]
    simp only [deriv_circleMap, circleMap_sub_center, one_div, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [weight]
    ring
  have hwcircle (t : ℝ) : circleMap w₀ s t ∈ closedBall w₀ (3 * B / 4) := by
    rw [mem_closedBall]
    have ht := circleMap_mem_sphere w₀ hs.le t
    rw [mem_sphere] at ht
    rw [ht]
    dsimp [s]
    linarith
  have hGeq_nhds {z : E} (hz : z ∈ ball z₀ (A / 2)) (t : ℝ) :
      (fun x ↦ G (x, circleMap w₀ s t)) =ᶠ[nhds z]
        (fun x ↦ f x (circleMap w₀ s t)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    exact hGeq _ ⟨ball_subset_closedBall hx, hwcircle t⟩
  have hlineDeriv (z v : E) (w : ℂ) :
      deriv (fun t : ℂ ↦ f (z + t • v) w) 0 =
        fderiv ℂ (fun x ↦ f x w) z v := by
    have hline : HasDerivAt (fun t : ℂ ↦ z + t • v) v 0 := by
      simpa using
        ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const v).const_add z
    change deriv ((fun x ↦ f x w) ∘ fun t : ℂ ↦ z + t • v) 0 = _
    simpa only [zero_smul, add_zero] using
      ((hf₁ w (z + (0 : ℂ) • v)).hasFDerivAt.comp_hasDerivAt 0 hline).deriv
  let L : ℝ := M / (A / 2)
  have hL : 0 ≤ L := div_nonneg hM0 (by positivity)
  have hfderiv_bound {z : E} (hz : z ∈ ball z₀ (A / 2))
      {w : ℂ} (hw : w ∈ closedBall w₀ B) :
      ‖fderiv ℂ (fun x ↦ f x w) z‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    have hdiff : Differentiable ℂ (fun t : ℂ ↦ f (z + t • u) w) :=
      (hf₁ w).comp (by fun_prop)
    have hbound : ‖deriv (fun t : ℂ ↦ f (z + t • u) w) 0‖ ≤ L := by
      apply
        (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
          (div_pos hA (by norm_num)) hdiff.diffContOnCl ?_)
      intro t ht
      apply hM (z + t • u)
      · rw [mem_closedBall]
        have htq : ‖t‖ = A / 2 := by
          simpa [mem_sphere, dist_zero_right] using ht
        calc
          dist (z + t • u) z₀ ≤ dist (z + t • u) z + dist z z₀ :=
            dist_triangle _ _ _
          _ = ‖t‖ + dist z z₀ := by
            simp [dist_eq_norm, norm_smul, hunorm]
          _ ≤ A := by
            have hz' := mem_ball.1 hz
            linarith
      · exact hw
    rw [hlineDeriv] at hbound
    have hscale : fderiv ℂ (fun x ↦ f x w) z v =
        (‖v‖ : ℂ) • fderiv ℂ (fun x ↦ f x w) z u := by
      calc
        _ = fderiv ℂ (fun x ↦ f x w) z ((‖v‖ : ℂ) • u) :=
          congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    rw [hscale, norm_smul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
  let g : ℂ → E → ℂ := fun w z ↦ G (z, w)
  have hgcont : Continuous (Function.uncurry g) := by
    change Continuous (fun p : ℂ × E ↦ G (p.2, p.1))
    exact hGc.comp (by fun_prop)
  have hfdmeas : Measurable (fun p : ℂ × E ↦ fderiv ℂ (g p.1) p.2) :=
    measurable_fderiv_with_param ℂ hgcont
  let J : E → ℂ := fun z ↦
    ∫ t in Icc 0 (2 * Real.pi), weight t * G (z, circleMap w₀ s t)
  have hJ : DifferentiableOn ℂ J (ball z₀ (A / 2)) := by
    intro z hz
    let F : E → ℝ → ℂ := fun x t ↦
      weight t * G (x, circleMap w₀ s t)
    let F' : E → ℝ → E →L[ℂ] ℂ := fun x t ↦
      weight t • fderiv ℂ (g (circleMap w₀ s t)) x
    let bound : ℝ → ℝ := fun t ↦ ‖weight t‖ * L
    have hFcont (x : E) : Continuous (F x) := by
      dsimp [F]
      exact hweight.mul (hGc.comp (by fun_prop))
    have hF'_meas :
        AEStronglyMeasurable (F' z) (volume.restrict (Icc 0 (2 * Real.pi))) := by
      apply Measurable.aestronglyMeasurable
      dsimp [F']
      apply hweight.measurable.smul
      simpa [Function.comp_def] using hfdmeas.comp
        (Measurable.prod (f := fun t : ℝ ↦ (circleMap w₀ s t, z))
          (continuous_circleMap w₀ s).measurable measurable_const)
    have hbound_int :
        Integrable bound (volume.restrict (Icc 0 (2 * Real.pi))) := by
      apply Continuous.integrableOn_Icc
      dsimp [bound]
      exact hweight.norm.mul continuous_const
    have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (isOpen_ball.mem_nhds hz)
      (Eventually.of_forall fun x ↦ (hFcont x).aestronglyMeasurable)
      ((hFcont z).integrableOn_Icc) hF'_meas (bound := bound)
      (by
        filter_upwards with t x hx
        dsimp [F', bound]
        have hfd_eq : fderiv ℂ (g (circleMap w₀ s t)) x =
            fderiv ℂ (fun y ↦ f y (circleMap w₀ s t)) x :=
          (hGeq_nhds hx t).fderiv_eq
        rw [norm_smul, hfd_eq]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply hfderiv_bound hx
        rw [mem_closedBall]
        have ht := circleMap_mem_sphere w₀ hs.le t
        rw [mem_sphere] at ht
        rw [ht]
        dsimp [s]
        linarith)
      hbound_int
      (by
        filter_upwards with t x hx
        dsimp [F, F']
        have hGderiv :=
          (hf₁ (circleMap w₀ s t) x).hasFDerivAt.congr_of_eventuallyEq
            (hGeq_nhds hx t)
        have hfd_eq : fderiv ℂ (g (circleMap w₀ s t)) x =
            fderiv ℂ (fun y ↦ f y (circleMap w₀ s t)) x :=
          (hGeq_nhds hx t).fderiv_eq
        rw [hfd_eq]
        exact hGderiv.const_mul (weight t))
    have hJeq : J = fun x ↦ ∫ t in Icc 0 (2 * Real.pi), F x t := by
      rfl
    rw [hJeq]
    exact hparam.differentiableAt.differentiableWithinAt
  have hab : ∀ z ∈ ball z₀ (A / 2),
      (cauchyPowerSeries (f z) w₀ s k) (fun _ ↦ 1) = b z := by
    intro z hz
    dsimp [b]
    rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
    congr 1
    apply circleIntegral.integral_congr hs.le
    intro w hw
    have hwS : w ∈ closedBall w₀ (3 * B / 4) := by
      rw [mem_closedBall]
      have hw' := mem_sphere.1 hw
      rw [hw']
      dsimp [s]
      linarith
    dsimp
    rw [hGeq (z, w) ⟨ball_subset_closedBall hz, hwS⟩]
    rfl
  have hbJ : b = J := funext hb_eq
  rw [hbJ] at hab
  exact hJ.congr hab

/-- Cauchy's estimate for a scalar Taylor coefficient, stated for Mathlib's
`cauchyPowerSeries`. -/
theorem norm_cauchyCoefficient_le
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : Differentiable ℂ f)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(cauchyPowerSeries f c R).coeff k‖ ≤ M * R⁻¹ ^ k := by
  have hcont : Continuous (fun θ : ℝ ↦ ‖f (circleMap c R θ)‖) :=
    hf.continuous.norm.comp (continuous_circleMap c R)
  have hint :
      (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) ≤
        ∫ _θ : ℝ in 0..2 * Real.pi, M := by
    apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro θ _hθ
    exact hM _ (circleMap_mem_sphere c hR.le θ)
  have hseries := norm_cauchyPowerSeries_le f c R k
  have heval : ‖(cauchyPowerSeries f c R).coeff k‖ ≤
      ‖cauchyPowerSeries f c R k‖ := by
    rw [FormalMultilinearSeries.coeff]
    calc
      _ ≤ ‖cauchyPowerSeries f c R k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        (cauchyPowerSeries f c R k).le_opNorm (fun _ ↦ 1)
      _ = _ := by simp
  calc
    ‖(cauchyPowerSeries f c R).coeff k‖ ≤
        ‖cauchyPowerSeries f c R k‖ := heval
    _ ≤ ((2 * Real.pi)⁻¹ *
          ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) *
        |R|⁻¹ ^ k := hseries
    _ ≤ ((2 * Real.pi)⁻¹ * (2 * Real.pi * M)) * R⁻¹ ^ k := by
      rw [abs_of_pos hR]
      gcongr
      simpa using hint
    _ = M * R⁻¹ ^ k := by
      field_simp [Real.pi_ne_zero]

private lemma disk_integral_eq_polar {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (_hR : 0 ≤ R) :
    ∫ z in closedBall (0 : ℂ) R, u z =
      ∫ r in Ioc 0 R, ∫ θ in Ioo (-Real.pi) Real.pi,
        r * u (Complex.polarCoord.symm (r, θ)) := by
  rw [← integral_indicator measurableSet_closedBall]
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [polarCoord_target]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ ↦ p.1 * u (Complex.polarCoord.symm p))
      (Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hpolar : Continuous (fun p : ℝ × ℝ ↦
        Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    have hbig : IntegrableOn
        (fun p : ℝ × ℝ ↦ p.1 * u (Complex.polarCoord.symm p))
        (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) :=
      ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
        ((continuous_fst.mul (hu.comp hpolar)).continuousOn)
    exact hbig.mono_set fun _ hp ↦
      ⟨Ioc_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
  rw [Measure.volume_eq_prod]
  rw [← setIntegral_prod _ hint]
  rw [← integral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  rw [← integral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  congr 1
  funext p
  by_cases hpθ : p.2 ∈ Ioo (-Real.pi) Real.pi
  · by_cases hpr : 0 < p.1
    · by_cases hpR : p.1 ≤ R
      · have habs : |p.1| ≤ R := by simpa [abs_of_pos hpr] using hpR
        simp [hpr, hpR, hpθ, habs, smul_eq_mul]
      · have habs : ¬|p.1| ≤ R := by simpa [abs_of_pos hpr] using hpR
        simp [hpr, hpR, hpθ, habs]
    · have hpnonpos : p.1 ≤ 0 := le_of_not_gt hpr
      have hpnot : p.1 ∉ Ioc 0 R := by simp [hpnonpos]
      simp [hpr, hpnot]
  · simp [hpθ]

private lemma angular_integral_eq_circleAverage (u : ℂ → ℝ) (r : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, u (Complex.polarCoord.symm (r, θ)) =
      2 * Real.pi * Real.circleAverage u 0 r := by
  rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
  rw [← intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hfun : (fun θ : ℝ ↦ u (Complex.polarCoord.symm (r, θ))) =
      fun θ : ℝ ↦ u (circleMap 0 r θ) := by
    funext θ
    congr 1
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  rw [hfun]
  rw [Real.circleAverage_eq_integral_add (f := u) (c := 0) (R := r) (-Real.pi)]
  have hshift :
      (∫ θ : ℝ in 0..2 * Real.pi, u (circleMap 0 r (θ + -Real.pi))) =
        ∫ θ : ℝ in -Real.pi..Real.pi, u (circleMap 0 r θ) := by
    have h := intervalIntegral.integral_comp_add_right
      (fun θ : ℝ ↦ u (circleMap 0 r θ)) (-Real.pi)
        (a := 0) (b := 2 * Real.pi)
    rw [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring] at h
    exact h
  rw [hshift]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

private lemma disk_integral_eq_polar_closed {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in closedBall (0 : ℂ) R, u z =
      ∫ r in Ioc 0 R, ∫ θ in Icc (-Real.pi) Real.pi,
        r * u (Complex.polarCoord.symm (r, θ)) := by
  rw [disk_integral_eq_polar hu hR]
  congr 1
  funext r
  exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc

private lemma disk_submean_zero {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 < R)
    (hsub : ∀ r ∈ Ioc 0 R, u 0 ≤ Real.circleAverage u 0 r) :
    (volume (closedBall (0 : ℂ) R)).toReal * u 0 ≤
      ∫ z in closedBall (0 : ℂ) R, u z := by
  have hconst : (volume (closedBall (0 : ℂ) R)).toReal * u 0 =
      ∫ r in Ioc 0 R, 2 * Real.pi * r * u 0 := by
    have h := disk_integral_eq_polar_closed
      (u := fun _ : ℂ ↦ u 0) continuous_const hR.le
    have hangle (r : ℝ) :
        (∫ θ in Icc (-Real.pi) Real.pi, r * (u 0 : ℝ)) =
          2 * Real.pi * r * u 0 := by
      rw [← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc]
      rw [MeasureTheory.integral_const_mul]
      have hc : (∫ θ in Ioo (-Real.pi) Real.pi, (u 0 : ℝ)) =
          2 * Real.pi * u 0 := by
        simpa only [Real.circleAverage_const] using
          angular_integral_eq_circleAverage (fun _ : ℂ ↦ u 0) r
      rw [hc]
      ring
    simp_rw [hangle] at h
    rw [MeasureTheory.setIntegral_const] at h
    simpa only [smul_eq_mul, measureReal_def, mul_assoc] using h
  rw [hconst, disk_integral_eq_polar_closed hu hR.le]
  apply MeasureTheory.setIntegral_mono_on
  · exact
      (show Continuous (fun r : ℝ ↦ 2 * Real.pi * r * u 0) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · have hcontinuous : Continuous (fun r : ℝ ↦
        ∫ θ in Icc (-Real.pi) Real.pi,
          r * u (Complex.polarCoord.symm (r, θ))) := by
      apply continuous_parametric_integral_of_continuous
      · change Continuous (fun p : ℝ × ℝ ↦
          p.1 * u (Complex.polarCoord.symm p))
        have hpolar : Continuous (fun p : ℝ × ℝ ↦
            Complex.polarCoord.symm p) := by
          simp only [Complex.polarCoord_symm_apply]
          fun_prop
        exact continuous_fst.mul (hu.comp hpolar)
      · exact isCompact_Icc
    exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact measurableSet_Ioc
  · intro r hr
    rw [← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc]
    rw [MeasureTheory.integral_const_mul]
    rw [angular_integral_eq_circleAverage]
    have hr0 : 0 ≤ r := hr.1.le
    have hpi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
    calc
      2 * Real.pi * r * u 0 = (2 * Real.pi * r) * u 0 := by ring
      _ ≤ (2 * Real.pi * r) * Real.circleAverage u 0 r :=
        mul_le_mul_of_nonneg_left (hsub r hr) (mul_nonneg hpi hr0)
      _ = r * (2 * Real.pi * Real.circleAverage u 0 r) := by ring

private lemma diskIntegral_add_center (u : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    ∫ t in closedBall (0 : ℂ) R, u (t + c) =
      ∫ z in closedBall c R, u z := by
  have hfun : (closedBall (0 : ℂ) R).indicator (fun t ↦ u (t + c)) =
      fun t ↦ (closedBall c R).indicator u (t + c) := by
    funext t
    by_cases ht : t ∈ closedBall (0 : ℂ) R
    · have htc : t + c ∈ closedBall c R := by
        simpa [mem_closedBall, dist_eq_norm] using ht
      simp [ht, htc]
    · have htc : t + c ∉ closedBall c R := by
        simpa [mem_closedBall, dist_eq_norm] using ht
      simp [ht, htc]
  calc
    _ = ∫ t, (closedBall (0 : ℂ) R).indicator (fun x ↦ u (x + c)) t := by
      rw [MeasureTheory.integral_indicator measurableSet_closedBall]
    _ = ∫ t, (closedBall c R).indicator u (t + c) := by rw [hfun]
    _ = ∫ z, (closedBall c R).indicator u z :=
      MeasureTheory.integral_add_right_eq_self _ c
    _ = _ := MeasureTheory.integral_indicator measurableSet_closedBall

private lemma disk_submean {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : ∀ r ∈ Ioc 0 R, u c ≤ Real.circleAverage u c r) :
    (volume (closedBall c R)).toReal * u c ≤
      ∫ z in closedBall c R, u z := by
  let v : ℂ → ℝ := fun t ↦ u (t + c)
  have hv : Continuous v := hu.comp (continuous_id.add continuous_const)
  have hvsub : ∀ r ∈ Ioc 0 R, v 0 ≤ Real.circleAverage v 0 r := by
    intro r hr
    simpa [v, Real.circleAverage_map_add_const] using hsub r hr
  have h := disk_submean_zero hv hR hvsub
  rw [diskIntegral_add_center u c R] at h
  simpa [v, Complex.volume_closedBall] using h

/-- The iterated solid-polydisc integral over equal coordinate radii. -/
noncomputable def hartogsPolydiscIntegral : {n : ℕ} →
    ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ → ℝ
  | 0, u, c, _ => u c
  | _n + 1, u, c, R =>
      ∫ z in closedBall (c 0) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) (c ∘ Fin.succ) R

@[simp]
private lemma hartogsPolydiscIntegral_zero
    (u : (Fin 0 → ℂ) → ℝ) (c : Fin 0 → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R = u c := rfl

private lemma hartogsPolydiscIntegral_succ {n : ℕ}
    (u : (Fin (n + 1) → ℂ) → ℝ) (c : Fin (n + 1) → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R =
      ∫ z in closedBall (c 0) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) (c ∘ Fin.succ) R := rfl

private lemma hartogsPolydiscIntegral_succ_add {n : ℕ}
    (u : (Fin (n + 1) → ℂ) → ℝ) (c : Fin (n + 1) → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R =
      ∫ t in closedBall (0 : ℂ) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons (t + c 0) y))
          (c ∘ Fin.succ) R := by
  rw [hartogsPolydiscIntegral_succ]
  exact (diskIntegral_add_center
    (fun z ↦ hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y))
      (c ∘ Fin.succ) R) (c 0) R).symm

private theorem continuous_hartogsPolydiscIntegral_param
    {n : ℕ} {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {u : X → (Fin n → ℂ) → ℝ}
    (hu : Continuous (Function.uncurry u))
    {c : X → Fin n → ℂ} (hc : Continuous c) (R : ℝ) :
    Continuous (fun x ↦ hartogsPolydiscIntegral (u x) (c x) R) := by
  induction n generalizing X with
  | zero =>
      change Continuous (fun x ↦ u x (c x))
      exact hu.comp (continuous_id.prodMk hc)
  | succ n ih =>
      simp_rw [hartogsPolydiscIntegral_succ_add]
      apply continuous_parametric_integral_of_continuous
      · change Continuous (Function.uncurry fun x t ↦
          hartogsPolydiscIntegral
            (fun y ↦ u x (Fin.cons (t + c x 0) y)) (c x ∘ Fin.succ) R)
        apply ih
        · change Continuous (fun p : (X × ℂ) × (Fin n → ℂ) ↦
            u p.1.1 (Fin.cons (p.1.2 + c p.1.1 0) p.2))
          have hvec : Continuous (fun p : (X × ℂ) × (Fin n → ℂ) ↦
              (Fin.cons (p.1.2 + c p.1.1 0) p.2 : Fin (n + 1) → ℂ)) := by
            apply continuous_pi
            intro i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simp only [Fin.cons_zero]
              fun_prop
            · simp only [Fin.cons_succ]
              fun_prop
          exact hu.comp ((continuous_fst.comp continuous_fst).prodMk hvec)
        · change Continuous (fun p : X × ℂ ↦ c p.1 ∘ Fin.succ)
          fun_prop
      · exact isCompact_closedBall (0 : ℂ) R

/-- Iterating the circle sub-mean inequality gives the corresponding inequality for the
solid polydisc average. -/
theorem hartogsPolydisc_submean
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hcircle : ∀ x ∈ closedBall c R, ∀ (i : Fin n) r, r ∈ Ioc 0 R →
      u x ≤ Real.circleAverage (fun z ↦ u (Function.update x i z)) (x i) r) :
    (volume (closedBall (0 : ℂ) R)).toReal ^ n * u c ≤
      hartogsPolydiscIntegral u c R := by
  induction n with
  | zero => simp
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      let A : ℝ := (volume (closedBall (0 : ℂ) R)).toReal ^ n
      let g : ℂ → ℝ := fun z ↦ A * u (Fin.cons z c')
      have hA : 0 ≤ A := pow_nonneg ENNReal.toReal_nonneg _
      have hg : Continuous g := by
        apply continuous_const.mul
        apply hu.comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [Fin.cons_zero]
          change Continuous (id : ℂ → ℂ)
          exact continuous_id
        · simp only [Fin.cons_succ]
          exact continuous_const
      have hgsub : ∀ r ∈ Ioc 0 R,
          g (c 0) ≤ Real.circleAverage g (c 0) r := by
        intro r hr
        have hc_cons : Fin.cons (c 0) c' = c := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
        have hslice : (fun z ↦ u (Function.update c 0 z)) =
            fun z ↦ u (Fin.cons z c') := by
          funext z
          congr 1
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
        have h := hcircle c (by simp [hR.le]) 0 r hr
        rw [hslice] at h
        dsimp [g]
        rw [hc_cons]
        rw [show (fun z ↦ A * u (Fin.cons z c')) =
          A • (fun z ↦ u (Fin.cons z c')) by rfl]
        rw [Real.circleAverage_smul]
        exact mul_le_mul_of_nonneg_left h hA
      have hdisc := disk_submean hg hR hgsub
      have hmono :
          (∫ z in closedBall (c 0) R, g z) ≤
            ∫ z in closedBall (c 0) R,
              hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R := by
        apply MeasureTheory.setIntegral_mono_on
        · exact hg.continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
        · have hp : Continuous (fun z ↦
              hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R) := by
            apply continuous_hartogsPolydiscIntegral_param
            · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
                u (Fin.cons p.1 p.2))
              apply hu.comp
              apply continuous_pi
              intro i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · simp only [Fin.cons_zero]
                change Continuous (Prod.fst : ℂ × (Fin n → ℂ) → ℂ)
                exact continuous_fst
              · simp only [Fin.cons_succ]
                change Continuous ((fun y : Fin n → ℂ ↦ y j) ∘ Prod.snd)
                exact (continuous_apply j).comp continuous_snd
            · exact continuous_const
          exact hp.continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
        · exact measurableSet_closedBall
        · intro z hz
          change A * u (Fin.cons z c') ≤
            hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R
          dsimp [A]
          apply ih (u := fun y ↦ u (Fin.cons z y)) (c := c')
          · change Continuous (fun y ↦ u (Fin.cons z y))
            apply hu.comp
            fun_prop
          · intro y hy i r hr
            have hc_cons' : Fin.cons (c 0) c' = c := by
              funext j
              refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [c']
            have hxy : Fin.cons z y ∈ closedBall c R := by
              rw [← hc_cons']
              rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
              intro j
              refine Fin.cases ?_ (fun k ↦ ?_) j
              · simpa [Metric.mem_closedBall] using hz
              · have hy' :=
                  (dist_pi_le_iff hR.le).1
                    (Metric.mem_closedBall.1 hy) k
                simpa using hy'
            have h := hcircle (Fin.cons z y) hxy i.succ r hr
            simpa only [Fin.cons_succ, Fin.cons_update] using h
      rw [hartogsPolydiscIntegral_succ]
      have hc_cons : Fin.cons (c 0) (c ∘ Fin.succ) = c := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      have hlhs :
          (volume (closedBall (0 : ℂ) R)).toReal ^ (n + 1) * u c =
            (volume (closedBall (c 0) R)).toReal * g (c 0) := by
        dsimp [g, A, c']
        rw [hc_cons]
        simp only [Complex.volume_closedBall]
        ring
      rw [hlhs]
      exact hdisc.trans hmono

private lemma fin_cons_mem_closedBall {n : ℕ} {z c₀ : ℂ}
    {y c' : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ closedBall c₀ R) (hy : y ∈ closedBall c' R) :
    (Fin.cons z y : Fin (n + 1) → ℂ) ∈
      closedBall (Fin.cons c₀ c' : Fin (n + 1) → ℂ) R := by
  have hy' : ∀ j, dist (y j) (c' j) ≤ R :=
    (dist_pi_le_iff hR).1 (Metric.mem_closedBall.1 hy)
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa [Metric.mem_closedBall] using hz
  · simpa using hy' j

private theorem hartogsPolydiscIntegral_nonneg
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : ∀ x, 0 ≤ u x)
    (c : Fin n → ℂ) (R : ℝ) :
    0 ≤ hartogsPolydiscIntegral u c R := by
  induction n with
  | zero => exact hu _
  | succ n ih =>
      rw [hartogsPolydiscIntegral_succ]
      exact MeasureTheory.integral_nonneg fun z ↦
        ih (u := fun y ↦ u (Fin.cons z y)) (fun y ↦ hu _)
          (c ∘ Fin.succ)

private theorem hartogsPolydiscIntegral_le
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    {c : Fin n → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hC : ∀ x ∈ closedBall c R, u x ≤ C) :
    hartogsPolydiscIntegral u c R ≤
      (volume (closedBall (0 : ℂ) R)).toReal ^ n * C := by
  induction n with
  | zero =>
      simpa using hC c (by simp [hR])
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      have hc_cons : Fin.cons (c 0) c' = c := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
      rw [hartogsPolydiscIntegral_succ]
      calc
        _ ≤ ∫ _z in closedBall (c 0) R,
              (volume (closedBall (0 : ℂ) R)).toReal ^ n * C := by
          apply MeasureTheory.setIntegral_mono_on
          · have hp : Continuous (fun z ↦
                hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R) := by
              apply continuous_hartogsPolydiscIntegral_param
              · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
                  u (Fin.cons p.1 p.2))
                apply hu.comp
                fun_prop
              · exact continuous_const
            exact hp.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact integrableOn_const measure_closedBall_lt_top.ne
          · exact measurableSet_closedBall
          · intro z hz
            apply ih
            · change Continuous (fun y ↦ u (Fin.cons z y))
              apply hu.comp
              fun_prop
            · intro y hy
              apply hC
              rw [← hc_cons]
              exact fin_cons_mem_closedBall hR hz hy
        _ = (volume (closedBall (0 : ℂ) R)).toReal ^ (n + 1) * C := by
          rw [MeasureTheory.setIntegral_const]
          simp only [smul_eq_mul, measureReal_def, Complex.volume_closedBall]
          ring

private theorem tendsto_hartogsPolydiscIntegral_zero
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    (hu : ∀ k, Continuous (u k))
    (hnonneg : ∀ k x, 0 ≤ u k x) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k x, u k x ≤ C) {c : Fin n → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0)) :
    Tendsto (fun k ↦ hartogsPolydiscIntegral (u k) c R)
      atTop (nhds 0) := by
  induction n with
  | zero =>
      simpa using hlim c (by simp [hR])
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      let B : ℝ := (volume (closedBall (0 : ℂ) R)).toReal ^ n * C
      let F : ℕ → ℂ → ℝ := fun k z ↦
        hartogsPolydiscIntegral (fun y ↦ u k (Fin.cons z y)) c' R
      have hFcont : ∀ k, Continuous (F k) := by
        intro k
        dsimp [F]
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u k (Fin.cons p.1 p.2))
          apply (hu k).comp
          fun_prop
        · exact continuous_const
      have hB : 0 ≤ B :=
        mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _) hC
      have hFB : ∀ k z, F k z ≤ B := by
        intro k z
        dsimp [F, B]
        apply hartogsPolydiscIntegral_le
        · change Continuous (fun y ↦ u k (Fin.cons z y))
          apply (hu k).comp
          fun_prop
        · exact hR
        · intro y _hy
          exact hbound k _
      have hF0 : ∀ k z, 0 ≤ F k z := by
        intro k z
        exact hartogsPolydiscIntegral_nonneg
          (u := fun y ↦ u k (Fin.cons z y)) (fun y ↦ hnonneg k _)
            c' R
      have hFtendsto : ∀ z ∈ closedBall (c 0) R,
          Tendsto (fun k ↦ F k z) atTop (nhds 0) := by
        intro z hz
        apply ih
        · intro k
          change Continuous (fun y ↦ u k (Fin.cons z y))
          apply (hu k).comp
          fun_prop
        · intro k y
          exact hnonneg k _
        · intro k y
          exact hbound k _
        · intro y hy
          apply hlim
          have hc_cons : Fin.cons (c 0) c' = c := by
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
          rw [← hc_cons]
          exact fin_cons_mem_closedBall hR hz hy
      have ht := MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (closedBall (c 0) R)) (fun _ : ℂ ↦ B)
        (fun k ↦ (hFcont k).aestronglyMeasurable)
        (integrableOn_const measure_closedBall_lt_top.ne)
        (fun k ↦ Filter.Eventually.of_forall fun z ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 k z)]
          exact hFB k z)
        (ae_restrict_of_forall_mem measurableSet_closedBall
          fun z hz ↦ hFtendsto z hz)
      simpa [F, hartogsPolydiscIntegral_succ] using ht

private theorem hartogsPolydiscIntegral_mono_center
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) {c c' : Fin n → ℂ} {R S : ℝ}
    (hsub : ∀ i, closedBall (c' i) S ⊆ closedBall (c i) R) :
    hartogsPolydiscIntegral u c' S ≤ hartogsPolydiscIntegral u c R := by
  induction n with
  | zero =>
      change u c' ≤ u c
      rw [Subsingleton.elim c' c]
  | succ n ih =>
      let d : Fin n → ℂ := c ∘ Fin.succ
      let d' : Fin n → ℂ := c' ∘ Fin.succ
      rw [hartogsPolydiscIntegral_succ, hartogsPolydiscIntegral_succ]
      let F : ℂ → ℝ := fun z ↦
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) d R
      let F' : ℂ → ℝ := fun z ↦
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) d' S
      have hF : Continuous F := by
        dsimp [F]
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u (Fin.cons p.1 p.2))
          apply hu.comp
          fun_prop
        · exact continuous_const
      have hF' : Continuous F' := by
        dsimp [F']
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u (Fin.cons p.1 p.2))
          apply hu.comp
          fun_prop
        · exact continuous_const
      calc
        (∫ z in closedBall (c' 0) S, F' z) ≤
            ∫ z in closedBall (c' 0) S, F z := by
          apply MeasureTheory.setIntegral_mono_on
          · exact hF'.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact hF.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact measurableSet_closedBall
          · intro z _hz
            apply ih
            · change Continuous (fun y ↦ u (Fin.cons z y))
              apply hu.comp
              fun_prop
            · intro y
              exact hu0 _
            · intro i
              exact hsub i.succ
        _ ≤ ∫ z in closedBall (c 0) R, F z := by
          apply MeasureTheory.setIntegral_mono_set
          · exact hF.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact Filter.Eventually.of_forall fun z ↦
              hartogsPolydiscIntegral_nonneg
                (u := fun y ↦ u (Fin.cons z y)) (fun y ↦ hu0 _) d R
          · exact Filter.Eventually.of_forall fun z hz ↦ hsub 0 hz

private theorem hartogs_eventually_uniform_of_submean_global
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    {c : Fin n → ℂ} {R C : ℝ}
    (hR : 0 < R) (hu : ∀ k, Continuous (u k))
    (hu0 : ∀ k x, 0 ≤ u k x) (hC : 0 ≤ C)
    (hub : ∀ k x, u k x ≤ C)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0))
    (hcircle : ∀ k x (i : Fin n) r, 0 < r →
      (∀ z ∈ closedBall (x i) r,
        Function.update x i z ∈ closedBall c R) →
      u k x ≤
        Real.circleAverage (fun z ↦ u k (Function.update x i z)) (x i) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ closedBall c (R / 4), u k x ≤ ε := by
  let S : ℝ := R / 4
  let V : ℝ := (volume (closedBall (0 : ℂ) S)).toReal ^ n
  have hS : 0 < S := div_pos hR (by norm_num)
  have hvol : 0 < (volume (closedBall (0 : ℂ) S)).toReal := by
    rw [Complex.volume_closedBall]
    simpa [ENNReal.toReal_mul, hS.le] using
      mul_pos (pow_pos hS 2) Real.pi_pos
  have hV : 0 < V := pow_pos hvol _
  have ht : Tendsto
      (fun k ↦ hartogsPolydiscIntegral (u k) c R) atTop (nhds 0) :=
    tendsto_hartogsPolydiscIntegral_zero hu hu0 hC hub hR.le hlim
  have hevent : ∀ᶠ k in atTop,
      hartogsPolydiscIntegral (u k) c R < V * ε :=
    (tendsto_order.1 ht).2 _ (mul_pos hV hε)
  filter_upwards [hevent] with k hk
  intro x hx
  have hsubsets : ∀ i,
      closedBall (x i) S ⊆ closedBall (c i) R := by
    intro i z hz
    rw [Metric.mem_closedBall] at hx hz ⊢
    have hxi : dist (x i) (c i) ≤ S :=
      (dist_pi_le_iff hS.le).1 hx i
    calc
      dist z (c i) ≤ dist z (x i) + dist (x i) (c i) :=
        dist_triangle _ _ _
      _ ≤ S + S := add_le_add hz hxi
      _ ≤ R := by dsimp [S]; linarith
  have hmean : V * u k x ≤ hartogsPolydiscIntegral (u k) x S := by
    dsimp [V]
    apply hartogsPolydisc_submean (hu k) hS
    intro y hy i r hr
    apply hcircle k y i r hr.1
    intro z hz
    rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      have hyi : dist (y i) (x i) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hy) i
      have hxi : dist (x i) (c i) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hx) i
      calc
        dist z (c i) ≤ dist z (y i) + dist (y i) (c i) :=
          dist_triangle _ _ _
        _ ≤ r + (dist (y i) (x i) + dist (x i) (c i)) := by
          gcongr
          · simpa [Metric.mem_closedBall] using hz
          · exact dist_triangle _ _ _
        _ ≤ S + (S + S) := by gcongr; exact hr.2
        _ ≤ R := by dsimp [S]; linarith
    · rw [Function.update_of_ne hji]
      have hyj : dist (y j) (x j) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hy) j
      have hxj : dist (x j) (c j) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hx) j
      exact (dist_triangle _ _ _).trans
        ((add_le_add hyj hxj).trans (by dsimp [S]; linarith))
  have hnested : hartogsPolydiscIntegral (u k) x S ≤
      hartogsPolydiscIntegral (u k) c R :=
    hartogsPolydiscIntegral_mono_center (hu k) (hu0 k) hsubsets
  have hlt : V * u k x < V * ε :=
    (hmean.trans hnested).trans_lt hk
  exact (lt_of_mul_lt_mul_left hlt hV.le).le

/-- Hartogs' lemma: locally bounded nonnegative sub-mean functions that converge pointwise to
zero converge uniformly on a smaller concentric polydisc. -/
theorem hartogs_eventually_uniform_of_submean
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    {c : Fin n → ℂ} {R C : ℝ}
    (hR : 0 < R)
    (hu : ∀ k, ContinuousOn (u k) (closedBall c R))
    (hu0 : ∀ k x, x ∈ closedBall c R → 0 ≤ u k x)
    (hC : 0 ≤ C)
    (hub : ∀ k x, x ∈ closedBall c R → u k x ≤ C)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0))
    (hcircle : ∀ k x, x ∈ closedBall c R → ∀ (i : Fin n) r, 0 < r →
      (∀ z ∈ closedBall (x i) r,
        Function.update x i z ∈ closedBall c R) →
      u k x ≤
        Real.circleAverage (fun z ↦ u k (Function.update x i z)) (x i) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ closedBall c (R / 4), u k x ≤ ε := by
  let K : Set (Fin n → ℂ) := closedBall c R
  let uk : ℕ → C(K, ℝ) := fun k ↦
    ⟨K.domRestrict (u k), (hu k).domRestrict⟩
  have hext (k : ℕ) : ∃ v : C(Fin n → ℂ, ℝ),
      (∀ x, v x ∈ Icc 0 C) ∧ ContinuousMap.restrict K v = uk k := by
    apply (uk k).exists_restrict_eq_forall_mem_of_closed
    · intro x
      exact ⟨hu0 k x x.property, hub k x x.property⟩
    · exact nonempty_Icc.2 hC
    · exact isClosed_closedBall
  choose v hv_range hv_restrict using hext
  let vfun : ℕ → (Fin n → ℂ) → ℝ := fun k ↦ v k
  have hv_eq (k : ℕ) (x : Fin n → ℂ) (hx : x ∈ closedBall c R) :
      vfun k x = u k x := by
    have h := DFunLike.congr_fun (hv_restrict k) ⟨x, hx⟩
    simpa [vfun, uk, K] using h
  have hglobal := hartogs_eventually_uniform_of_submean_global
    (u := vfun) hR
    (fun k ↦ (v k).continuous)
    (fun k x ↦ (hv_range k x).1)
    hC
    (fun k x ↦ (hv_range k x).2)
    (fun x hx ↦ by
      simpa only [hv_eq _ x hx] using hlim x hx)
    (fun k x i r hr hincl ↦ by
      have hx : x ∈ closedBall c R := by
        have hxc := hincl (x i) (by simp [hr.le])
        simpa using hxc
      rw [hv_eq k x hx]
      calc
        u k x ≤
            Real.circleAverage
              (fun z ↦ u k (Function.update x i z)) (x i) r :=
          hcircle k x hx i r hr hincl
        _ = Real.circleAverage
              (fun z ↦ vfun k (Function.update x i z)) (x i) r := by
          apply Real.circleAverage_congr_codiscreteWithin _ hr.ne'
          filter_upwards [Filter.self_mem_codiscreteWithin
            (sphere (x i) |r|)] with z hz
          apply (hv_eq k (Function.update x i z) ?_).symm
          apply hincl z
          simpa [abs_of_pos hr] using sphere_subset_closedBall hz)
    hε
  filter_upwards [hglobal] with k hk
  intro x hx
  rw [← hv_eq k x (by
    exact mem_closedBall'.2 ((mem_closedBall'.1 hx).trans (by linarith)))]
  exact hk x hx

private theorem hartogs_pi_all {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ (x : Fin n → ℂ) (i : Fin n),
      Differentiable ℂ (fun z : ℂ ↦ f (Function.update x i z))) :
    Differentiable ℂ f := by
  induction n with
  | zero => exact differentiable_of_subsingleton
  | succ n ih =>
      intro x₀
      let z₀ : Fin n → ℂ := x₀ ∘ Fin.succ
      let w₀ : ℂ := x₀ 0
      let F : (Fin n → ℂ) → ℂ → ℂ := fun z w ↦ f (Fin.cons w z)
      have hx₀ : Fin.cons w₀ z₀ = x₀ := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [w₀, z₀]
      have hF₁ (w : ℂ) : Differentiable ℂ (fun z ↦ F z w) := by
        apply ih
        intro x i
        have h := hf (Fin.cons w x) i.succ
        convert h using 1
        funext t
        simp only [F, Fin.cons_update]
      have hF₂ (z : Fin n → ℂ) : Differentiable ℂ (F z) := by
        have h := hf (Fin.cons 0 z) 0
        convert h using 1
        funext t
        simp only [F, Fin.update_cons_zero]
      let K : Set (Fin n → ℂ) := closedBall z₀ 8
      obtain ⟨m, hm⟩ := hartogs_exists_interior_uniform_bound
        (f := fun w z ↦ F z w) (K := K)
        (isCompact_closedBall z₀ 8)
        (fun z _hz ↦ (hF₂ z).continuous)
        (fun w ↦ (hF₁ w).continuous.continuousOn)
      rcases hm with ⟨w₂, hw₂⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w₂ hw₂
      let B : ℝ := r / 2
      have hB : 0 < B := div_pos hr (by norm_num)
      have hbound : ∀ z ∈ closedBall z₀ 8,
          ∀ w ∈ closedBall w₂ B, ‖F z w‖ ≤ (m : ℝ) := by
        intro z hz w hw
        have hwball : w ∈ ball w₂ r := by
          rw [mem_ball]
          exact (mem_closedBall.1 hw).trans_lt (by dsimp [B]; linarith)
        exact interior_subset (hball hwball) z hz
      let s : ℝ := B / 2
      have hs : 0 < s := div_pos hB (by norm_num)
      let p : (Fin n → ℂ) → FormalMultilinearSeries ℂ ℂ ℂ :=
        fun z ↦ cauchyPowerSeries (F z) w₂ s
      let a : ℕ → (Fin n → ℂ) → ℂ := fun k z ↦ (p z).coeff k
      have ha_diff (k : ℕ) : DifferentiableOn ℂ (a k) (ball z₀ 4) := by
        convert
          differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
            (f := F) (z₀ := z₀) (w₀ := w₂) (A := 8) (B := B)
            (M := (m : ℝ)) (by norm_num) hB hF₁ hF₂ hbound k using 1
        · rfl
        · norm_num
      have ha_bound (k : ℕ) (z : Fin n → ℂ) (hz : z ∈ closedBall z₀ 2) :
          ‖a k z‖ ≤ (m : ℝ) * s⁻¹ ^ k := by
        apply norm_cauchyCoefficient_le hs (hF₂ z) _ k
        intro w hw
        apply hbound z
        · exact mem_closedBall'.2 ((mem_closedBall'.1 hz).trans (by norm_num))
        · rw [mem_closedBall]
          have hw' := mem_sphere.1 hw
          rw [hw']
          dsimp [s]
          linarith
      let W : ℝ := 4 * (‖w₀ - w₂‖ + 1)
      have hW : 0 < W := mul_pos (by norm_num) (by positivity)
      have hterm (z : Fin n → ℂ) :
          Tendsto (fun k ↦ ‖a k z‖ * W ^ k) atTop (nhds 0) := by
        let q : NNReal := ⟨s, hs.le⟩
        have hqs : (q : ℝ) = s := rfl
        have hq : 0 < q := by
          rw [← NNReal.coe_pos]
          rw [hqs]
          exact hs
        have hfps := (hF₂ z).hasFPowerSeriesOnBall w₂ hq
        have hsum := hfps.hasSum (y := (W : ℂ)) (by simp)
        have ht := hsum.summable.tendsto_atTop_zero.norm
        rw [hqs] at ht
        simpa [a, p,
          FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          norm_smul, abs_of_pos hW, mul_comm] using ht
      let u : ℕ → (Fin n → ℂ) → ℝ := fun k z ↦
        ((k + 1 : ℕ) : ℝ)⁻¹ *
          Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1))
      have hu_cont (k : ℕ) : ContinuousOn (u k) (closedBall z₀ 2) := by
        apply ContinuousOn.mul continuousOn_const
        apply Real.continuous_posLog.comp_continuousOn
        apply ContinuousOn.mul
        · apply (ha_diff (k + 1)).continuousOn.norm.mono
          intro z hz
          exact mem_ball'.2 ((mem_closedBall'.1 hz).trans_lt (by norm_num))
        · exact continuousOn_const
      have hu0 (k : ℕ) (z : Fin n → ℂ) : 0 ≤ u k z :=
        mul_nonneg (inv_nonneg.mpr (by positivity)) Real.posLog_nonneg
      let Q : ℝ := s⁻¹ * W
      have hQ : 0 < Q := mul_pos (inv_pos.mpr hs) hW
      let C : ℝ := Real.posLog (m : ℝ) + Real.posLog Q
      have hC : 0 ≤ C := add_nonneg Real.posLog_nonneg Real.posLog_nonneg
      have hu_bound (k : ℕ) (z : Fin n → ℂ)
          (hz : z ∈ closedBall z₀ 2) : u k z ≤ C := by
        let j : ℕ := k + 1
        have hjpos : (0 : ℝ) < j := by
          exact_mod_cast Nat.succ_pos k
        have hterm_bound : ‖a j z‖ * W ^ j ≤ (m : ℝ) * Q ^ j := by
          calc
            ‖a j z‖ * W ^ j ≤ ((m : ℝ) * s⁻¹ ^ j) * W ^ j :=
              mul_le_mul_of_nonneg_right (ha_bound j z hz) (pow_nonneg hW.le _)
            _ = (m : ℝ) * (s⁻¹ ^ j * W ^ j) := by ring
            _ = (m : ℝ) * (s⁻¹ * W) ^ j :=
              congrArg (fun t : ℝ ↦ (m : ℝ) * t) (mul_pow s⁻¹ W j).symm
            _ = (m : ℝ) * Q ^ j := by rfl
        have hposlog :
            Real.posLog (‖a j z‖ * W ^ j) ≤
              Real.posLog (m : ℝ) + (j : ℝ) * Real.posLog Q := by
          calc
            Real.posLog (‖a j z‖ * W ^ j) ≤
                Real.posLog ((m : ℝ) * Q ^ j) :=
              Real.posLog_le_posLog
                (by
                  have : 0 ≤ ‖a j z‖ * W ^ j :=
                    mul_nonneg (norm_nonneg _) (pow_nonneg hW.le _)
                  linarith)
                hterm_bound
            _ ≤ Real.posLog (m : ℝ) + Real.posLog (Q ^ j) :=
              Real.posLog_mul
            _ = Real.posLog (m : ℝ) +
                (j : ℝ) * Real.posLog Q := by rw [Real.posLog_pow]
        dsimp [u, C]
        change (j : ℝ)⁻¹ * Real.posLog (‖a j z‖ * W ^ j) ≤ _
        calc
          (j : ℝ)⁻¹ * Real.posLog (‖a j z‖ * W ^ j) ≤
              (j : ℝ)⁻¹ *
                (Real.posLog (m : ℝ) + (j : ℝ) * Real.posLog Q) :=
            mul_le_mul_of_nonneg_left hposlog (inv_nonneg.mpr hjpos.le)
          _ = (j : ℝ)⁻¹ * Real.posLog (m : ℝ) + Real.posLog Q := by
            field_simp [hjpos.ne']
          _ ≤ Real.posLog (m : ℝ) + Real.posLog Q := by
            have hjone : (1 : ℝ) ≤ j := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
            have hmul : (j : ℝ)⁻¹ * Real.posLog (m : ℝ) ≤
                Real.posLog (m : ℝ) := by
              calc
                _ ≤ 1 * Real.posLog (m : ℝ) :=
                  mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hjone)
                    Real.posLog_nonneg
                _ = _ := one_mul _
            exact add_le_add_left hmul _
      have hu_lim (z : Fin n → ℂ) :
          Tendsto (fun k ↦ u k z) atTop (nhds 0) := by
        have ht : Tendsto
            (fun k ↦ ‖a (k + 1) z‖ * W ^ (k + 1)) atTop (nhds 0) := by
          simpa [Nat.add_comm] using
            (Filter.tendsto_add_atTop_iff_nat 1).2 (hterm z)
        have hpl : Tendsto
            (fun k ↦ Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)))
            atTop (nhds 0) := by
          have hcomp : Tendsto
              (Real.posLog ∘ fun k ↦ ‖a (k + 1) z‖ * W ^ (k + 1))
              atTop (nhds 0) := by
            simpa only [Real.posLog_zero] using
              Real.continuous_posLog.continuousAt.tendsto.comp ht
          exact hcomp.congr' (Eventually.of_forall fun _ ↦ rfl)
        apply squeeze_zero (fun k ↦ hu0 k z) _ hpl
        intro k
        have hjone : (1 : ℝ) ≤ (k + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        dsimp [u]
        calc
          ((k + 1 : ℕ) : ℝ)⁻¹ *
              Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)) ≤
              1 * Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (inv_le_one_of_one_le₀ hjone) Real.posLog_nonneg
          _ = _ := one_mul _
      have hu_circle (k : ℕ) (x : Fin n → ℂ)
          (hx : x ∈ closedBall z₀ 2) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
          (hincl : ∀ z ∈ closedBall (x i) ρ,
            Function.update x i z ∈ closedBall z₀ 2) :
          u k x ≤ Real.circleAverage
            (fun z ↦ u k (Function.update x i z)) (x i) ρ := by
        let j : ℕ := k + 1
        let upd : ℂ → Fin n → ℂ := fun z ↦ Function.update x i z
        have hupd : Differentiable ℂ upd := by
          rw [differentiable_pi]
          intro l
          by_cases hli : l = i
          · subst l
            simp [upd, Function.update_self]
          · have heq : (fun z ↦ upd z l) = fun _ : ℂ ↦ x l := by
              funext z
              simp [upd, Function.update_of_ne hli]
            rw [heq]
            exact differentiable_const _
        let V : Set ℂ := upd ⁻¹' ball z₀ 4
        have hVopen : IsOpen V := isOpen_ball.preimage hupd.continuous
        let g : ℂ → ℂ := fun z ↦ a j (upd z) * (W : ℂ) ^ j
        have hgdiff : DifferentiableOn ℂ g V := by
          intro z hz
          have ha_at : DifferentiableAt ℂ (a j) (upd z) :=
            (ha_diff j (upd z) hz).differentiableAt
              (isOpen_ball.mem_nhds hz)
          exact ((ha_at.comp z (hupd z)).mul_const _).differentiableWithinAt
        have hclosed : closedBall (x i) ρ ⊆ V := by
          intro z hz
          exact mem_ball'.2
            ((mem_closedBall'.1 (hincl z hz)).trans_lt (by norm_num))
        have hganalytic : AnalyticOnNhd ℂ g (closedBall (x i) ρ) :=
          (hgdiff.analyticOnNhd hVopen).mono hclosed
        have hsub := hartogs_posLog_norm_le_circleAverage hρ hganalytic
        have hsub' : Real.posLog (‖a j x‖ * W ^ j) ≤
            Real.circleAverage
              (fun z ↦ Real.posLog (‖a j (Function.update x i z)‖ * W ^ j))
              (x i) ρ := by
          simpa [g, upd, j, norm_mul, norm_pow, abs_of_pos hW,
            Function.update_eq_self, mul_comm] using hsub
        dsimp [u]
        change (j : ℝ)⁻¹ * Real.posLog (‖a j x‖ * W ^ j) ≤ _
        calc
          (j : ℝ)⁻¹ * Real.posLog (‖a j x‖ * W ^ j) ≤
              (j : ℝ)⁻¹ * Real.circleAverage
                (fun z ↦ Real.posLog
                  (‖a j (Function.update x i z)‖ * W ^ j)) (x i) ρ :=
            mul_le_mul_of_nonneg_left hsub' (inv_nonneg.mpr (by positivity))
          _ = Real.circleAverage
              (fun z ↦ (j : ℝ)⁻¹ * Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) (x i) ρ := by
            rw [show (fun z ↦ (j : ℝ)⁻¹ * Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) =
              (j : ℝ)⁻¹ • (fun z ↦ Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) by rfl]
            rw [Real.circleAverage_smul]
            rfl
          _ = _ := by rfl
      have huniform := hartogs_eventually_uniform_of_submean
        (u := u) (c := z₀) (R := 2) (C := C) (by norm_num)
        hu_cont (fun k z _hz ↦ hu0 k z) hC hu_bound
        (fun z _hz ↦ hu_lim z) hu_circle
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      have huniform' : ∀ᶠ k in atTop,
          ∀ z ∈ closedBall z₀ (1 / 2 : ℝ), u k z ≤ Real.log 2 := by
        rw [show (2 : ℝ) / 4 = 1 / 2 by norm_num] at huniform
        exact huniform
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 huniform'
      have ha_tail (k : ℕ) (hk : N ≤ k) (z : Fin n → ℂ)
          (hz : z ∈ closedBall z₀ (1 / 2 : ℝ)) :
          ‖a (k + 1) z‖ ≤ (2 / W) ^ (k + 1) := by
        let j : ℕ := k + 1
        let t : ℝ := ‖a j z‖ * W ^ j
        have hjpos : (0 : ℝ) < j := by
          exact_mod_cast Nat.succ_pos k
        have ht0 : 0 ≤ t :=
          mul_nonneg (norm_nonneg _) (pow_nonneg hW.le _)
        have hu_le := hN k hk z hz
        have hpl : Real.posLog t ≤ (j : ℝ) * Real.log 2 := by
          apply (inv_mul_le_iff₀ hjpos).1
          simpa [u, j, t] using hu_le
        have ht2 : t ≤ (2 : ℝ) ^ j := by
          by_cases ht : t ≤ 1
          · exact ht.trans (one_le_pow₀ (by norm_num))
          · have htpos : 0 < t := lt_trans (by norm_num) (lt_of_not_ge ht)
            apply (Real.strictMonoOn_log.le_iff_le htpos
              (pow_pos (by norm_num : (0 : ℝ) < 2) j)).1
            rw [Real.log_pow]
            rw [Real.posLog_eq_log (by
              rw [abs_of_nonneg ht0]
              exact (lt_of_not_ge ht).le)] at hpl
            exact hpl
        rw [div_pow]
        apply (le_div_iff₀ (pow_pos hW _)).2
        simpa [t, j] using ht2
      have hp_sum (z : Fin n → ℂ) (w : ℂ) :
          HasSum (fun j ↦ (p z j) (fun _ ↦ w - w₂)) (F z w) := by
        let q : NNReal := ⟨s, hs.le⟩
        have hqs : (q : ℝ) = s := rfl
        have hq : 0 < q := by
          rw [← NNReal.coe_pos, hqs]
          exact hs
        have hfps := (hF₂ z).hasFPowerSeriesOnBall w₂ hq
        have hsum := hfps.hasSum (y := w - w₂) (by simp)
        rw [hqs] at hsum
        simpa [p] using hsum
      let head : ℕ → ℝ := fun j ↦
        if j ≤ N then (m : ℝ) * s⁻¹ ^ j * (W / 4) ^ j else 0
      let major : ℕ → ℝ := fun j ↦ head j + (1 / 2 : ℝ) ^ j
      have hhead_support : Function.HasFiniteSupport head := by
        apply (Set.finite_Iic N).subset
        intro j hj
        by_contra hle
        have hjn : ¬j ≤ N := by simpa only [mem_Iic] using hle
        exact hj (by simp only [head, ite_eq_right hjn])
      have hmajor : Summable major := by
        apply (summable_of_hasFiniteSupport hhead_support).add
        exact summable_geometric_of_norm_lt_one (by norm_num)
      have hlocal_bound : ∀ z ∈ closedBall z₀ (1 / 2 : ℝ),
          ∀ w ∈ closedBall w₀ 1, ‖F z w‖ ≤ ∑' j, major j := by
        intro z hz w hw
        apply (hp_sum z w).norm_le_of_bounded hmajor.hasSum
        intro j
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul,
          norm_pow]
        have hz2 : z ∈ closedBall z₀ 2 :=
          mem_closedBall'.2 ((mem_closedBall'.1 hz).trans (by norm_num))
        have hd : ‖w - w₂‖ ≤ W / 4 := by
          calc
            ‖w - w₂‖ ≤ ‖w - w₀‖ + ‖w₀ - w₂‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ 1 + ‖w₀ - w₂‖ := by
              gcongr
              simpa [mem_closedBall, dist_eq_norm] using hw
            _ = W / 4 := by dsimp [W]; ring
        by_cases hj : j ≤ N
        · calc
            ‖w - w₂‖ ^ j * ‖(p z).coeff j‖ ≤
                (W / 4) ^ j * ((m : ℝ) * s⁻¹ ^ j) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd _) (ha_bound j z hz2)
                (norm_nonneg _) (pow_nonneg (by positivity) _)
            _ = (m : ℝ) * s⁻¹ ^ j * (W / 4) ^ j := by ring
            _ ≤ major j := by
              dsimp [major, head]
              rw [ite_eq_left hj]
              exact le_add_of_nonneg_right (pow_nonneg (by norm_num) _)
        · have hj0 : j ≠ 0 := by
            intro hjzero
            subst j
            exact hj (Nat.zero_le _)
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hk : N ≤ k := by omega
          calc
            ‖w - w₂‖ ^ (k + 1) * ‖(p z).coeff (k + 1)‖ ≤
                (W / 4) ^ (k + 1) * (2 / W) ^ (k + 1) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd _)
                (ha_tail k hk z hz) (norm_nonneg _) (pow_nonneg (by positivity) _)
            _ = (1 / 2 : ℝ) ^ (k + 1) := by
              rw [← mul_pow]
              field_simp [hW.ne']
              norm_num
            _ ≤ major (k + 1) := by
              dsimp [major, head]
              rw [ite_eq_right (by omega : ¬ k + 1 ≤ N)]
              simp
      have hjoint : DifferentiableAt ℂ (Function.uncurry F) (z₀, w₀) :=
        differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
          isOpen_ball isOpen_ball hF₁ hF₂
          (fun z hz w hw ↦ hlocal_bound z (ball_subset_closedBall hz) w
            (ball_subset_closedBall hw))
          (by simp) (by simp)
      let split : (Fin (n + 1) → ℂ) → (Fin n → ℂ) × ℂ := fun x ↦
        (x ∘ Fin.succ, x 0)
      have hsplit : Differentiable ℂ split := by
        dsimp [split]
        fun_prop
      have hsplit₀ : split x₀ = (z₀, w₀) := by rfl
      have hjoint' : DifferentiableAt ℂ (Function.uncurry F) (split x₀) := by
        rw [hsplit₀]
        exact hjoint
      have hcomp := hjoint'.comp x₀ (hsplit x₀)
      convert hcomp using 1
      funext x
      dsimp [Function.uncurry, F, split]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

private theorem hartogs_euclidean_of_pi {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : Differentiable ℂ (fun x : Fin n → ℂ => f (WithLp.toLp 2 x))) :
    Differentiable ℂ f := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    EuclideanSpace.equiv (Fin n) ℂ
  have he : Differentiable ℂ (e : EuclideanSpace ℂ (Fin n) → Fin n → ℂ) :=
    e.toContinuousLinearMap.differentiable
  have hf' : Differentiable ℂ (fun x : Fin n → ℂ => f (e.symm x)) := by
    simpa [e] using hf
  have hcomp := hf'.comp he
  convert hcomp using 1
  funext x
  change f x = f (e.symm (e x))
  rw [e.symm_apply_apply]

/--
If `f : ℂⁿ → ℂ` is entire in each variable separately via `Function.update` slices, then `f` is
jointly `Differentiable ℂ` on `ℂⁿ`. Source: Hartogs separate analyticity (Osgood–Hartogs); see
Hörmander; Lean is scalar-valued entire separately holomorphic via Function.update slices implies
jointly Differentiable ℂ, finite-dimensional ℂⁿ specialization.

Proves `Wanted` entry `hartogs_separate_analyticity`.

Proof: induction on the number of variables. Baire category gives a polydisc where `f` is
bounded, where Osgood's lemma makes it holomorphic; Hartogs' lemma on sub-mean-value functions
then makes the Cauchy expansion in the last variable converge locally uniformly.
-/
theorem hartogs_separate_analyticity
    {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n),
      Differentiable ℂ (fun z : ℂ =>
        f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z)))) :
    Differentiable ℂ f := by
  apply hartogs_euclidean_of_pi
  apply hartogs_pi_all
  intro x i
  simpa using hf (WithLp.toLp 2 x) i

end MathlibExt.Analysis.Complex.HartogsWanted
