/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Ball averages of harmonic functions

A twice continuously differentiable function is harmonic on an open set exactly when its
average over each positive-radius closed ball in the set equals its value at the centre.
-/

public section

namespace MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

open InnerProductSpace Metric MeasureTheory Set Filter Laplacian
open scoped RealInnerProductSpace Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E]

/-- A weight supported on the unit ball whose negative gradient in the ball is the identity. -/
private noncomputable def weight (y : E) : ℝ := (1 - min ‖y‖ 1 ^ 2) / 2

private lemma weight_lipschitz : LipschitzWith 1 (weight (E := E)) := by
  let m (x : E) := min ‖x‖ 1
  have hm : LipschitzWith 1 m := lipschitzWith_one_norm.min_const 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    |weight x - weight y| = |m y - m x| * ((m x + m y) / 2) := by
      have hn : 0 ≤ (m x + m y) / 2 := by dsimp [m]; positivity
      rw [← abs_of_nonneg hn, ← abs_mul]
      congr 1
      dsimp [weight, m]
      ring
    _ ≤ dist x y := by
      have h := hm.dist_le_mul y x
      rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_comm y x] at h
      exact (mul_le_of_le_one_right (abs_nonneg _) (by
        dsimp [m]
        linarith [min_le_right ‖x‖ (1 : ℝ), min_le_right ‖y‖ (1 : ℝ)])).trans h

private lemma weight_eq_zero {y : E} (hy : y ∉ closedBall 0 1) : weight y = 0 := by
  simp only [mem_closedBall, dist_zero_right, not_le] at hy
  simp [weight, min_eq_right hy.le]

variable [InnerProductSpace ℝ E]

private lemma weight_lineDeriv {y : E} (hy : y ∈ ball 0 1) (v : E) :
    lineDeriv ℝ weight y (-v) = ⟪v, y⟫_ℝ := by
  have he : weight =ᶠ[𝓝 y] (fun z : E ↦ (1 - ‖z‖ ^ 2) / 2) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp [weight, min_eq_left (mem_ball_zero_iff.mp hz).le]
  simp only [div_eq_mul_inv] at he
  have hd := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_sub 1).mul_const (2 : ℝ)⁻¹
  rw [he.lineDeriv_eq, (hd.hasLineDerivAt (-v)).lineDeriv]
  simp [real_inner_comm v y]

private lemma mapsTo_unitBall (x : E) {s : ℝ} (hs : 0 ≤ s) :
    MapsTo (fun y ↦ x + s • y) (closedBall 0 1) (closedBall x s) := by
  intro y hy
  simpa [mem_closedBall, dist_eq_norm, norm_smul, Real.norm_of_nonneg hs]
    using mul_le_of_le_one_right hs (mem_closedBall_zero_iff.mp hy)

variable [FiniteDimensional ℝ E]

private lemma laplacian_continuousOn {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) : ContinuousOn (Δ u) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hH := (hd.fderiv_of_isOpen (m := 0) hU (by norm_num)).continuousOn
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo]
  exact continuousOn_finsetSum _ fun _ _ ↦ (hH.clm_apply continuousOn_const).clm_apply
    continuousOn_const

variable [MeasurableSpace E] [BorelSpace E]

/-- Integration by parts against the truncated quadratic weight produces a coordinate of
the position vector. Only the restriction of the differentiated function to the ball matters. -/
private lemma integral_inner_mul {q : E → ℝ} (v : E)
    (hq : ContDiffOn ℝ 1 q (closedBall 0 1)) :
    ∫ y in closedBall (0 : E) 1, ⟪v, y⟫_ℝ * q y =
      ∫ y in closedBall (0 : E) 1, weight y * fderiv ℝ q y v := by
  classical
  obtain ⟨K, hK⟩ := hq.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall ..) (isCompact_closedBall ..)
  obtain ⟨g, hg, he⟩ := hK.extend_real
  have hc : HasCompactSupport (weight (E := E)) :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun _ ↦ weight_eq_zero
  have hs : ∀ᵐ y : E, y ∉ sphere 0 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere_of_ne_zero volume 0 one_ne_zero)
  rw [← integral_indicator measurableSet_closedBall, ← integral_indicator measurableSet_closedBall]
  calc
    _ = ∫ y, lineDeriv ℝ weight y (-v) * g y := by
      apply integral_congr_ae
      filter_upwards [hs] with y hy
      by_cases h : y ∈ closedBall (0 : E) 1
      · have hi : y ∈ ball (0 : E) 1 := lt_of_le_of_ne h hy
        rw [indicator_of_mem h, weight_lineDeriv hi, he h]
      · have hz : weight =ᶠ[𝓝 y] (fun _ : E ↦ (0 : ℝ)) := by
          filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds h] with z hz
          exact weight_eq_zero hz
        rw [indicator_of_notMem h, hz.lineDeriv_eq,
          ((hasFDerivAt_const (0 : ℝ) y).hasLineDerivAt (-v)).lineDeriv]
        simp
    _ = ∫ y, lineDeriv ℝ g y v * weight y :=
      (hg.integral_lineDeriv_mul_eq weight_lipschitz hc v).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hs] with y hy
      by_cases h : y ∈ closedBall (0 : E) 1
      · have hi : y ∈ ball (0 : E) 1 := lt_of_le_of_ne h hy
        have hn := mem_of_superset (isOpen_ball.mem_nhds hi) ball_subset_closedBall
        have hd := (hq.differentiableOn_one y h).differentiableAt hn
        have he' : q =ᶠ[𝓝 y] g := Filter.eventually_of_mem hn fun _ hz ↦ he hz
        rw [indicator_of_mem h, ← he'.lineDeriv_eq, (hd.hasFDerivAt.hasLineDerivAt v).lineDeriv,
          mul_comm]
      · simp [indicator_of_notMem h, weight_eq_zero h]

/-- Summing the integration by parts identity for the directional derivatives gives the
weighted Laplacian. The factor `t` comes from differentiating `x + t • y` in `y`. -/
private lemma radial_integral {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (x : E) (t : ℝ)
    (ht : MapsTo (fun y ↦ x + t • y) (closedBall 0 1) U) :
    ∫ y in closedBall (0 : E) 1, fderiv ℝ u (x + t • y) y =
      t * ∫ y in closedBall (0 : E) 1, weight y * Δ u (x + t • y) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let p := fun y : E ↦ x + t • y
  let d := fderiv ℝ u
  let H := fderiv ℝ d
  let B := closedBall (0 : E) 1
  have hd : ContDiffOn ℝ 1 d U := hu.fderiv_of_isOpen hU (by norm_num)
  have hH : ContinuousOn H U := (hd.fderiv_of_isOpen (m := 0) hU (by norm_num)).continuousOn
  have hp : ContDiff ℝ 1 p := contDiff_const.add (contDiff_id.const_smul t)
  let q := fun i y ↦ d (p y) (b i)
  have hq i : ContDiffOn ℝ 1 (q i) B := (hd.comp hp.contDiffOn ht).clm_apply contDiffOn_const
  have hq' i y (hy : y ∈ B) : fderiv ℝ (q i) y (b i) = t * H (p y) (b i) (b i) := by
    have hp' := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t).const_add x
    have hd' := ((hd.contDiffAt (hU.mem_nhds (ht hy))).differentiableAt one_ne_zero).hasFDerivAt
    have he := ((hd'.comp y hp').clm_apply (hasFDerivAt_const (𝕜 := ℝ) (b i) y)).fderiv
    simpa [q, p, H, Function.comp_def] using congrArg (fun L : E →L[ℝ] ℝ ↦ L (b i)) he
  have htrace (z : E) : Δ u z = ∑ i, H z (b i) (b i) := by
    simp [laplacian_eq_iteratedFDeriv_orthonormalBasis u b,
      ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo, H, d]
  calc
    _ = ∫ y in B, ∑ i, ⟪b i, y⟫_ℝ * q i y := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro y _
      simpa [q, p, d] using congrArg (d (p y)) (b.sum_repr' y).symm
    _ = ∑ i, ∫ y in B, ⟪b i, y⟫_ℝ * q i y := by
      apply integral_finsetSum
      intro i _
      exact ((continuous_const.inner continuous_id).continuousOn.mul
        (hq i).continuousOn).integrableOn_compact (isCompact_closedBall ..)
    _ = ∑ i, ∫ y in B, t * (weight y * H (p y) (b i) (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_inner_mul _ (hq i)]
      apply setIntegral_congr_fun measurableSet_closedBall
      intro y hy
      dsimp only
      rw [hq' i y hy]
      ring
    _ = ∫ y in B, ∑ i, t * (weight y * H (p y) (b i) (b i)) := by
      symm
      apply integral_finsetSum
      intro i _
      have hc := (hH.comp hp.continuous.continuousOn ht).clm_apply
        (continuousOn_const (c := b i))
      exact (continuousOn_const.mul (weight_lipschitz.continuous.continuousOn.mul
        (hc.clm_apply continuousOn_const))).integrableOn_compact (isCompact_closedBall ..)
    _ = _ := by simp only [← Finset.mul_sum, ← htrace, integral_const_mul, B, p]

private lemma hasDerivAt_ballIntegral {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (x : E) (t : ℝ)
    (ht : MapsTo (fun y ↦ x + t • y) (closedBall 0 1) U) :
    HasDerivAt (fun s : ℝ ↦ ∫ y in closedBall (0 : E) 1, u (x + s • y))
      (t * ∫ y in closedBall (0 : E) 1, weight y * Δ u (x + t • y)) t := by
  let p := fun z : ℝ × E ↦ x + z.1 • z.2
  let B := closedBall (0 : E) 1
  have hp : ContDiff ℝ 1 p := contDiff_const.add (contDiff_fst.smul contDiff_snd)
  obtain ⟨V, W, hV, _, htV, hBW, hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := t)) (isCompact_closedBall (0 : E) 1)
    (hU.preimage hp.continuous) (by rintro ⟨s, y⟩ ⟨rfl : s = t, hy⟩; exact ht hy)
  have hc : ContDiffOn ℝ 1 (fun z : ℝ × E ↦ u (p z)) (V ×ˢ B) :=
    (hu.of_le (by norm_num)).comp hp.contDiffOn ((prod_mono_right hBW).trans hVW)
  let F := fun s : ℝ ↦ fun y : E ↦ u (x + s • y)
  have h := (hasFDerivAt_integral_of_contDiffOn (μ := volume) (f := F)
    (hV.mem_nhds (htV (mem_singleton t))) (isCompact_closedBall (0 : E) 1)
    (isCompact_closedBall (0 : E) 1).measure_ne_top Subset.rfl hc).hasDerivAt
  let a := fun y ↦ fderiv ℝ (fun s ↦ F s y) t
  have ha (y) (hy : y ∈ B) :
      HasDerivAt (fun s ↦ F s y) (fderiv ℝ u (x + t • y) y) t := by
    have hd := ((hu.contDiffAt (hU.mem_nhds (ht hy))).differentiableAt (by norm_num)).hasFDerivAt
    simpa [F, Function.comp_def] using!
      hd.comp_hasDerivAt t (((hasDerivAt_id' t).smul_const y).const_add x)
  have hai : IntegrableOn a B := by
    apply ContinuousOn.integrableOn_compact (isCompact_closedBall ..)
    exact ContinuousOn.uncurry_left (f := fun s y ↦ fderiv ℝ (fun z ↦ F z y) s) t
      (htV (mem_singleton t)) (hc.fderiv_left (f := F) hV (n := 0)).continuousOn
  convert h using 1
  rw [← radial_integral hU hu x t ht, ContinuousLinearMap.integral_apply hai]
  exact setIntegral_congr_fun measurableSet_closedBall fun y hy ↦ (ha y hy).deriv.symm

/-- Change variables from a ball of radius `r` to the unit ball. -/
private lemma ballIntegral_eq (u : E → ℝ) (x : E) {r : ℝ} (hr : 0 < r) :
    ∫ y in closedBall (0 : E) 1, u (x + r • y) =
      volume.real (closedBall (0 : E) 1) * ⨍ y in closedBall x r, u y := by
  have hpre : (fun y ↦ x + y) ⁻¹' closedBall x r = closedBall 0 r := by
    ext y
    simp [mem_closedBall, dist_eq_norm]
  have hvol : volume.real (closedBall (0 : E) 1) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume 0 zero_lt_one).ne'
      measure_closedBall_lt_top.ne).ne'
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun y ↦ u (x + y)) _ hr,
    smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_one, ← hpre,
    (measurePreserving_add_left volume x).setIntegral_preimage_emb (measurableEmbedding_addLeft x),
    setAverage_eq, Measure.addHaar_real_closedBall' volume x hr.le]
  simp [smul_eq_mul, mul_assoc, hvol]

private lemma laplacian_eq_zero_of_average {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (hm : ∀ x : E, ∀ r : ℝ, 0 < r → closedBall x r ⊆ U → ⨍ y in closedBall x r, u y = u x)
    (x : E) (hx : x ∈ U) : Δ u x = 0 := by
  by_contra hne
  -- A nonzero Laplacian keeps its sign on a small ball about the centre.
  have hc := laplacian_continuousOn hU hu
  have hpos := (continuousAt_const.mul (hc.continuousAt (hU.mem_nhds hx))).eventually
    (lt_mem_nhds (mul_self_pos.mpr hne))
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hpos)
  let t := R / 2
  have ht : t ∈ Ioo 0 R := ⟨half_pos hR, half_lt_self hR⟩
  have hdom {s} (hs : s ∈ Ioo 0 R) : closedBall x s ⊆ U :=
    fun y hy ↦ (hsub (closedBall_subset_ball hs.2 hy)).1
  let B := closedBall (0 : E) 1
  let p := fun y : E ↦ x + t • y
  have hp : MapsTo p B U := (mapsTo_unitBall x ht.1.le).mono_right (hdom ht)
  have he : (fun s : ℝ ↦ ∫ y in B, u (x + s • y)) =ᶠ[𝓝 t]
      (fun _ ↦ volume.real B * u x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [ballIntegral_eq u x hs.1, hm x s hs.1 (hdom hs)]
  have hz := (hasDerivAt_ballIntegral hU hu x t hp).unique
    ((hasDerivAt_const t (volume.real B * u x)).congr_of_eventuallyEq he)
  have hz' := (mul_eq_zero.mp hz).resolve_left ht.1.ne'
  let f := fun y ↦ Δ u x * (weight y * Δ u (p y))
  have hf (y : E) (hy : y ∈ B) : 0 < Δ u x * Δ u (p y) :=
    (hsub (closedBall_subset_ball ht.2 (mapsTo_unitBall x ht.1.le hy))).2
  have hw {y : E} (hy : y ∈ B) : 0 ≤ weight y := by
    have hn := mem_closedBall_zero_iff.mp hy
    rw [weight, min_eq_left hn]
    nlinarith [sq_le_sq₀ (norm_nonneg y) zero_le_one |>.mpr hn]
  have hfi : IntegrableOn f B := (continuousOn_const.mul
    (weight_lipschitz.continuous.continuousOn.mul (hc.comp (by fun_prop : Continuous p).continuousOn
      hp))).integrableOn_compact (isCompact_closedBall ..)
  have hfp : 0 < ∫ y in B, f y := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ hfi).2
    · apply (measure_ball_pos volume (0 : E) zero_lt_one).trans_le (measure_mono _)
      intro y hy
      have hn := mem_ball_zero_iff.mp hy
      have hw' : 0 < weight y := by
        rw [weight, min_eq_left hn.le]
        nlinarith [sq_lt_sq₀ (norm_nonneg y) zero_le_one |>.mpr hn]
      exact ⟨(show 0 < f y by
        simpa [f, mul_left_comm] using mul_pos hw' (hf y (ball_subset_closedBall hy))).ne',
        ball_subset_closedBall hy⟩
    · filter_upwards [ae_restrict_mem (s := B) measurableSet_closedBall] with y hy
      simpa [f, mul_left_comm] using mul_nonneg (hw hy) (hf y hy).le
  apply hfp.ne'
  change ∫ y in B, Δ u x * (weight y * Δ u (x + t • y)) = 0
  rw [integral_const_mul, hz', mul_zero]

/-- **Mean-value property of harmonic functions, and its converse.** Let `U` be open and `u` be
`C²` on `U`. Then `u` is harmonic on `U` if and only if `⨍_{closedBall x r} u = u x` for every
closed ball of positive radius contained in `U`. This is Mean Value Property 3.3 of M. Schmidt,
*Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 3, in
its ball-average form (balls with compact closure in `U`; the source also gives sphere averages). -/
theorem harmonicOnNhd_iff_forall_average_closedBall {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) :
    HarmonicOnNhd u U ↔
      ∀ x : E, ∀ r : ℝ, 0 < r → closedBall x r ⊆ U → ⨍ y in closedBall x r, u y = u x := by
  constructor
  · intro hh x r hr hball
    let B := closedBall (0 : E) 1
    let A := fun s : ℝ ↦ ∫ y in B, u (x + s • y)
    have hd (s) (hs : s ∈ Icc 0 r) : HasDerivAt A 0 s := by
      have hp := (mapsTo_unitBall x hs.1).mono_right
        ((closedBall_subset_closedBall hs.2).trans hball)
      have hz : ∫ y in B, weight y * Δ u (x + s • y) = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro y hy
        simp [(hh _ (hp hy)).2.self_of_nhds]
      have h := hasDerivAt_ballIntegral hU hu x s hp
      rw [hz, mul_zero] at h
      exact h
    obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope A hr
      (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt)
    rw [(hd c (Ioo_subset_Icc_self hc)).deriv, sub_zero, eq_comm, div_eq_zero_iff] at he
    have h := sub_eq_zero.mp (he.resolve_right hr.ne')
    have hvol : volume.real B ≠ 0 :=
      (ENNReal.toReal_pos (measure_closedBall_pos volume (0 : E) zero_lt_one).ne'
        measure_closedBall_lt_top.ne).ne'
    apply mul_left_cancel₀ hvol
    simpa only [A, B, ballIntegral_eq u x hr, zero_smul, add_zero, setIntegral_const, smul_eq_mul]
      using h
  · intro hm x hx
    refine ⟨hu.contDiffAt (hU.mem_nhds hx), ?_⟩
    filter_upwards [hU.mem_nhds hx] with y hy
    exact laplacian_eq_zero_of_average hU hu hm y hy

end MathlibExt.Analysis.PDE.LaplaceMeanValueWanted
