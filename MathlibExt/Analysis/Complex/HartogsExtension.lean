/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.WithLp

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Hartogs extension in `ℂⁿ`

This file proves extension across compact holes in connected domains of complex Euclidean spaces.
It also develops the required several-variable `C¹` regularity and a compactly supported
one-variable Cauchy–Green solver.
-/

namespace MathlibExt.Analysis.Complex.HartogsWanted

open MeasureTheory Set
open scoped Convolution

private theorem hartogsext_fderiv_single_eq_deriv
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (i : Fin n) (hf : DifferentiableAt ℂ f x) :
    fderiv ℂ f x (EuclideanSpace.single i 1) =
      deriv (fun z : ℂ ↦ f (x + z • EuclideanSpace.single i 1)) 0 := by
  have hline : HasDerivAt (fun z : ℂ ↦ x + z • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const (EuclideanSpace.single i 1)).const_add x
  have hf₀ : DifferentiableAt ℂ f (x + (0 : ℂ) • EuclideanSpace.single i 1) := by
    simpa using hf
  change fderiv ℂ f x (EuclideanSpace.single i 1) =
    deriv (f ∘ fun z : ℂ ↦ x + z • EuclideanSpace.single i 1) 0
  simpa using (hf₀.hasFDerivAt.comp_hasDerivAt 0 hline).deriv.symm

private theorem hartogsext_line_closedBall_subset
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {x₀ x : EuclideanSpace ℂ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.ball x₀ r) (hball : Metric.ball x₀ (4 * r) ⊆ s)
    (i : Fin n) :
    Metric.closedBall (0 : ℂ) (2 * r) ⊆
      (fun z : ℂ ↦ x + z • EuclideanSpace.single i 1) ⁻¹' s := by
  intro z hz
  apply hball
  rw [Metric.mem_ball]
  calc
    dist (x + z • EuclideanSpace.single i 1) x₀ ≤
        dist (x + z • EuclideanSpace.single i 1) x + dist x x₀ := dist_triangle _ _ _
    _ = ‖z‖ + dist x x₀ := by
      simp [dist_eq_norm, norm_smul]
    _ < 4 * r := by
      have hz' : ‖z‖ ≤ 2 * r := by simpa [Metric.mem_closedBall] using hz
      have hx' : dist x x₀ < r := Metric.mem_ball.1 hx
      linarith

private theorem hartogsext_continuousOn_circle_partial
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {x₀ : EuclideanSpace ℂ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball x₀ (4 * r) ⊆ s)
    (hf : ContinuousOn f s) (i : Fin n) :
    ContinuousOn
      (fun x ↦ ∮ z in C(0, 2 * r),
        (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1))
      (Metric.ball x₀ r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let q : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball x₀ r
  let _ : LocallyCompactSpace q :=
    IsOpen.locallyCompactSpace (by simp [q])
  have hfcomp : Continuous (fun p : q × ℝ ↦
      f (p.1.1 + circleMap 0 (2 * r) p.2 • EuclideanSpace.single i 1)) := by
    apply hf.comp_continuous (by fun_prop)
    intro p
    apply hartogsext_line_closedBall_subset hr p.1.2 hball i
    exact Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 (by positivity) p.2)
  have hcircle (p : q × ℝ) : circleMap 0 (2 * r) p.2 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_circleMap_zero, abs_of_pos (by positivity : 0 < 2 * r)]
    positivity
  have hcirclecont : Continuous (fun p : q × ℝ ↦ circleMap 0 (2 * r) p.2) := by
    fun_prop
  have hinv : Continuous (fun p : q × ℝ ↦ ((circleMap 0 (2 * r) p.2) ^ 2)⁻¹) :=
    (hcirclecont.pow 2).inv₀ fun p ↦ pow_ne_zero _ (hcircle p)
  have hint : Continuous (fun p : q × ℝ ↦
      deriv (circleMap 0 (2 * r)) p.2 *
        ((circleMap 0 (2 * r) p.2) ^ 2)⁻¹ *
          f (p.1.1 + circleMap 0 (2 * r) p.2 • EuclideanSpace.single i 1)) := by
    simp_rw [deriv_circleMap]
    exact ((hcirclecont.mul continuous_const).mul hinv).mul hfcomp
  have hc := continuous_parametric_integral_of_continuous
    (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) (2 * Real.pi))
    (f := fun x : q ↦ fun θ : ℝ ↦
      deriv (circleMap 0 (2 * r)) θ * ((circleMap 0 (2 * r) θ) ^ 2)⁻¹ *
        f (x.1 + circleMap 0 (2 * r) θ • EuclideanSpace.single i 1))
    hint isCompact_Icc
  apply hc.congr
  intro x
  rw [Set.domRestrict_apply, circleIntegral_def_Icc]
  simp only [smul_eq_mul, mul_assoc]

private theorem hartogsext_fderiv_single_eq_circleIntegral
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {x₀ x : EuclideanSpace ℂ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hs : IsOpen s)
    (hball : Metric.ball x₀ (4 * r) ⊆ s) (hf : DifferentiableOn ℂ f s)
    (hx : x ∈ Metric.ball x₀ r) (i : Fin n) :
    fderiv ℂ f x (EuclideanSpace.single i 1) =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1) := by
  let line : ℂ → EuclideanSpace ℂ (Fin n) :=
    fun z ↦ x + z • EuclideanSpace.single i 1
  let v : Set ℂ := line ⁻¹' s
  have hv : IsOpen v := hs.preimage (by fun_prop)
  have hline : Differentiable ℂ line := by
    dsimp [line]
    fun_prop
  have hg : DifferentiableOn ℂ (fun z ↦ f (line z)) v := by
    intro z hz
    exact ((hf.differentiableAt (hs.mem_nhds hz)).comp z (hline z)).differentiableWithinAt
  have hclosed : Metric.closedBall (0 : ℂ) (2 * r) ⊆ v := by
    exact hartogsext_line_closedBall_subset hr hx hball i
  have hformula :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      hv hclosed hg (Metric.mem_ball_self (by positivity : 0 < 2 * r))
  have hxs : x ∈ s := by
    apply hball
    rw [Metric.mem_ball] at hx ⊢
    linarith
  calc
    fderiv ℂ f x (EuclideanSpace.single i 1) = deriv (fun z ↦ f (line z)) 0 := by
      exact hartogsext_fderiv_single_eq_deriv i
        (hf.differentiableAt (hs.mem_nhds hxs))
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (line z) := by
      simpa [sub_zero, smul_eq_mul] using hformula.symm
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1) := by
      rfl

private theorem hartogsext_continuousOn_fderiv_single
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (i : Fin n) :
    ContinuousOn (fun x ↦ fderiv ℂ f x (EuclideanSpace.single i 1)) s := by
  rw [hs.continuousOn_iff]
  intro x hx
  rcases Metric.isOpen_iff.mp hs x hx with ⟨ε, hε, hεs⟩
  let r := ε / 4
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hball : Metric.ball x (4 * r) ⊆ s := by
    have hradius : (4 : ℝ) * (ε / 4) = ε := by ring
    simpa only [r, hradius] using hεs
  have hcircle := hartogsext_continuousOn_circle_partial
    hr hball hf.continuousOn i
  have hscaled : ContinuousOn
      (fun y ↦ (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (y + z • EuclideanSpace.single i 1))
      (Metric.ball x r) :=
    continuousOn_const.mul hcircle
  have hderiv : ContinuousOn
      (fun y ↦ fderiv ℂ f y (EuclideanSpace.single i 1)) (Metric.ball x r) :=
    hscaled.congr fun y hy ↦
      hartogsext_fderiv_single_eq_circleIntegral hr hs hball hf hy i
  exact hderiv.continuousAt (Metric.ball_mem_nhds x hr)

/-- The derivative of a complex-differentiable scalar function on an open subset of `ℂⁿ` is
continuous. In particular, the function is `C¹` there. -/
theorem continuousOn_fderiv_of_differentiableOn
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) : ContinuousOn (fderiv ℂ f) s := by
  have hsingle (i : Fin n) :
      ContinuousOn (fun x ↦ fderiv ℂ f x (EuclideanSpace.single i 1)) s :=
    hartogsext_continuousOn_fderiv_single hs hf i
  have hfd : ContinuousOn (fderiv ℂ f) s := by
    rw [continuousOn_clm_apply]
    intro y
    have hsum : ContinuousOn
        (fun x ↦ ∑ i : Fin n,
          WithLp.ofLp y i * fderiv ℂ f x (EuclideanSpace.single i 1)) s := by
      apply continuousOn_finsetSum Finset.univ
      intro i hi
      exact continuousOn_const.mul (hsingle i)
    apply hsum.congr
    intro x hx
    change fderiv ℂ f x y = ∑ i : Fin n,
      WithLp.ofLp y i * fderiv ℂ f x (EuclideanSpace.single i 1)
    have hy : y = ∑ i : Fin n,
        WithLp.ofLp y i • EuclideanSpace.single i 1 := by
      simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr y).symm
    conv_lhs => rw [hy]
    simp
  exact hfd

private theorem hartogsext_differentiableOn_contDiffOn_one_real
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) : ContDiffOn ℝ 1 f s := by
  have hcomplex := continuousOn_fderiv_of_differentiableOn hs hf
  have hrestricted : ContinuousOn
      (fun x ↦ (fderiv ℂ f x).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ
      (EuclideanSpace ℂ (Fin n)) ℂ ℝ ℝ).continuous.comp_continuousOn hcomplex
  have hreal : ContinuousOn (fderiv ℝ f) s := by
    apply hrestricted.congr
    intro x hx
    exact (hf.differentiableAt (hs.mem_nhds hx)).fderiv_restrictScalars (𝕜 := ℝ)
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hs).2
  exact ⟨hf.restrictScalars ℝ, by simp, contDiffOn_zero.mpr hreal⟩

private theorem hartogsext_contDiff_mul_of_tsupport_subset
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f a : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (ha : ContDiff ℝ 1 a) (has : tsupport a ⊆ s) :
    ContDiff ℝ 1 (fun x ↦ f x * a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact ((hf x hx).contDiffAt (hs.mem_nhds hx)).mul ha.contDiffAt
  · have hxt : x ∉ tsupport a := fun h ↦ hx (has h)
    have ha0 : Filter.EventuallyEq (nhds x) a (fun _ ↦ 0) := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hxt] with y hy
      rw [mem_compl_iff] at hy
      apply Classical.byContradiction
      intro hay
      exact hy (subset_tsupport a hay)
    have hzero : ContDiffAt ℝ 1
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℂ)) x := contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [ha0] with y hy
    simp [hy]

private theorem hartogsext_exists_cutoff
    {n : ℕ} {U K : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℂ (Fin n) → ℝ,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
        ∃ V, IsOpen V ∧ K ⊆ V ∧ Set.EqOn χ (fun _ ↦ 1) V := by
  obtain ⟨W, hWopen, hKW, hWcompact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hK
  have hUWopen : IsOpen (U ∩ W) := hU.inter hWopen
  have hKUW : K ⊆ U ∩ W := fun x hx ↦ ⟨hKU hx, hKW hx⟩
  obtain ⟨S, hSopen, hKS, hSsub⟩ :=
    hK.exists_isOpen_closure_subset (hUWopen.mem_nhdsSet.mpr hKUW)
  have hScompact : IsCompact (closure S) :=
    hWcompact.of_isClosed_subset isClosed_closure
      ((hSsub.trans inter_subset_right).trans subset_closure)
  obtain ⟨V, hVopen, hKV, hVsub⟩ :=
    hK.exists_isOpen_closure_subset (hSopen.mem_nhdsSet.mpr hKS)
  obtain ⟨χ, hχdiff, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 2) hSopen isClosed_closure hVsub
  refine ⟨χ, hχdiff, ?_, ?_, V, hVopen, hKV, ?_⟩
  · rw [HasCompactSupport, tsupport, hχsupport]
    exact hScompact
  · rw [tsupport, hχsupport]
    exact hSsub.trans inter_subset_left
  · intro x hx
    exact (hχone x).mp (subset_closure hx)

private noncomputable def hartogsextBarPartial
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  (2 : ℂ)⁻¹ *
    (fderiv ℝ f x (EuclideanSpace.single i 1) +
      Complex.I * fderiv ℝ f x (EuclideanSpace.single i Complex.I))

/-- The Wirtinger derivative `∂f/∂z̄` of a real-differentiable complex-valued function. -/
noncomputable def barDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

private noncomputable def hartogsextBarEvalCLM
    {n : ℕ} (i : Fin n) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)) +
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp
        (ContinuousLinearMap.apply ℝ ℂ
          (EuclideanSpace.single i Complex.I)))

private theorem hartogsextBarEvalCLM_apply
    {n : ℕ} (i : Fin n) (L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) :
    hartogsextBarEvalCLM i L =
      (2 : ℂ)⁻¹ *
        (L (EuclideanSpace.single i 1) +
          Complex.I * L (EuclideanSpace.single i Complex.I)) := by
  simp only [hartogsextBarEvalCLM, ContinuousLinearMap.comp_add, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.mul_apply']
  exact (mul_add _ _ _).symm

private theorem hartogsextBarPartial_eq_barEval
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i f x = hartogsextBarEvalCLM i (fderiv ℝ f x) := by
  rw [hartogsextBarPartial, hartogsextBarEvalCLM_apply]

private theorem hartogsext_barPartial_mul
    {n : ℕ} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ f y * g y) x =
      hartogsextBarPartial i f x * g x + f x * hartogsextBarPartial i g x := by
  rw [hartogsextBarPartial, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hartogsextBarPartial, hartogsextBarPartial]
  ring

private theorem hartogsext_barPartial_add
    {n : ℕ} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ f y + g y) x =
      hartogsextBarPartial i f x + hartogsextBarPartial i g x := by
  rw [hartogsextBarPartial, fderiv_fun_add hf hg]
  simp only [add_apply]
  rw [hartogsextBarPartial, hartogsextBarPartial]
  ring

private theorem hartogsext_barPartial_one_sub
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ 1 - f y) x =
      -hartogsextBarPartial i f x := by
  rw [hartogsextBarPartial, fderiv_const_sub]
  simp only [neg_apply]
  rw [hartogsextBarPartial]
  ring

private theorem hartogsext_barPartial_comm
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i (hartogsextBarPartial j f) x =
      hartogsextBarPartial j (hartogsextBarPartial i f) x := by
  let Ci := hartogsextBarEvalCLM i
  let Cj := hartogsextBarEvalCLM j
  let D2 := fderiv ℝ (fderiv ℝ f) x
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hfj : hartogsextBarPartial j f = Cj ∘ fderiv ℝ f := by
    funext y
    exact hartogsextBarPartial_eq_barEval j f y
  have hfi : hartogsextBarPartial i f = Ci ∘ fderiv ℝ f := by
    funext y
    exact hartogsextBarPartial_eq_barEval i f y
  have hj : HasFDerivAt (hartogsextBarPartial j f) (Cj.comp D2) x := by
    rw [hfj]
    exact (Cj.hasFDerivAt (x := fderiv ℝ f x)).comp x hD.hasFDerivAt
  have hi : HasFDerivAt (hartogsextBarPartial i f) (Ci.comp D2) x := by
    rw [hfi]
    exact (Ci.hasFDerivAt (x := fderiv ℝ f x)).comp x hD.hasFDerivAt
  rw [hartogsextBarPartial_eq_barEval, hartogsextBarPartial_eq_barEval,
    hj.fderiv, hi.fderiv]
  dsimp only [Ci, Cj]
  simp only [hartogsextBarEvalCLM_apply, ContinuousLinearMap.comp_apply]
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)
  rw [hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
    hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j Complex.I),
    hsymm (EuclideanSpace.single i Complex.I) (EuclideanSpace.single j 1),
    hsymm (EuclideanSpace.single i Complex.I) (EuclideanSpace.single j Complex.I)]
  ring

private theorem hartogsext_contDiff_barPartial
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (hartogsextBarPartial i f) := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  unfold hartogsextBarPartial
  exact contDiff_const.mul
    ((hDf.clm_apply contDiff_const).add
      (contDiff_const.mul (hDf.clm_apply contDiff_const)))

private theorem hartogsext_hasCompactSupport_barPartial
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (hartogsextBarPartial i f) := by
  have h1 := hf.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hI := hf.fderiv_apply ℝ (EuclideanSpace.single i Complex.I)
  have hsum : HasCompactSupport
      ((fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) +
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ Complex.I) *
          fun x ↦ fderiv ℝ f x (EuclideanSpace.single i Complex.I)) :=
    HasCompactSupport.add h1 (HasCompactSupport.mul_left hI)
  have hscaled := HasCompactSupport.mul_left hsum
    (f := fun _ : EuclideanSpace ℂ (Fin n) ↦ (2 : ℂ)⁻¹)
  change HasCompactSupport
    (fun x ↦ (2 : ℂ)⁻¹ *
      (fderiv ℝ f x (EuclideanSpace.single i 1) +
        Complex.I * fderiv ℝ f x (EuclideanSpace.single i Complex.I)))
  convert hscaled using 1

private theorem hartogsext_tsupport_barPartial_subset
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ} (i : Fin n) :
    tsupport (hartogsextBarPartial i f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  have hfd : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ hxt
  exact hx (by simp [hartogsextBarPartial, hfd])

private theorem hartogsext_barPartial_eq_zero_of_notMem_tsupport
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∉ tsupport f) (i : Fin n) :
    hartogsextBarPartial i f x = 0 := by
  rw [hartogsextBarPartial, fderiv_of_notMem_tsupport ℝ hx]
  simp

private theorem hartogsext_barPartial_eq_zero_of_differentiableAt
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℂ f x) (i : Fin n) :
    hartogsextBarPartial i f x = 0 := by
  rw [hartogsextBarPartial, hf.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have hsingle : EuclideanSpace.single i Complex.I =
      Complex.I • EuclideanSpace.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hsingle, map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

private theorem hartogsext_tsupport_barPartial_subset_compl
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {V : Set (EuclideanSpace ℂ (Fin n))} (hV : IsOpen V)
    (hf : Set.EqOn f (fun _ ↦ 1) V) (i : Fin n) :
    tsupport (hartogsextBarPartial i f) ⊆ Vᶜ := by
  apply closure_minimal _ hV.isClosed_compl
  intro x hx
  rw [mem_compl_iff]
  intro hxV
  have hxV' : x ∈ V := by simpa using hxV
  have hconst : Filter.EventuallyEq (nhds x) f (fun _ ↦ 1) := by
    filter_upwards [hV.mem_nhds hxV'] with y hy
    exact hf hy
  have hfd : fderiv ℝ f x = 0 :=
    (hasFDerivAt_zero_of_eventually_const (1 : ℂ) hconst).fderiv
  rw [Function.mem_support] at hx
  exact hx (by simp [hartogsextBarPartial, hfd])

private noncomputable def hartogsextReplace
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    EuclideanSpace ℂ (Fin n) :=
  x + EuclideanSpace.single i (z - WithLp.ofLp x i)

private theorem hartogsextReplace_apply
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    WithLp.ofLp (hartogsextReplace i x z) i = z := by
  simp [hartogsextReplace]

private theorem hartogsextReplace_self
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextReplace i x (WithLp.ofLp x i) = x := by
  simp [hartogsextReplace]

private theorem hartogsextReplace_sub
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    hartogsextReplace i x (WithLp.ofLp x i - t) =
      x - EuclideanSpace.single i t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [hartogsextReplace, PiLp.add_apply, PiLp.sub_apply,
      PiLp.single_eq_same]
    abel
  · simp only [hartogsextReplace, PiLp.add_apply, PiLp.sub_apply,
      PiLp.single_eq_of_ne (p := 2) hji]
    rw [add_zero, sub_zero]

private noncomputable def hartogsextSlice
    {n : ℕ} (i : Fin n) (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) : ℂ :=
  g (hartogsextReplace i x z)

private theorem hartogsext_single_eq_smul
    {n : ℕ} (i : Fin n) (z : ℂ) :
    EuclideanSpace.single i z = z • EuclideanSpace.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private noncomputable def hartogsextSingleCLM
    {n : ℕ} (i : Fin n) : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  ((ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)).flip)
      (EuclideanSpace.single i 1)

private theorem hartogsextSingleCLM_apply
    {n : ℕ} (i : Fin n) (z : ℂ) :
    hartogsextSingleCLM i z = EuclideanSpace.single i z := by
  change z • EuclideanSpace.single i 1 = EuclideanSpace.single i z
  exact (hartogsext_single_eq_smul i z).symm

private theorem hartogsextReplace_hasFDerivAt
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    HasFDerivAt (hartogsextReplace i x) (hartogsextSingleCLM i) z := by
  let S := hartogsextSingleCLM i
  have haff : HasFDerivAt
      (fun w ↦ (x - S (WithLp.ofLp x i)) + S w) S z :=
    (S.hasFDerivAt (x := z)).const_add (x - S (WithLp.ofLp x i))
  apply haff.congr_of_eventuallyEq
  filter_upwards with w
  rw [hartogsextReplace, hartogsext_single_eq_smul]
  change x + S (w - WithLp.ofLp x i) = x - S (WithLp.ofLp x i) + S w
  rw [map_sub]
  abel

private theorem hartogsext_contDiff_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    ContDiff ℝ 1 (hartogsextSlice i g x) := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun z ↦ ((hg.differentiable (by norm_num)
    (hartogsextReplace i x z)).comp z
      (hartogsextReplace_hasFDerivAt i x z).differentiableAt), ?_⟩
  have hrep : ContDiff ℝ 1 (hartogsextReplace i x) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z ↦ (hartogsextReplace_hasFDerivAt i x z).differentiableAt, ?_⟩
    have hfd : fderiv ℝ (hartogsextReplace i x) = fun _ ↦ hartogsextSingleCLM i := by
      funext z
      exact (hartogsextReplace_hasFDerivAt i x z).fderiv
    rw [hfd]
    exact continuous_const
  have hcomp : ContDiff ℝ 1 (g ∘ hartogsextReplace i x) := hg.comp hrep
  have hslice : hartogsextSlice i g x = g ∘ hartogsextReplace i x := by rfl
  rw [hslice]
  exact hcomp.continuous_fderiv (by norm_num)

private theorem hartogsext_hasCompactSupport_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    HasCompactSupport (hartogsextSlice i g x) := by
  have himage : IsCompact
      ((fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g) :=
    hgc.isCompact.image (by fun_prop)
  obtain ⟨R, hRpos, hR⟩ := himage.isBounded.exists_pos_norm_lt
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy : hartogsextReplace i x z ∈ tsupport g :=
    subset_tsupport g hz
  have hzimage : z ∈
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g := by
    refine ⟨hartogsextReplace i x z, hy, hartogsextReplace_apply i x z⟩
  exact (hR _ hzimage).le

private theorem hartogsext_barDeriv_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    barDeriv (hartogsextSlice i g x) z =
      hartogsextBarPartial i g (hartogsextReplace i x z) := by
  have hcomp := (hg.differentiable (by norm_num)
    (hartogsextReplace i x z)).hasFDerivAt.comp z
      (hartogsextReplace_hasFDerivAt i x z)
  have hcomp' : HasFDerivAt (hartogsextSlice i g x)
      ((fderiv ℝ g (hartogsextReplace i x z)).comp (hartogsextSingleCLM i)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with w
    rfl
  rw [barDeriv, hartogsextBarPartial, hcomp'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hartogsextSingleCLM_apply]

private noncomputable def hartogsextCauchyGreenKernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * z⁻¹

private noncomputable def hartogsextCauchyGreenTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g

private theorem hartogsext_cauchyGreenKernel_locallyIntegrable :
    LocallyIntegrable hartogsextCauchyGreenKernel (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow
    (E := ℂ) (F := ℂ) (μ := volume) (C := Real.pi⁻¹) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · apply ae_of_all
    intro z
    simp only [hartogsextCauchyGreenKernel, norm_mul, norm_inv, Real.rpow_neg_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact le_rfl
  · change AEStronglyMeasurable (fun z : ℂ ↦ (Real.pi : ℂ)⁻¹ * z⁻¹) volume
    exact (measurable_const.mul measurable_id.inv).aestronglyMeasurable

private noncomputable def hartogsextPartialCauchyGreen
    {n : ℕ} (i : Fin n) (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  hartogsextCauchyGreenTransform (hartogsextSlice i g x) (WithLp.ofLp x i)

private theorem hartogsext_contDiff_uncurry_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n) :
    ContDiff ℝ 1 (Function.uncurry (hartogsextSlice i g)) := by
  change ContDiff ℝ 1 (fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
    g (hartogsextReplace i q.1 q.2))
  apply hg.comp
  unfold hartogsextReplace
  rw [show (fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
      q.1 + EuclideanSpace.single i (q.2 - (WithLp.ofLp q.1) i)) =
      fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
        q.1 + (q.2 - (WithLp.ofLp q.1) i) •
        EuclideanSpace.single i 1 by
    funext q
    rw [hartogsext_single_eq_smul]]
  fun_prop

private theorem hartogsext_slice_uniform_support
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (i : Fin n) :
    ∃ R : ℝ, 0 < R ∧ ∀ x z, z ∉ Metric.closedBall 0 R →
      hartogsextSlice i g x z = 0 := by
  have himage : IsCompact
      ((fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i) '' tsupport g) :=
    hgc.isCompact.image (by fun_prop)
  obtain ⟨R, hRpos, hR⟩ := himage.isBounded.exists_pos_norm_lt
  refine ⟨R, hRpos, ?_⟩
  intro x z hz
  apply Classical.byContradiction
  intro hgz
  have hy : hartogsextReplace i x z ∈ tsupport g :=
    subset_tsupport g hgz
  have hzimage : z ∈
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g := by
    refine ⟨hartogsextReplace i x z, hy, ?_⟩
    exact hartogsextReplace_apply i x z
  have hznorm := hR _ hzimage
  apply hz
  simpa [Metric.mem_closedBall, dist_zero_right] using hznorm.le

private theorem hartogsext_contDiff_partialCauchyGreen
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n) :
    ContDiff ℝ 1 (hartogsextPartialCauchyGreen i g) := by
  obtain ⟨R, hRpos, hsupport⟩ := hartogsext_slice_uniform_support hgc i
  have hparam := hartogsext_contDiff_uncurry_slice hg i
  have hcoord : ContDiffOn ℝ 1
      (fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i) Set.univ := by
    change ContDiffOn ℝ 1
      ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ) Set.univ
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ |>.contDiff.contDiffOn
  have hconv := contDiffOn_convolution_right_with_param_comp
    (n := 1) (ContinuousLinearMap.mul ℝ ℂ)
    (s := Set.univ) (k := Metric.closedBall (0 : ℂ) R)
    (v := fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i)
    hcoord isOpen_univ (isCompact_closedBall (0 : ℂ) R)
    (fun p z hp hz ↦ hsupport p z hz)
    hartogsext_cauchyGreenKernel_locallyIntegrable hparam.contDiffOn
  change ContDiff ℝ 1 (fun x : EuclideanSpace ℂ (Fin n) ↦
    (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
      hartogsextSlice i g x) (WithLp.ofLp x i))
  have hconv' : ContDiffOn ℝ 1
      (fun x : EuclideanSpace ℂ (Fin n) ↦
        (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          hartogsextSlice i g x) (WithLp.ofLp x i)) Set.univ :=
    hconv.of_le (by norm_num)
  simpa only [contDiffOn_univ] using hconv'

private noncomputable def hartogsextDiagCLM
    {n : ℕ} (i : Fin n) :
    EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) × ℂ :=
  (1 : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)).prod
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)

private theorem hartogsext_fderiv_uncurry_slice_diag
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    fderiv ℝ (Function.uncurry (hartogsextSlice i g))
        (x, WithLp.ofLp x i - t) (hartogsextDiagCLM i v) =
      fderiv ℝ g (x - EuclideanSpace.single i t) v := by
  let P : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hcoord : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) P x := by
    change HasFDerivAt P P x
    exact P.hasFDerivAt
  have hpair : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ (y, WithLp.ofLp y i - t))
      (hartogsextDiagCLM i) x := by
    change HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦
      (y, WithLp.ofLp y i - t))
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))).prod P) x
    have hpair' := (hasFDerivAt_id x).prodMk (hcoord.sub_const t)
    apply hpair'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hsliceDiff := (hartogsext_contDiff_uncurry_slice hg i).differentiable (by norm_num)
  have hleft := (hsliceDiff (x, WithLp.ofLp x i - t)).hasFDerivAt.comp x hpair
  have hright : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦
        g (y - EuclideanSpace.single i t))
      (fderiv ℝ g (x - EuclideanSpace.single i t)) x := by
    have hright' := (hg.differentiable (by norm_num)
      (x - EuclideanSpace.single i t)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const (EuclideanSpace.single i t))
    apply hright'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hleft' : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦
        g (y - EuclideanSpace.single i t))
      ((fderiv ℝ (Function.uncurry (hartogsextSlice i g))
        (x, WithLp.ofLp x i - t)).comp (hartogsextDiagCLM i)) x := by
    apply hleft.congr_of_eventuallyEq
    filter_upwards with y
    exact congrArg g (hartogsextReplace_sub i y t).symm
  have hmaps := hleft'.unique hright
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hmaps

private theorem hartogsext_fderiv_partialCauchyGreen_apply
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (hartogsextPartialCauchyGreen i g) x v =
      ∫ t : ℂ, hartogsextCauchyGreenKernel t *
        fderiv ℝ g (x - EuclideanSpace.single i t) v := by
  obtain ⟨R, hRpos, hsupport⟩ := hartogsext_slice_uniform_support hgc i
  let k : Set ℂ := Metric.closedBall 0 R
  have hk : IsCompact k := isCompact_closedBall (0 : ℂ) R
  have hparam := hartogsext_contDiff_uncurry_slice hg i
  have hq := hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.mul ℝ ℂ) isOpen_univ hk
    (fun p z hp hz ↦ hsupport p z hz)
    hartogsext_cauchyGreenKernel_locallyIntegrable hparam.contDiffOn
    (x, WithLp.ofLp x i) (Set.mem_univ x)
  let P : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hcoord : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) P x := by
    change HasFDerivAt P P x
    exact P.hasFDerivAt
  have hdiag : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ (y, WithLp.ofLp y i))
      (hartogsextDiagCLM i) x := by
    change HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦
      (y, WithLp.ofLp y i))
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))).prod P) x
    have hdiag' := (hasFDerivAt_id x).prodMk hcoord
    apply hdiag'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hcomp := hq.comp x hdiag
  have hcomp' : HasFDerivAt (hartogsextPartialCauchyGreen i g)
      (((hartogsextCauchyGreenKernel ⋆[
        (ContinuousLinearMap.mul ℝ ℂ).precompR
          (EuclideanSpace ℂ (Fin n) × ℂ), volume]
          fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t))
        (WithLp.ofLp x i)).comp (hartogsextDiagCLM i)) x := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  rw [hcomp'.fderiv, ContinuousLinearMap.comp_apply]
  have hDcont : Continuous
      (fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t)) :=
    (hparam.continuous_fderiv (by norm_num)).comp
      (continuous_const.prodMk continuous_id)
  have hDcompact : HasCompactSupport
      (fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact hk
    intro t ht
    by_contra htk
    have hevent : Filter.EventuallyEq (nhds (x, t))
        (Function.uncurry (hartogsextSlice i g)) (fun _ ↦ 0) := by
      filter_upwards [((isOpen_univ.prod hk.isClosed.isOpen_compl).mem_nhds
        ⟨Set.mem_univ x, htk⟩)] with q hqmem
      exact hsupport q.1 q.2 hqmem.2
    have hzero : fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t) = 0 :=
      (hasFDerivAt_zero_of_eventually_const (0 : ℂ) hevent).fderiv
    exact ht hzero
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hDcompact hDcont
    (WithLp.ofLp x i) (hartogsextDiagCLM i v)]
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  rw [hartogsext_fderiv_uncurry_slice_diag hg i x v t]
  exact ContinuousLinearMap.mul_apply' ℝ ℂ _ _

private theorem hartogsext_continuous_replace_right
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    Continuous (hartogsextReplace i x) := by
  unfold hartogsextReplace
  rw [show (fun z : ℂ ↦ x + EuclideanSpace.single i (z - WithLp.ofLp x i)) =
      fun z ↦ x + (z - WithLp.ofLp x i) • EuclideanSpace.single i 1 by
    funext z
    rw [hartogsext_single_eq_smul]]
  fun_prop

private theorem hartogsext_integrable_kernel_fderiv
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) :
    Integrable (fun t : ℂ ↦ hartogsextCauchyGreenKernel t *
      fderiv ℝ g (x - EuclideanSpace.single i t) v) := by
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun y ↦ fderiv ℝ g y v
  have hac : HasCompactSupport a := hgc.fderiv_apply ℝ v
  have ha : Continuous a :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨R, hRpos, hsupp⟩ := hartogsext_slice_uniform_support hac i
  have hsliceCompact : HasCompactSupport (hartogsextSlice i a x) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) R)
    intro z hz
    by_contra hzb
    exact hz (hsupp x z hzb)
  have hsliceContinuous : Continuous (hartogsextSlice i a x) :=
    ha.comp (hartogsext_continuous_replace_right i x)
  have hexists := hsliceCompact.convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hsliceContinuous
    (WithLp.ofLp x i)
  apply hexists.congr
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  change hartogsextCauchyGreenKernel t *
      fderiv ℝ g (hartogsextReplace i x (WithLp.ofLp x i - t)) v =
    hartogsextCauchyGreenKernel t *
      fderiv ℝ g (x - EuclideanSpace.single i t) v
  rw [hartogsextReplace_sub]

private theorem hartogsext_barPartial_partialCauchyGreen
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i j : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial j (hartogsextPartialCauchyGreen i g) x =
      hartogsextPartialCauchyGreen i (hartogsextBarPartial j g) x := by
  rw [hartogsextBarPartial]
  rw [hartogsext_fderiv_partialCauchyGreen_apply hgc hg i x
    (EuclideanSpace.single j 1)]
  rw [hartogsext_fderiv_partialCauchyGreen_apply hgc hg i x
    (EuclideanSpace.single j Complex.I)]
  unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
  simp only [convolution_def]
  have h1 := hartogsext_integrable_kernel_fderiv hgc hg i x
    (EuclideanSpace.single j 1)
  have hI := hartogsext_integrable_kernel_fderiv hgc hg i x
    (EuclideanSpace.single j Complex.I)
  rw [← integral_const_mul]
  rw [← integral_add h1 (hI.const_mul Complex.I), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  change _ = hartogsextCauchyGreenKernel t *
    hartogsextBarPartial j g
      (hartogsextReplace i x (WithLp.ofLp x i - t))
  rw [hartogsextReplace_sub]
  simp only [hartogsextBarPartial]
  ring

/-- A complex-differentiable function has vanishing Wirtinger derivative. -/
theorem barDeriv_eq_zero_of_differentiableAt
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : barDeriv f z = 0 := by
  rw [barDeriv, hf.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [show Complex.I = Complex.I • (1 : ℂ) by simp, map_smul]
  simp only [smul_eq_mul]
  rw [mul_one, ← mul_assoc, Complex.I_mul_I]
  simp

/-- A real-differentiable function with vanishing Wirtinger derivative is complex
differentiable. -/
theorem differentiableAt_of_barDeriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hbar : barDeriv f z = 0) : DifferentiableAt ℂ f z := by
  let L : ℂ →L[ℝ] ℂ := fderiv ℝ f z
  have hsum : L 1 + Complex.I * L Complex.I = 0 := by
    have htwo : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hbar).resolve_left htwo
  have hIL : L Complex.I = Complex.I * L 1 := by
    have hneg : Complex.I * L Complex.I = -L 1 :=
      eq_neg_of_add_eq_zero_right hsum
    calc
      L Complex.I = (-(Complex.I * Complex.I)) * L Complex.I := by
        rw [Complex.I_mul_I]
        simp
      _ = -Complex.I * (Complex.I * L Complex.I) := by ring
      _ = -Complex.I * (-L 1) := by rw [hneg]
      _ = Complex.I * L 1 := by ring
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ (L 1)
  apply (differentiableAt_iff_restrictScalars ℝ hf).2
  refine ⟨A, ?_⟩
  ext x
  have hx : x = x.re • (1 : ℂ) + x.im • Complex.I := by
    simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    exact Complex.re_add_im x |>.symm
  have hLx : L x = x * L 1 := by
    rw [hx, map_add, map_smul, map_smul, hIL]
    simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    rw [← mul_assoc, ← add_mul]
  rw [hLx]
  change L 1 * x = x * L 1
  exact mul_comm _ _

private theorem hartogsext_differentiableAt_of_barPartial_eq_zero
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hbar : ∀ i, hartogsextBarPartial i f x = 0) : DifferentiableAt ℂ f x := by
  let L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ := fderiv ℝ f x
  have hLI (i : Fin n) : L (EuclideanSpace.single i Complex.I) =
      Complex.I * L (EuclideanSpace.single i 1) := by
    have hsum : L (EuclideanSpace.single i 1) +
        Complex.I * L (EuclideanSpace.single i Complex.I) = 0 := by
      have htwo : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (hbar i)).resolve_left htwo
    have hneg : Complex.I * L (EuclideanSpace.single i Complex.I) =
        -L (EuclideanSpace.single i 1) := eq_neg_of_add_eq_zero_right hsum
    calc
      L (EuclideanSpace.single i Complex.I) =
          (-(Complex.I * Complex.I)) * L (EuclideanSpace.single i Complex.I) := by
        rw [Complex.I_mul_I]
        simp
      _ = -Complex.I *
          (Complex.I * L (EuclideanSpace.single i Complex.I)) := by ring
      _ = -Complex.I * (-L (EuclideanSpace.single i 1)) := by rw [hneg]
      _ = Complex.I * L (EuclideanSpace.single i 1) := by ring
  have hLsingle (i : Fin n) (z : ℂ) :
      L (z • EuclideanSpace.single i 1) =
        z * L (EuclideanSpace.single i 1) := by
    have hz : z • EuclideanSpace.single i 1 =
        z.re • EuclideanSpace.single i 1 +
          z.im • EuclideanSpace.single i Complex.I := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_eq_same,
          RCLike.real_smul_eq_coe_mul, smul_eq_mul, mul_one]
        exact Complex.re_add_im z |>.symm
      · simp [hji]
    rw [hz, map_add, map_smul, map_smul, hLI]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc, ← add_mul]
    exact congrArg (fun w : ℂ ↦ w * L (EuclideanSpace.single i 1))
      (Complex.re_add_im z)
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    ∑ i : Fin n, ((ContinuousLinearMap.mul ℂ ℂ).flip
      (L (EuclideanSpace.single i 1))).comp (EuclideanSpace.proj (𝕜 := ℂ) i)
  apply (differentiableAt_iff_restrictScalars ℝ hf).2
  refine ⟨A, ?_⟩
  ext y
  have hy : y = ∑ i : Fin n,
      WithLp.ofLp y i • EuclideanSpace.single i 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr y).symm
  calc
    A.restrictScalars ℝ y = ∑ i : Fin n,
        WithLp.ofLp y i * L (EuclideanSpace.single i 1) := by
      simp only [A, ContinuousLinearMap.coe_restrictScalars',
        sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
        EuclideanSpace.coe_proj]
    _ = ∑ i : Fin n, L (WithLp.ofLp y i • EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hLsingle i (WithLp.ofLp y i)).symm
    _ = L y := by rw [← map_sum, ← hy]

private theorem hartogsext_cauchyGreenTransform_hasFDerivAt
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    HasFDerivAt (hartogsextCauchyGreenTransform g)
      ((hartogsextCauchyGreenKernel ⋆[
        (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ, volume] fderiv ℝ g) z) z := by
  exact hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hg z

private theorem hartogsext_barDeriv_cauchyGreenTransform
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    barDeriv (hartogsextCauchyGreenTransform g) z =
      (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] barDeriv g) z := by
  have hD := hartogsext_cauchyGreenTransform_hasFDerivAt hgc hg z
  have hDf : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hconv_one := (hgc.fderiv_apply ℝ (1 : ℂ)).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ) hartogsext_cauchyGreenKernel_locallyIntegrable
    ((continuous_clm_apply.mp hDf) 1)
  have hconv_I := (hgc.fderiv_apply ℝ Complex.I).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ) hartogsext_cauchyGreenKernel_locallyIntegrable
    ((continuous_clm_apply.mp hDf) Complex.I)
  rw [barDeriv, hD.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable (hgc.fderiv ℝ) hDf z 1]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable (hgc.fderiv ℝ) hDf z Complex.I]
  simp only [convolution_def]
  change (2 : ℂ)⁻¹ *
      ((∫ t, hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) 1) +
        Complex.I * ∫ t, hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) Complex.I) =
    ∫ t, hartogsextCauchyGreenKernel t * barDeriv g (z - t)
  have hone : Integrable
      (fun t ↦ hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) 1) volume :=
    hconv_one z
  have hI : Integrable
      (fun t ↦ hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) Complex.I) volume :=
    hconv_I z
  rw [← integral_const_mul]
  rw [← integral_add hone (hI.const_mul Complex.I), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [barDeriv]
  ring

private noncomputable def hartogsextUnitCircle (θ : ℝ) : ℂ :=
  Real.cos θ + Real.sin θ * Complex.I

private theorem hartogsextUnitCircle_ne_zero (θ : ℝ) : hartogsextUnitCircle θ ≠ 0 := by
  rw [← norm_ne_zero_iff]
  simp [hartogsextUnitCircle, Complex.norm_cos_add_sin_mul_I]

private theorem hartogsext_barDeriv_polar_identity
    (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) (hr : r ≠ 0) :
    (hartogsextUnitCircle θ)⁻¹ *
        ((2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I)) =
      (2 : ℂ)⁻¹ *
        (L (hartogsextUnitCircle θ) +
          Complex.I * (r : ℂ)⁻¹ *
            L ((r : ℂ) * Complex.I * hartogsextUnitCircle θ)) := by
  let c := Real.cos θ
  let s := Real.sin θ
  let e := hartogsextUnitCircle θ
  have heq : e = c • (1 : ℂ) + s • Complex.I := by
    simp [e, c, s, hartogsextUnitCircle, RCLike.real_smul_eq_coe_mul]
  have hIeq : Complex.I * e = (-s) • (1 : ℂ) + c • Complex.I := by
    rw [heq]
    simp only [mul_add, mul_smul_comm, Complex.I_mul_I, mul_one, smul_neg]
    simp only [RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  have hLe : L e = c • L 1 + s • L Complex.I := by
    rw [heq, map_add, map_smul, map_smul]
  have hLrIe : L ((r : ℂ) * Complex.I * e) =
      r • ((-s) • L 1 + c • L Complex.I) := by
    have hrIe : (r : ℂ) * Complex.I * e = r • (Complex.I * e) := by
      simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
    rw [hrIe, map_smul, hIeq, map_add, map_smul, map_smul]
  have heinv : e⁻¹ = (c : ℂ) - s * Complex.I := by
    have heexp : e = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I]
      simp [e, hartogsextUnitCircle]
    rw [heexp, ← Complex.exp_neg]
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I]
    dsimp [c, s]
    simp [sub_eq_add_neg]
  rw [hLe, hLrIe]
  rw [heinv]
  simp only [RCLike.real_smul_eq_coe_mul]
  push_cast
  field_simp [hr]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  simp only [sub_eq_add_neg]
  ac_rfl

private theorem hartogsext_barDeriv_polar_identity'
    (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) (hr : r ≠ 0) :
    (hartogsextUnitCircle θ)⁻¹ *
        ((2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I)) =
      (2 : ℂ)⁻¹ *
        (L (hartogsextUnitCircle θ) +
          Complex.I * L (Complex.I * hartogsextUnitCircle θ)) := by
  rw [hartogsext_barDeriv_polar_identity L r θ hr]
  congr 2
  have hinput : (r : ℂ) * Complex.I * hartogsextUnitCircle θ =
      r • (Complex.I * hartogsextUnitCircle θ) := by
    simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
  rw [hinput, map_smul]
  simp only [RCLike.real_smul_eq_coe_mul]
  field_simp [hr]
  rfl

private theorem hartogsext_hasDerivAt_polar_radius
    {h : ℂ → ℂ} (hh : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun ρ : ℝ ↦ h ((ρ : ℂ) * hartogsextUnitCircle θ))
      (fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) r := by
  have hin : HasDerivAt (fun ρ : ℝ ↦ (ρ : ℂ) * hartogsextUnitCircle θ)
      (hartogsextUnitCircle θ) r := by
    convert ((hasDerivAt_id (𝕜 := ℝ) (x := r)).smul_const
      (hartogsextUnitCircle θ)) using 1 <;> simp [RCLike.real_smul_eq_coe_mul]
  exact (hh ((r : ℂ) * hartogsextUnitCircle θ)).hasFDerivAt.comp_hasDerivAt r hin

private theorem hartogsext_hasDerivAt_polar_angle
    {h : ℂ → ℂ} (hh : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun φ : ℝ ↦ h ((r : ℂ) * hartogsextUnitCircle φ))
      (fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        ((r : ℂ) * Complex.I * hartogsextUnitCircle θ)) θ := by
  have hcircle : (fun φ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle φ) = circleMap 0 r := by
    funext φ
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
  have hin : HasDerivAt (fun φ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle φ)
      ((r : ℂ) * Complex.I * hartogsextUnitCircle θ) θ := by
    rw [hcircle]
    convert hasDerivAt_circleMap 0 r θ using 1
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
    ring
  exact (hh ((r : ℂ) * hartogsextUnitCircle θ)).hasFDerivAt.comp_hasDerivAt θ hin

private theorem hartogsext_integral_inv_mul_barDeriv_eq_polar (h : ℂ → ℂ) :
    (∫ z : ℂ, z⁻¹ * barDeriv h z) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (hartogsextUnitCircle p.2)⁻¹ *
          barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2) := by
  rw [← Complex.integral_comp_polarCoord_symm (fun z : ℂ ↦ z⁻¹ * barDeriv h z)]
  change (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * barDeriv h (Complex.polarCoord.symm p))) = _
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [Complex.polarCoord_symm_apply]
  change (p.1 : ℂ) *
      (((p.1 : ℂ) * hartogsextUnitCircle p.2)⁻¹ *
        barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) =
    (hartogsextUnitCircle p.2)⁻¹ *
      barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
  field_simp [ne_of_gt hp.1, hartogsextUnitCircle_ne_zero]

private theorem hartogsext_integrableOn_polar_fderiv
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h)
    {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (v p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  let φ : ℝ × ℝ → ℂ := fun p ↦
    fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (v p.2)
  have hDf : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have hpoint : Continuous (fun p : ℝ × ℝ ↦
      (p.1 : ℂ) * hartogsextUnitCircle p.2) := by
    unfold hartogsextUnitCircle
    fun_prop
  have hφ : Continuous φ :=
    (hDf.comp hpoint).clm_apply (hv.comp continuous_snd)
  obtain ⟨R, hRpos, hR⟩ := hhc.isCompact.isBounded.exists_pos_norm_lt
  let q : Set (ℝ × ℝ) := Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi
  have hq : IsCompact q := isCompact_Icc.prod isCompact_Icc
  have hφq : IntegrableOn φ q := hφ.continuousOn.integrableOn_compact hq
  have hind : Integrable (q.indicator φ) := hφq.integrable_indicator hq.measurableSet
  apply hind.integrableOn.congr_fun _ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  by_cases hpR : p.1 ≤ R
  · rw [Set.indicator_of_mem]
    exact ⟨⟨hp.1.le, hpR⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  · rw [Set.indicator_of_notMem]
    · dsimp [φ]
      have hz : (p.1 : ℂ) * hartogsextUnitCircle p.2 ∉ tsupport h := by
        intro hz
        have hnorm := hR _ hz
        have heq : ‖(p.1 : ℂ) * hartogsextUnitCircle p.2‖ = p.1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1]
          simp [hartogsextUnitCircle, Complex.norm_cos_add_sin_mul_I]
        rw [heq] at hnorm
        exact hpR hnorm.le
      rw [fderiv_of_notMem_tsupport ℝ hz]
      simp
    · intro hpq
      exact hpR hpq.1.2

private theorem hartogsext_integral_polar_radius
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (θ : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) =
        -h 0 := by
  let q : ℝ → ℂ := fun r ↦ h ((r : ℂ) * hartogsextUnitCircle θ)
  have hline : ContDiff ℝ 1 (fun r : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) := by
    simpa [RCLike.real_smul_eq_coe_mul] using
      (contDiff_id.smul_const (hartogsextUnitCircle θ) :
        ContDiff ℝ 1 (fun r : ℝ ↦ r • hartogsextUnitCircle θ))
  have hq : ContDiff ℝ 1 q := by
    simpa only [q, Function.comp_def] using hh.comp hline
  obtain ⟨R, hRpos, hR⟩ := hhc.isCompact.isBounded.exists_pos_norm_lt
  have hqc : HasCompactSupport q := by
    refine HasCompactSupport.of_support_subset_isCompact
      (show IsCompact (Set.Icc (-R) R) from isCompact_Icc) ?_
    intro r hr
    have hz : (r : ℂ) * hartogsextUnitCircle θ ∈ tsupport h :=
      subset_closure hr
    have hnorm := hR _ hz
    have habs : |r| < R := by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, hartogsextUnitCircle,
        Complex.norm_cos_add_sin_mul_I] using hnorm
    exact ⟨(neg_lt_of_abs_lt habs).le, (lt_of_abs_lt habs).le⟩
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) =
      ∫ r in Set.Ioi (0 : ℝ), deriv q r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact (hartogsext_hasDerivAt_polar_radius (hh.differentiable (by norm_num)) r θ).deriv.symm
    _ = -q 0 := hqc.integral_Ioi_deriv_eq hq 0
    _ = -h 0 := by simp [q]

private theorem hartogsext_integral_polar_angle
    {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        (Complex.I * hartogsextUnitCircle θ)) = 0 := by
  let q : ℝ → ℂ := fun θ ↦ h ((r : ℂ) * hartogsextUnitCircle θ)
  have hcircle : (fun θ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) = circleMap 0 r := by
    funext θ
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
  have hinner : ContDiff ℝ 1 (fun θ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) := by
    rw [hcircle]
    exact contDiff_circleMap 0 r
  have hq : ContDiff ℝ 1 q := by
    simpa only [q, Function.comp_def] using hh.comp hinner
  have hderiv (θ : ℝ) : deriv q θ =
      fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        ((r : ℂ) * Complex.I * hartogsextUnitCircle θ) :=
    (hartogsext_hasDerivAt_polar_angle (hh.differentiable (by norm_num)) r θ).deriv
  have hrewrite (θ : ℝ) :
      Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
          (Complex.I * hartogsextUnitCircle θ) =
        (Complex.I * (r : ℂ)⁻¹) * deriv q θ := by
    rw [hderiv]
    have hinput : (r : ℂ) * Complex.I * hartogsextUnitCircle θ =
        r • (Complex.I * hartogsextUnitCircle θ) := by
      simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
    rw [hinput, map_smul]
    simp only [RCLike.real_smul_eq_coe_mul]
    field_simp [hr.ne']
    exact mul_comm _ _
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
          (Complex.I * hartogsextUnitCircle θ)) =
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (Complex.I * (r : ℂ)⁻¹) * deriv q θ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          exact hrewrite θ
    _ = (Complex.I * (r : ℂ)⁻¹) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, deriv q θ := by
      rw [integral_const_mul]
    _ = (Complex.I * (r : ℂ)⁻¹) *
        ∫ θ in (-Real.pi)..Real.pi, deriv q θ := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    _ = (Complex.I * (r : ℂ)⁻¹) * (q Real.pi - q (-Real.pi)) := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hq.contDiffOn
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    _ = 0 := by
      simp [q, hartogsextUnitCircle]

private theorem hartogsext_integral_inv_mul_barDeriv
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) :
    (∫ z : ℂ, z⁻¹ * barDeriv h z) = -(Real.pi : ℂ) * h 0 := by
  let radial : ℝ × ℝ → ℂ := fun p ↦
    fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (hartogsextUnitCircle p.2)
  let angular : ℝ × ℝ → ℂ := fun p ↦
    Complex.I * fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
      (Complex.I * hartogsextUnitCircle p.2)
  have hunit : Continuous hartogsextUnitCircle := by
    unfold hartogsextUnitCircle
    fun_prop
  have hradial : IntegrableOn radial
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    exact hartogsext_integrableOn_polar_fderiv hhc hh hunit
  have hangbase : IntegrableOn
      (fun p : ℝ × ℝ ↦ fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
        (Complex.I * hartogsextUnitCircle p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    apply hartogsext_integrableOn_polar_fderiv hhc hh
      (v := fun θ ↦ Complex.I * hartogsextUnitCircle θ)
    exact continuous_const.mul hunit
  have hangular : IntegrableOn angular
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    hangbase.const_mul Complex.I
  have hradialIntegral :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) =
        -(2 * Real.pi : ℝ) * h 0 := by
    calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) =
          ∫ p in Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ), radial p.swap :=
        (setIntegral_prod_swap (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi) radial).symm
      _ = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ∫ r in Set.Ioi (0 : ℝ), radial (r, θ) := by
        simpa only [Measure.volume_eq_prod, Function.comp_apply,
          Prod.swap_prod_mk] using
          (setIntegral_prod (radial ∘ Prod.swap) hradial.swap)
      _ = ∫ _θ in Set.Ioo (-Real.pi) Real.pi, -h 0 := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ hθ
        exact hartogsext_integral_polar_radius hhc hh θ
      _ = -(2 * Real.pi : ℝ) * h 0 := by
        have hpi : 0 ≤ Real.pi - -Real.pi := by linarith [Real.pi_pos]
        have hlength : Real.pi - -Real.pi = 2 * Real.pi := by ring
        rw [integral_const]
        simp only [Measure.restrict_apply_univ, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal hpi, RCLike.real_smul_eq_coe_mul]
        rw [hlength]
        push_cast
        rw [neg_mul, mul_neg]
        rfl
  have hangularIntegral :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) = 0 := by
    calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) =
          ∫ r in Set.Ioi (0 : ℝ),
            ∫ θ in Set.Ioo (-Real.pi) Real.pi, angular (r, θ) := by
        simpa only [Measure.volume_eq_prod] using
          (setIntegral_prod angular hangular)
      _ = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro r hr
        exact hartogsext_integral_polar_angle hh hr
  rw [hartogsext_integral_inv_mul_barDeriv_eq_polar]
  calc
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (hartogsextUnitCircle p.2)⁻¹ *
          barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (2 : ℂ)⁻¹ * (radial p + angular p) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact hartogsext_barDeriv_polar_identity'
        (fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) p.1 p.2
          (ne_of_gt hp.1)
    _ = (2 : ℂ)⁻¹ *
        ((∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) +
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) := by
      rw [integral_const_mul, integral_add hradial hangular]
    _ = -(Real.pi : ℂ) * h 0 := by
      rw [hradialIntegral, hangularIntegral]
      push_cast
      ring

private theorem hartogsext_barDeriv_const_sub
    {g : ℂ → ℂ} (hg : Differentiable ℝ g) (z t : ℂ) :
    barDeriv (fun w ↦ g (z - w)) t = -barDeriv g (z - t) := by
  have hinner : HasFDerivAt (fun w : ℂ ↦ z - w) (-(1 : ℂ →L[ℝ] ℂ)) t :=
    (hasFDerivAt_id t).const_sub z
  have hcomp := (hg (z - t)).hasFDerivAt.comp t hinner
  have hcomp' : HasFDerivAt (fun w ↦ g (z - w))
      (fderiv ℝ g (z - t) ∘L (-(1 : ℂ →L[ℝ] ℂ))) t := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with w
    rfl
  rw [barDeriv, barDeriv, hcomp'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, one_apply_eq_self, map_neg]
  ring

private theorem hartogsext_integral_inv_mul_barDeriv_const_sub
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    (∫ t : ℂ, t⁻¹ * barDeriv g (z - t)) = (Real.pi : ℂ) * g z := by
  let h : ℂ → ℂ := fun t ↦ g (z - t)
  have hhc : HasCompactSupport h := by
    simpa only [h, Function.comp_def, Homeomorph.subLeft,
      Homeomorph.homeomorph_mk_coe, Equiv.subLeft_apply] using
      hgc.comp_homeomorph (Homeomorph.subLeft z)
  have hh : ContDiff ℝ 1 h := by
    have hinner : ContDiff ℝ 1 (fun t : ℂ ↦ z - t) :=
      contDiff_const.sub contDiff_id
    simpa only [h, Function.comp_def] using hg.comp hinner
  have hcore := hartogsext_integral_inv_mul_barDeriv hhc hh
  calc
    (∫ t : ℂ, t⁻¹ * barDeriv g (z - t)) =
        -(∫ t : ℂ, t⁻¹ * barDeriv h t) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with t
      rw [hartogsext_barDeriv_const_sub (hg.differentiable (by norm_num))]
      ring
    _ = -(-(Real.pi : ℂ) * h 0) := by rw [hcore]
    _ = (Real.pi : ℂ) * g z := by simp [h]

private theorem hartogsext_barDeriv_cauchyGreenTransform_eq
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    barDeriv (hartogsextCauchyGreenTransform g) z = g z := by
  rw [hartogsext_barDeriv_cauchyGreenTransform hgc hg]
  simp only [convolution_def, hartogsextCauchyGreenKernel]
  calc
    (∫ t : ℂ, ((Real.pi : ℂ)⁻¹ * t⁻¹) * barDeriv g (z - t)) =
        (Real.pi : ℂ)⁻¹ * ∫ t : ℂ, t⁻¹ * barDeriv g (z - t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ac_rfl
    _ = g z := by
      rw [hartogsext_integral_inv_mul_barDeriv_const_sub hgc hg z]
      field_simp [ne_of_gt Real.pi_pos]

/-- A compactly supported `C¹` function on `ℂ` is a Wirtinger derivative. -/
theorem exists_differentiable_barDeriv_eq_of_hasCompactSupport
    {g : ℂ → ℂ} (hg : Differentiable ℝ g) (hDg : Continuous (fderiv ℝ g))
    (hgc : HasCompactSupport g) :
    ∃ u : ℂ → ℂ, Differentiable ℝ u ∧ ∀ z, barDeriv u z = g z := by
  have hg' : ContDiff ℝ 1 g := contDiff_one_iff_fderiv.mpr ⟨hg, hDg⟩
  refine ⟨hartogsextCauchyGreenTransform g, ?_, ?_⟩
  · intro z
    exact (hartogsext_cauchyGreenTransform_hasFDerivAt hgc hg' z).differentiableAt
  · exact hartogsext_barDeriv_cauchyGreenTransform_eq hgc hg'

private theorem hartogsext_barPartial_partialCauchyGreen_self
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i (hartogsextPartialCauchyGreen i g) x = g x := by
  have hsc := hartogsext_hasCompactSupport_slice hgc i x
  have hsd := hartogsext_contDiff_slice hg i x
  have hfun : barDeriv (hartogsextSlice i g x) =
      hartogsextSlice i (hartogsextBarPartial i g) x := by
    funext z
    exact hartogsext_barDeriv_slice hg i x z
  calc
    hartogsextBarPartial i (hartogsextPartialCauchyGreen i g) x =
        hartogsextPartialCauchyGreen i (hartogsextBarPartial i g) x :=
      hartogsext_barPartial_partialCauchyGreen hgc hg i i x
    _ = (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          barDeriv (hartogsextSlice i g x)) (WithLp.ofLp x i) := by
      unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
      rw [hfun]
    _ = barDeriv (hartogsextCauchyGreenTransform (hartogsextSlice i g x))
        (WithLp.ofLp x i) :=
      (hartogsext_barDeriv_cauchyGreenTransform hsc hsd _).symm
    _ = hartogsextSlice i g x (WithLp.ofLp x i) :=
      hartogsext_barDeriv_cauchyGreenTransform_eq hsc hsd _
    _ = g x := by
      unfold hartogsextSlice
      rw [hartogsextReplace_self]

private theorem hartogsext_partialCauchyGreen_eq_zero_of_coord
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (i j : Fin n) (hji : j ≠ i) {R : ℝ}
    (hR : ∀ y ∈ tsupport g, ‖y‖ < R)
    {x : EuclideanSpace ℂ (Fin n)} (hx : R ≤ ‖WithLp.ofLp x j‖) :
    hartogsextPartialCauchyGreen i g x = 0 := by
  unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
  simp only [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  have hslice :
      hartogsextSlice i g x (WithLp.ofLp x i - t) = 0 := by
    apply Classical.byContradiction
    intro hne
    have hy : hartogsextReplace i x (WithLp.ofLp x i - t) ∈ tsupport g :=
      subset_tsupport g hne
    have hcoord := PiLp.norm_apply_le
      (hartogsextReplace i x (WithLp.ofLp x i - t)) j
    have heq : WithLp.ofLp (hartogsextReplace i x
        (WithLp.ofLp x i - t)) j = WithLp.ofLp x j := by
      simp [hartogsextReplace, hji]
    rw [heq] at hcoord
    exact (not_lt_of_ge hx) (hcoord.trans_lt (hR _ hy))
  simp [hslice]

private theorem hartogsext_hasCompactSupport_partialCauchyGreen
    {n : ℕ} (hn : 2 ≤ n)
    {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    {h : Fin n → EuclideanSpace ℂ (Fin n) → ℂ}
    (hhc : ∀ j, HasCompactSupport (h j))
    (hbar : ∀ j x,
      hartogsextBarPartial j (hartogsextPartialCauchyGreen i g) x = h j x) :
    HasCompactSupport (hartogsextPartialCauchyGreen i g) := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨Rg, hRg_pos, hRg⟩ := hgc.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Rh, hRh_pos, hRh⟩ := (hhc j).isCompact.isBounded.exists_pos_norm_lt
  let u := hartogsextPartialCauchyGreen i g
  have hu : ContDiff ℝ 1 u := hartogsext_contDiff_partialCauchyGreen hgc hg i
  have htransverse {x : EuclideanSpace ℂ (Fin n)} {k : Fin n}
      (hki : k ≠ i) (hx : Rg ≤ ‖WithLp.ofLp x k‖) : u x = 0 := by
    exact hartogsext_partialCauchyGreen_eq_zero_of_coord i k hki hRg hx
  have hfirst {x : EuclideanSpace ℂ (Fin n)}
      (hx : Rh ≤ ‖WithLp.ofLp x i‖) : u x = 0 := by
    let q : ℂ → ℂ := hartogsextSlice j u x
    have hq_contDiff : ContDiff ℝ 1 q := hartogsext_contDiff_slice hu j x
    have hq_bar (z : ℂ) : barDeriv q z = 0 := by
      rw [show barDeriv q z =
        hartogsextBarPartial j u (hartogsextReplace j x z) by
          exact hartogsext_barDeriv_slice hu j x z]
      rw [hbar]
      apply Classical.byContradiction
      intro hne
      have hy : hartogsextReplace j x z ∈ tsupport (h j) :=
        subset_tsupport (h j) hne
      have hcoord := PiLp.norm_apply_le (hartogsextReplace j x z) i
      have heq : WithLp.ofLp (hartogsextReplace j x z) i = WithLp.ofLp x i := by
        simp [hartogsextReplace, Ne.symm hji]
      rw [heq] at hcoord
      exact (not_lt_of_ge hx) (hcoord.trans_lt (hRh _ hy))
    have hq_diff : Differentiable ℂ q := by
      intro z
      exact differentiableAt_of_barDeriv_eq_zero
        (hq_contDiff.differentiable (by norm_num) z) (hq_bar z)
    let z₀ : ℂ := ((Rg + 1 : ℝ) : ℂ)
    have hz₀ : Rg < ‖z₀‖ := by
      change Rg < ‖((Rg + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hevent : Filter.EventuallyEq (nhds z₀) q (fun _ ↦ 0) := by
      have hopen : IsOpen {z : ℂ | Rg < ‖z‖} :=
        isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hz₀] with z hz
      apply htransverse hji
      simpa only [q, hartogsextReplace_apply] using hz.le
    have hq_an : AnalyticOnNhd ℂ q Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hq_diff
    have hq_zero : q = fun _ ↦ 0 :=
      hq_an.eq_of_eventuallyEq analyticOnNhd_const hevent
    have hself := congrFun hq_zero (WithLp.ofLp x j)
    simpa only [q, hartogsextSlice, hartogsextReplace_self] using hself
  let R : ℝ := max Rg Rh
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) ((n : ℝ) * R))
  intro x hx_support
  have hcoord (k : Fin n) : ‖WithLp.ofLp x k‖ ≤ R := by
    by_cases hki : k = i
    · subst k
      by_contra hxR
      have hzero := hfirst ((le_max_right Rg Rh).trans (le_of_not_ge hxR))
      exact hx_support hzero
    · by_contra hxR
      have hzero := htransverse hki
        ((le_max_left Rg Rh).trans (le_of_not_ge hxR))
      exact hx_support hzero
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx_repr : x = ∑ k : Fin n,
      WithLp.ofLp x k • EuclideanSpace.single k 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr x).symm
  calc
    ‖x‖ = ‖∑ k : Fin n,
        WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)‖ :=
      congrArg norm hx_repr
    _ ≤ ∑ k : Fin n,
        ‖WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)‖ := by
      simpa only [Finset.sum_filter] using
        (norm_sum_le Finset.univ (fun k : Fin n ↦
          WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)))
    _ = ∑ k : Fin n, ‖WithLp.ofLp x k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    _ ≤ ∑ _k : Fin n, R := Finset.sum_le_sum fun k hk ↦ hcoord k
    _ = (n : ℝ) * R := by simp

private theorem hartogsext_eqOn_of_differentiableOn_of_isConnected
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hs_open : IsOpen s) (hs_conn : IsConnected s)
    (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    {x₀ : EuclideanSpace ℂ (Fin n)} (hx₀ : x₀ ∈ s)
    (hfg : Filter.EventuallyEq (nhds x₀) f g) : Set.EqOn f g s := by
  set A : Set (EuclideanSpace ℂ (Fin n)) :=
    {x | ∃ o : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen o ∧ x ∈ o ∧ Set.EqOn f g o} with hA
  have hA_open : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨o, ho, hxo, heq⟩ := hx
    exact ⟨o, fun y hy ↦ ⟨o, ho, hy, heq⟩, ho, hxo⟩
  have hx₀A : x₀ ∈ A := by
    have hfg' : {x | f x = g x} ∈ nhds x₀ := hfg
    obtain ⟨o, ho_sub, ho_open, hx₀o⟩ := mem_nhds_iff.mp hfg'
    exact ⟨o, ho_open, hx₀o, fun x hx ↦ ho_sub hx⟩
  have hclosure : closure A ∩ s ⊆ A := by
    intro x hx
    obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.mp hs_open x hx.2
    obtain ⟨y, hy_ball, hyA⟩ :=
      mem_closure_iff_nhds.mp hx.1 (Metric.ball x r)
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    obtain ⟨o, ho_open, hyo, heq_o⟩ := hyA
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    intro z hz
    let v : EuclideanSpace ℂ (Fin n) := z - y
    let ℓ : ℂ → EuclideanSpace ℂ (Fin n) := fun t ↦ y + t • v
    have hℓ0 : ℓ 0 = y := by simp [ℓ]
    have hℓ1 : ℓ 1 = z := by simp [ℓ, v]
    have hℓ_diff : Differentiable ℂ ℓ := by
      exact (differentiable_id.smul_const v).const_add y
    have hℓ_cont : Continuous ℓ := hℓ_diff.continuous
    let D : Set ℂ := ℓ ⁻¹' Metric.ball x r
    have hD_open : IsOpen D := Metric.isOpen_ball.preimage hℓ_cont
    have h0D : (0 : ℂ) ∈ D := by
      change ℓ 0 ∈ Metric.ball x r
      rw [hℓ0]
      exact hy_ball
    have h1D : (1 : ℂ) ∈ D := by
      change ℓ 1 ∈ Metric.ball x r
      rw [hℓ1]
      exact hz
    have hD_convex : Convex ℝ D := by
      intro a ha b hb u w hu hw huw
      change ℓ (u • a + w • b) ∈ Metric.ball x r
      have haff : ℓ (u • a + w • b) = u • ℓ a + w • ℓ b := by
        simp only [ℓ]
        rw [smul_add, smul_add, add_smul, ← smul_assoc u a v,
          ← smul_assoc w b v]
        have hrearr :
            (u • y + (u • a) • v) + (w • y + (w • b) • v) =
              (u • y + w • y) + ((u • a) • v + (w • b) • v) := by
          abel
        rw [hrearr, ← add_smul u w y, huw, one_smul]
      rw [haff]
      exact (convex_ball x r) ha hb hu hw huw
    have hmaps : MapsTo ℓ D s := fun t ht ↦ hr_sub ht
    have hf_slice : DifferentiableOn ℂ (f ∘ ℓ) D :=
      hf.comp (hℓ_diff.differentiableOn (s := D)) hmaps
    have hg_slice : DifferentiableOn ℂ (g ∘ ℓ) D :=
      hg.comp (hℓ_diff.differentiableOn (s := D)) hmaps
    have hf_an : AnalyticOnNhd ℂ (f ∘ ℓ) D := hf_slice.analyticOnNhd hD_open
    have hg_an : AnalyticOnNhd ℂ (g ∘ ℓ) D := hg_slice.analyticOnNhd hD_open
    have hevent : Filter.EventuallyEq (nhds (0 : ℂ)) (f ∘ ℓ) (g ∘ ℓ) := by
      have htend : Filter.Tendsto ℓ (nhds (0 : ℂ)) (nhds y) := by
        simpa only [hℓ0] using hℓ_cont.tendsto 0
      filter_upwards [htend.eventually (ho_open.mem_nhds hyo)] with t ht
      exact heq_o ht
    have heqD := hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an
      hD_convex.isPreconnected h0D hevent
    simpa only [Function.comp_apply, hℓ1] using heqD h1D
  let T : Set s := Subtype.val ⁻¹' A
  have hT_open : IsOpen T := hA_open.preimage continuous_subtype_val
  have hT_closed : IsClosed T := by
    rw [isClosed_induced_iff]
    refine ⟨closure A, isClosed_closure, ?_⟩
    ext x
    constructor
    · intro hx
      exact hclosure ⟨hx, x.property⟩
    · intro hx
      exact subset_closure hx
  let _ : ConnectedSpace s := Subtype.connectedSpace hs_conn
  have hT_clopen : IsClopen T := ⟨hT_closed, hT_open⟩
  have hT_univ : T = Set.univ := hT_clopen.eq_univ ⟨⟨x₀, hx₀⟩, hx₀A⟩
  intro x hx
  have hxT : (⟨x, hx⟩ : s) ∈ T := by rw [hT_univ]; exact Set.mem_univ _
  obtain ⟨o, ho, hxo, heq⟩ := hxT
  exact heq hxo

private theorem hartogsext_exists_zero_germ
    {n : ℕ} (hn : 2 ≤ n)
    {U K : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {φ u : EuclideanSpace ℂ (Fin n) → ℂ}
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hKφ : K ⊆ tsupport φ) (hφne : (tsupport φ).Nonempty)
    (huc : HasCompactSupport u)
    (hu : DifferentiableOn ℂ u (tsupport φ)ᶜ) :
    ∃ y ∈ U \ K, Filter.EventuallyEq (nhds y) u (fun _ ↦ 0) ∧
      Filter.EventuallyEq (nhds y) φ (fun _ ↦ 0) := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hb : Bornology.IsBounded (tsupport φ ∪ tsupport u) :=
    hφc.isCompact.isBounded.union huc.isCompact.isBounded
  have hproper : tsupport φ ∪ tsupport u ≠ Set.univ := by
    intro heq
    apply NormedSpace.unbounded_univ ℝ (EuclideanSpace ℂ (Fin n))
    rwa [← heq]
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  have haφ : a ∉ tsupport φ := fun h ↦ ha (Or.inl h)
  have hau : a ∉ tsupport u := fun h ↦ ha (Or.inr h)
  obtain ⟨p, hpφ, hpdist⟩ :=
    hφc.isCompact.exists_infDist_eq_dist hφne a
  let d := dist a p
  have hd : 0 < d := by
    have hinf : 0 < Metric.infDist a (tsupport φ) :=
      ((isClosed_tsupport φ).notMem_iff_infDist_pos hφne).mp haφ
    rw [hpdist] at hinf
    exact hinf
  have hballφ : Metric.ball a d ⊆ (tsupport φ)ᶜ := by
    intro z hz
    rw [mem_compl_iff]
    intro hzφ
    have hle : dist a p ≤ dist a z := by
      rw [← hpdist]
      exact Metric.infDist_le_dist_of_mem hzφ
    have hlt : dist a z < dist a p := by
      simpa only [d, dist_comm] using Metric.mem_ball.mp hz
    exact (not_lt_of_ge hle) hlt
  have hzero_event : Filter.EventuallyEq (nhds a) u (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hau] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hzero_ball : Set.EqOn u
      (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℂ)) (Metric.ball a d) := by
    apply hartogsext_eqOn_of_differentiableOn_of_isConnected
      Metric.isOpen_ball
      ⟨⟨a, Metric.mem_ball_self hd⟩, (convex_ball a d).isPreconnected⟩
      (hu.mono hballφ) (differentiable_const (c := (0 : ℂ))).differentiableOn
      (Metric.mem_ball_self hd) hzero_event
  have hpclosed : p ∈ Metric.closedBall a d := by
    rw [Metric.mem_closedBall]
    simp only [d, dist_comm, le_refl]
  have hpclosure : p ∈ closure (Metric.ball a d) := by
    rw [closure_ball a hd.ne']
    exact hpclosed
  obtain ⟨y, hyU, hyball⟩ := mem_closure_iff_nhds.mp hpclosure U
    (hU.mem_nhds (hφU hpφ))
  have hyφ : y ∉ tsupport φ := by
    exact hballφ hyball
  refine ⟨y, ⟨hyU, fun hyK ↦ hyφ (hKφ hyK)⟩, ?_, ?_⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyball] with z hz
    exact hzero_ball hz
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyball] with z hz
    exact image_eq_zero_of_notMem_tsupport
      (hballφ hz)

/--
Let `U ⊆ ℂⁿ` be open connected with `2 ≤ n`, `K ⊆ U` compact with `U \ K` connected. Every `f : ℂⁿ
→ ℂ` holomorphic on `U \ K` extends to holomorphic `F` on `U` with `Set.EqOn F f (U \ K)`. Here
`ℂⁿ` is `EuclideanSpace ℂ (Fin n)`. Source: Hartogs extension phenomenon, F. Hartogs, Math. Ann.
62 (1906); see Hörmander, An Introduction to Complex Analysis in Several Variables; Lean is ℂⁿ n ≥
2 finite-dimensional form via EuclideanSpace ℂ (Fin n) with U open connected K compact U\K
connected.

Proves `Wanted` entry `hartogs_extension`.

Proof: The compactly supported Cauchy–Green equation in one coordinate, combined with a smooth
cutoff and one-variable identity continuation.
-/
theorem hartogs_extension
    {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hUK_conn : IsConnected (U \ K))
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f (U \ K)) :
    ∃ F : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) := by
  by_cases hKne : K.Nonempty
  · let W := U \ K
    have hW_open : IsOpen W := hU_open.sdiff hK_compact.isClosed
    let i₀ : Fin n := ⟨0, lt_of_lt_of_le zero_lt_two hn⟩
    obtain ⟨χ, hχdiff, hχcompact, hχU, V, hV_open, hKV, hχone⟩ :=
      hartogsext_exists_cutoff hU_open hK_compact hKU
    let φ : EuclideanSpace ℂ (Fin n) → ℂ := Complex.ofRealCLM ∘ χ
    have hφdiff : ContDiff ℝ 2 φ := by
      exact Complex.ofRealCLM.contDiff.comp hχdiff
    have hφcompact : HasCompactSupport φ := by
      exact hχcompact.comp_left rfl
    have hφU : tsupport φ ⊆ U := by
      exact (tsupport_comp_subset rfl χ).trans hχU
    have hφone : Set.EqOn φ (fun _ ↦ 1) V := by
      intro x hx
      simp only [φ, Function.comp_apply, Complex.ofRealCLM_apply]
      rw [hχone hx]
      exact Complex.ofReal_one
    have hKφ : K ⊆ tsupport φ := by
      intro x hx
      apply subset_tsupport φ
      rw [Function.mem_support, hφone (hKV hx)]
      norm_num
    have hφne : (tsupport φ).Nonempty := hKne.mono hKφ
    let a : Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
      fun j ↦ hartogsextBarPartial j φ
    have ha_diff (j : Fin n) : ContDiff ℝ 1 (a j) := by
      exact hartogsext_contDiff_barPartial hφdiff j
    have ha_compact (j : Fin n) : HasCompactSupport (a j) := by
      exact hartogsext_hasCompactSupport_barPartial hφcompact j
    have haW (j : Fin n) : tsupport (a j) ⊆ W := by
      intro x hx
      refine ⟨hφU (hartogsext_tsupport_barPartial_subset j hx), ?_⟩
      intro hxK
      have hxcompl := hartogsext_tsupport_barPartial_subset_compl
        hV_open hφone j hx
      exact hxcompl (hKV hxK)
    have hf_real : ContDiffOn ℝ 1 f W :=
      hartogsext_differentiableOn_contDiffOn_one_real hW_open hf
    let g : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * a i₀ x
    have hg_diff : ContDiff ℝ 1 g := by
      exact hartogsext_contDiff_mul_of_tsupport_subset
        hW_open hf_real (ha_diff i₀) (haW i₀)
    have hg_compact : HasCompactSupport g := by
      exact (ha_compact i₀).mul_left
    let b : Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
      fun j x ↦ f x * a j x
    have hb_diff (j : Fin n) : ContDiff ℝ 1 (b j) := by
      exact hartogsext_contDiff_mul_of_tsupport_subset
        hW_open hf_real (ha_diff j) (haW j)
    have hb_compact (j : Fin n) : HasCompactSupport (b j) := by
      exact (ha_compact j).mul_left
    have hcompat (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
        hartogsextBarPartial j g x = hartogsextBarPartial i₀ (b j) x := by
      by_cases hxW : x ∈ W
      · have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hfR : DifferentiableAt ℝ f x := hfd.restrictScalars ℝ
        have hai (k : Fin n) : DifferentiableAt ℝ (a k) x :=
          (ha_diff k).differentiable (by norm_num) x
        rw [show hartogsextBarPartial j g x =
            hartogsextBarPartial j (fun y ↦ f y * a i₀ y) x by rfl,
          hartogsext_barPartial_mul hfR (hai i₀) j,
          show hartogsextBarPartial i₀ (b j) x =
            hartogsextBarPartial i₀ (fun y ↦ f y * a j y) x by rfl,
          hartogsext_barPartial_mul hfR (hai j) i₀,
          hartogsext_barPartial_eq_zero_of_differentiableAt hfd j,
          hartogsext_barPartial_eq_zero_of_differentiableAt hfd i₀]
        simp only [zero_mul, zero_add]
        exact congrArg (fun z : ℂ ↦ f x * z)
          (hartogsext_barPartial_comm hφdiff j i₀ x)
      · have hxg : x ∉ tsupport g := by
          intro hxg
          apply hxW
          apply haW i₀
          exact tsupport_mul_subset_right hxg
        have hxb : x ∉ tsupport (b j) := by
          intro hxb
          apply hxW
          apply haW j
          exact tsupport_mul_subset_right hxb
        rw [hartogsext_barPartial_eq_zero_of_notMem_tsupport hxg,
          hartogsext_barPartial_eq_zero_of_notMem_tsupport hxb]
    let u := hartogsextPartialCauchyGreen i₀ g
    have hu_diff : ContDiff ℝ 1 u :=
      hartogsext_contDiff_partialCauchyGreen hg_compact hg_diff i₀
    have hu_bar (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
        hartogsextBarPartial j u x = b j x := by
      calc
        hartogsextBarPartial j u x =
            hartogsextPartialCauchyGreen i₀
              (hartogsextBarPartial j g) x :=
          hartogsext_barPartial_partialCauchyGreen
            hg_compact hg_diff i₀ j x
        _ = hartogsextPartialCauchyGreen i₀
              (hartogsextBarPartial i₀ (b j)) x := by
          rw [show hartogsextBarPartial j g =
            hartogsextBarPartial i₀ (b j) from funext (hcompat j)]
        _ = hartogsextBarPartial i₀
              (hartogsextPartialCauchyGreen i₀ (b j)) x :=
          (hartogsext_barPartial_partialCauchyGreen
            (hb_compact j) (hb_diff j) i₀ i₀ x).symm
        _ = b j x := hartogsext_barPartial_partialCauchyGreen_self
          (hb_compact j) (hb_diff j) i₀ x
    have hu_compact : HasCompactSupport u :=
      hartogsext_hasCompactSupport_partialCauchyGreen hn hg_compact hg_diff i₀
        hb_compact hu_bar
    let q : EuclideanSpace ℂ (Fin n) → ℂ :=
      fun x ↦ (1 - φ x) * f x
    have hq_event_of_mem_K {x : EuclideanSpace ℂ (Fin n)} (hxK : x ∈ K) :
        Filter.EventuallyEq (nhds x) q (fun _ ↦ 0) := by
      filter_upwards [hV_open.mem_nhds (hKV hxK)] with y hy
      simp only [q, hφone hy, sub_self, zero_mul]
    have hq_diff_at {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) :
        DifferentiableAt ℝ q x := by
      by_cases hxK : x ∈ K
      · exact (hasFDerivAt_zero_of_eventually_const
          (0 : ℂ) (hq_event_of_mem_K hxK)).differentiableAt
      · have hxW : x ∈ W := ⟨hxU, hxK⟩
        have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hφd : DifferentiableAt ℝ φ x :=
          hφdiff.differentiable (by norm_num) x
        exact ((differentiable_const (c := (1 : ℂ)) x).sub hφd).mul
          (hfd.restrictScalars ℝ)
    let F : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ q x + u x
    have hF_real {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) :
        DifferentiableAt ℝ F x :=
      (hq_diff_at hxU).add (hu_diff.differentiable (by norm_num) x)
    have hF_bar {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) (j : Fin n) :
        hartogsextBarPartial j F x = 0 := by
      have hqd := hq_diff_at hxU
      have hud : DifferentiableAt ℝ u x := hu_diff.differentiable (by norm_num) x
      rw [show hartogsextBarPartial j F x =
          hartogsextBarPartial j (fun y ↦ q y + u y) x by rfl,
        hartogsext_barPartial_add hqd hud j, hu_bar]
      by_cases hxK : x ∈ K
      · have hqbar : hartogsextBarPartial j q x = 0 := by
          rw [hartogsextBarPartial,
            (hasFDerivAt_zero_of_eventually_const
              (0 : ℂ) (hq_event_of_mem_K hxK)).fderiv]
          simp
        have hxaj : x ∉ tsupport (a j) := by
          intro hxaj
          have hxcompl := hartogsext_tsupport_barPartial_subset_compl
            hV_open hφone j hxaj
          exact hxcompl (hKV hxK)
        have haj : a j x = 0 := image_eq_zero_of_notMem_tsupport hxaj
        rw [hqbar]
        simp [b, haj]
      · have hxW : x ∈ W := ⟨hxU, hxK⟩
        have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hfR : DifferentiableAt ℝ f x := hfd.restrictScalars ℝ
        have hφR : DifferentiableAt ℝ φ x :=
          hφdiff.differentiable (by norm_num) x
        let p : EuclideanSpace ℂ (Fin n) → ℂ := fun y ↦ 1 - φ y
        have hpR : DifferentiableAt ℝ p x :=
          (differentiable_const (c := (1 : ℂ)) x).sub hφR
        have hpbar : hartogsextBarPartial j p x = -a j x :=
          hartogsext_barPartial_one_sub φ x j
        have hqbar : hartogsextBarPartial j q x = (-a j x) * f x := by
          change hartogsextBarPartial j (fun y ↦ p y * f y) x = _
          rw [hartogsext_barPartial_mul hpR hfR j, hpbar,
            hartogsext_barPartial_eq_zero_of_differentiableAt hfd j]
          simp
        rw [hqbar]
        simp only [b]
        ring
    have hF_diff : DifferentiableOn ℂ F U := by
      intro x hxU
      exact (hartogsext_differentiableAt_of_barPartial_eq_zero
        (hF_real hxU) (hF_bar hxU)).differentiableWithinAt
    have hu_holo : DifferentiableOn ℂ u (tsupport φ)ᶜ := by
      intro x hx
      apply (hartogsext_differentiableAt_of_barPartial_eq_zero
        (hu_diff.differentiable (by norm_num) x) ?_).differentiableWithinAt
      intro j
      rw [hu_bar]
      have hxaj : x ∉ tsupport (a j) := by
        intro hxaj
        exact hx (hartogsext_tsupport_barPartial_subset j hxaj)
      have haj : a j x = 0 := image_eq_zero_of_notMem_tsupport hxaj
      simp [b, haj]
    obtain ⟨y, hyW, huy, hφy⟩ := hartogsext_exists_zero_germ
      hn hU_open hφcompact hφU hKφ hφne hu_compact hu_holo
    have hFf : Filter.EventuallyEq (nhds y) F f := by
      filter_upwards [huy, hφy] with x hux hφx
      simp [F, q, hux, hφx]
    have hEq : Set.EqOn F f W :=
      hartogsext_eqOn_of_differentiableOn_of_isConnected
        hW_open hUK_conn (hF_diff.mono fun x hx ↦ hx.1) hf hyW hFf
    exact ⟨F, hF_diff, hEq⟩
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    subst K
    refine ⟨f, ?_, ?_⟩
    · simpa using hf
    · intro x hx
      rfl

end MathlibExt.Analysis.Complex.HartogsWanted
