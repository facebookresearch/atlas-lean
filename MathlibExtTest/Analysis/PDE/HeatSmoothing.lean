/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.PDE.HeatSmoothing

/-!
# Heat smoothing checks

Concrete consumers of `MathlibExt.Analysis.PDE.HeatSmoothing`: the constant function `1`, whose
heat convolution is `1` (in dimensions `1` and `0`, the latter a boundary case); the Gaussian
`exp(-‖y‖²)`, whose heat convolution is `C^∞` at positive time and satisfies the heat equation;
and the `(1 - x^2)^3` cutoff bump in dimension `1` and the constant `1` in dimension `0`, for which
the `L^p` heat-semigroup generator equals the Laplacian.

These are elaboration and non-vacuity checks, not new results: the Gaussian is bounded and
measurable and the bump is a nonzero compactly supported `C²` function, so the module's theorems
apply to them non-trivially. The private definitions `gaussian`, `gaussian_meas`, and
`gaussian_bdd` are the test function `exp(-‖y‖²)` and its side conditions. The first check pins
`heatConvolution` to the shared heat kernel `MathlibExt.Analysis.PDE.HeatKernel.heatKernel`, and
a time-zero check records that the convolution is `0`, not the identity, at `t = 0`.
-/

open MeasureTheory
open scoped ContDiff Topology
open MathlibExt.Analysis.PDE.HeatKernel

/-- The heat convolution is the convolution with the shared heat kernel on
`EuclideanSpace ℝ (Fin n)`. -/
example (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    heatConvolution n g t x = ∫ y, g y * heatKernel (EuclideanSpace ℝ (Fin n)) t (x - y) :=
  rfl

/-! ## A. The Gaussian test function and its side conditions -/

/-- The Gaussian `exp(-‖y‖²)` on `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def gaussian (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => Real.exp (-‖y‖ ^ 2)

/-- The Gaussian is measurable. -/
private theorem gaussian_meas (n : ℕ) :
    AEStronglyMeasurable (gaussian n) volume := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2)) :=
    Real.continuous_exp.comp ((continuous_norm.pow 2).neg)
  exact hcont.aestronglyMeasurable

/-- The Gaussian is bounded by `1`. -/
private theorem gaussian_bdd (n : ℕ) :
    ∃ M : ℝ, ∀ᵐ y, |gaussian n y| ≤ M := by
  refine ⟨1, Filter.Eventually.of_forall fun y => ?_⟩
  show |Real.exp (-‖y‖ ^ 2)| ≤ 1
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

/-! ## B. Constant-one, in dimensions `1` and `0` -/

/-- The heat convolution of `1` in dimension `1` is `1`. -/
example : heatConvolution 1 (fun _ => (1 : ℝ)) 1
    (0 : EuclideanSpace ℝ (Fin 1)) = 1 :=
  heat_convolution_const_one 1 one_pos 0

/-- The heat convolution of `1` in dimension `0` (boundary case: the space
is a point) is `1`. -/
example : heatConvolution 0 (fun _ => (1 : ℝ)) 1
    (0 : EuclideanSpace ℝ (Fin 0)) = 1 :=
  heat_convolution_const_one 0 one_pos 0

/-- The positive-time contract: at `t = 0` the heat convolution in dimension `1` is `0` for every
`g`, the constant `1` included, not the identity. -/
example (g : EuclideanSpace ℝ (Fin 1) → ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    heatConvolution 1 g 0 x = 0 := by
  have hk : ∀ y : EuclideanSpace ℝ (Fin 1), heatKernel (EuclideanSpace ℝ (Fin 1)) 0 y = 0 := by
    intro y
    simp only [heatKernel, mul_zero, finrank_euclideanSpace_fin]
    rw [Real.zero_rpow (by norm_num), zero_mul]
  simp [heatConvolution, hk]

/-! ## C. Smoothing and the heat equation for the Gaussian -/

/-- Smoothing: the heat convolution of the Gaussian in dimension `1` is
`ContDiffOn ℝ ∞` (`C^∞`) at positive time. -/
example : ContDiffOn ℝ ∞
    (fun p : ℝ × EuclideanSpace ℝ (Fin 1) =>
      heatConvolution 1 (gaussian 1) p.1 p.2)
    (Set.Ioi 0 ×ˢ Set.univ) :=
  heat_convolution_smooth 1 (gaussian_meas 1) (gaussian_bdd 1)

/-- Heat equation: the heat convolution of the Gaussian in dimension `1`
satisfies `u_t = Δu` at `t = 1`, `x = 0`. -/
example : deriv (fun s => heatConvolution 1 (gaussian 1) s
      (0 : EuclideanSpace ℝ (Fin 1))) 1
    = Laplacian.laplacian (fun y => heatConvolution 1 (gaussian 1) 1 y)
      (0 : EuclideanSpace ℝ (Fin 1)) :=
  heat_convolution_satisfies_heat_equation 1 (gaussian_meas 1)
    (gaussian_bdd 1) one_pos 0

/-! ## D. The `(1 - x^2)^3` cutoff bump in dimension `1` -/

private theorem bump_inner_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub hsq

private theorem bump_poly_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t ^ 2) ^ 3) (3 * (1 - t ^ 2) ^ 2 * (-(2 * t))) t := by
  simpa using (bump_inner_hasDerivAt t).fun_pow 3

private theorem bump_poly2_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => 3 * (1 - t ^ 2) ^ 2 * (-(2 * t)))
      (6 * (1 - t ^ 2) * (5 * t ^ 2 - 1)) t := by
  have hd : HasDerivAt (fun t : ℝ => (1 - t ^ 2) ^ 2) (2 * (1 - t ^ 2) * (-(2 * t))) t := by
    simpa using (bump_inner_hasDerivAt t).fun_pow 2
  have hu : HasDerivAt (fun t : ℝ => 3 * (1 - t ^ 2) ^ 2)
      (3 * (2 * (1 - t ^ 2) * (-(2 * t)))) t :=
    HasDerivAt.const_mul 3 hd
  have hv : HasDerivAt (fun t : ℝ => -(2 * t)) (-2) t :=
    (hasDerivAt_const_mul 2).neg
  convert hu.fun_mul hv using 2
  ring

private theorem bump_hasDerivAt (F F' : ℝ → ℝ) (hF : ∀ t, HasDerivAt F (F' t) t)
    (hP1 : F' 1 = 0) (hPm1 : F' (-1) = 0) (hF1 : F 1 = 0) (hFm1 : F (-1) = 0) (t : ℝ) :
    HasDerivAt (fun t => if |t| < 1 then F t else 0)
      (if |t| < 1 then F' t else 0) t := by
  by_cases hmem : |t| < 1
  · have hopen : IsOpen {s : ℝ | |s| < 1} := isOpen_lt continuous_abs continuous_const
    have heq : (fun s : ℝ => if |s| < 1 then F s else 0) =ᶠ[𝓝 t] F :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) (fun s hs => ite_eq_left hs)
    rw [ite_eq_left hmem]
    exact (hF t).congr_of_eventuallyEq heq
  · by_cases hbeq : |t| = 1
    · obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hbeq
      · have hL : HasDerivWithinAt (fun s : ℝ => if |s| < 1 then F s else 0) 0
            (Set.Iic 1) 1 := by
          have hbase : HasDerivWithinAt F (F' 1) (Set.Iic 1) 1 := (hF 1).hasDerivWithinAt
          rw [hP1] at hbase
          have hmemI : Set.Iic (1 : ℝ) ∩ Set.Ioi 0 ∈ 𝓝[Set.Iic 1] 1 :=
            inter_mem_nhdsWithin _ (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr zero_lt_one))
          apply hbase.congr_of_eventuallyEq_of_mem (Filter.eventuallyEq_of_mem hmemI ?_)
            (Set.mem_Iic.mpr le_rfl)
          intro s hs
          rw [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi] at hs
          obtain ⟨hle, hpos⟩ := hs
          show (if |s| < 1 then F s else 0) = F s
          by_cases hs1 : |s| < 1
          · rw [ite_eq_left hs1]
          · have habs : |s| = s := abs_of_pos hpos
            have hge : (1 : ℝ) ≤ s := by
              rw [← habs]
              exact not_lt.mp hs1
            have hseq : s = 1 := le_antisymm hle hge
            rw [hseq, ite_eq_right (by norm_num : ¬ |(1 : ℝ)| < 1), hF1]
        have hR : HasDerivWithinAt (fun s : ℝ => if |s| < 1 then F s else 0) 0
            (Set.Ici 1) 1 := by
          have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Ici 1) 1 :=
            (hasDerivAt_const (1 : ℝ) (0 : ℝ)).hasDerivWithinAt
          apply hbase.congr_of_eventuallyEq_of_mem
            (Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_) (Set.mem_Ici.mpr le_rfl)
          intro s hs
          rw [Set.mem_Ici] at hs
          have hns : ¬ |s| < 1 := not_lt.mpr (le_trans hs (le_abs_self s))
          show (if |s| < 1 then F s else 0) = (fun _ : ℝ => (0 : ℝ)) s
          rw [ite_eq_right hns]
        have hJ : HasDerivAt (fun s : ℝ => if |s| < 1 then F s else 0) 0 1 :=
          (hL.union hR).hasDerivAt (by rw [Set.Iic_union_Ici]; exact Filter.univ_mem)
        rw [ite_eq_right (show ¬ |(1 : ℝ)| < 1 by norm_num)]
        exact hJ
      · have hL : HasDerivWithinAt (fun s : ℝ => if |s| < 1 then F s else 0) 0
            (Set.Iic (-1)) (-1) := by
          have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic (-1)) (-1) :=
            (hasDerivAt_const (-1 : ℝ) (0 : ℝ)).hasDerivWithinAt
          apply hbase.congr_of_eventuallyEq_of_mem
            (Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_) (Set.mem_Iic.mpr le_rfl)
          intro s hs
          rw [Set.mem_Iic] at hs
          have hns : ¬ |s| < 1 := by
            apply not_lt.mpr
            calc (1 : ℝ) ≤ -s := by linarith
              _ ≤ |s| := neg_le_abs s
          show (if |s| < 1 then F s else 0) = (fun _ : ℝ => (0 : ℝ)) s
          rw [ite_eq_right hns]
        have hR : HasDerivWithinAt (fun s : ℝ => if |s| < 1 then F s else 0) 0
            (Set.Ici (-1)) (-1) := by
          have hbase : HasDerivWithinAt F (F' (-1)) (Set.Ici (-1)) (-1) :=
            (hF (-1)).hasDerivWithinAt
          rw [hPm1] at hbase
          have hmemI : Set.Ici (-1 : ℝ) ∩ Set.Iio 0 ∈ 𝓝[Set.Ici (-1)] (-1) :=
            inter_mem_nhdsWithin _
              (isOpen_Iio.mem_nhds (show (-1 : ℝ) ∈ Set.Iio 0 by norm_num))
          apply hbase.congr_of_eventuallyEq_of_mem (Filter.eventuallyEq_of_mem hmemI ?_)
            (Set.mem_Ici.mpr le_rfl)
          intro s hs
          rw [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iio] at hs
          obtain ⟨hge, hneg⟩ := hs
          show (if |s| < 1 then F s else 0) = F s
          by_cases hs1 : |s| < 1
          · rw [ite_eq_left hs1]
          · have habs : |s| = -s := abs_of_neg hneg
            have hle : s ≤ (-1 : ℝ) := by
              have h1s : (1 : ℝ) ≤ |s| := not_lt.mp hs1
              rw [habs] at h1s
              linarith
            have hseq : s = -1 := le_antisymm hle hge
            rw [hseq, ite_eq_right (by norm_num : ¬ |(-1 : ℝ)| < 1), hFm1]
        have hJ : HasDerivAt (fun s : ℝ => if |s| < 1 then F s else 0) 0 (-1) :=
          (hL.union hR).hasDerivAt (by rw [Set.Iic_union_Ici]; exact Filter.univ_mem)
        rw [ite_eq_right (show ¬ |(-1 : ℝ)| < 1 by norm_num)]
        exact hJ
    · have hlt : (1 : ℝ) < |t| := lt_of_le_of_ne (not_lt.mp hmem) (Ne.symm hbeq)
      have hopen : IsOpen {s : ℝ | 1 < |s|} := isOpen_lt continuous_const continuous_abs
      have heq : (fun s : ℝ => if |s| < 1 then F s else 0) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hlt) (fun s hs => by
          have hs' : (1 : ℝ) < |s| := hs
          show (if |s| < 1 then F s else 0) = (fun _ : ℝ => (0 : ℝ)) s
          rw [ite_eq_right (not_lt.mpr (le_of_lt hs'))])
      rw [ite_eq_right hmem]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq

private theorem bump_continuous (F : ℝ → ℝ) (hF : Continuous F) (hF1 : F 1 = 0)
    (hFm1 : F (-1) = 0) :
    Continuous (fun t : ℝ => if |t| < 1 then F t else 0) := by
  have hmid : ContinuousOn (fun t : ℝ => if |t| < 1 then F t else 0) (Set.Icc (-1) 1) := by
    apply ContinuousOn.congr hF.continuousOn ?_
    intro t ht
    rw [Set.mem_Icc] at ht
    by_cases hmem : |t| < 1
    · show (if |t| < 1 then F t else 0) = F t
      rw [ite_eq_left hmem]
    · have habs1 : |t| ≤ 1 := abs_le.mpr ht
      have habs : |t| = 1 := le_antisymm habs1 (not_lt.mp hmem)
      obtain rfl | rfl := eq_or_eq_neg_of_abs_eq habs
      · show (if |(1 : ℝ)| < 1 then F 1 else 0) = F 1
        rw [ite_eq_right (by norm_num : ¬ |(1 : ℝ)| < 1), hF1]
      · show (if |(-1 : ℝ)| < 1 then F (-1) else 0) = F (-1)
        rw [ite_eq_right (by norm_num : ¬ |(-1 : ℝ)| < 1), hFm1]
  have houter : ContinuousOn (fun t : ℝ => if |t| < 1 then F t else 0) {t | 1 ≤ |t|} := by
    apply ContinuousOn.congr (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn ?_
    intro t ht
    have ht' : (1 : ℝ) ≤ |t| := ht
    show (if |t| < 1 then F t else 0) = (fun _ : ℝ => (0 : ℝ)) t
    rw [ite_eq_right (not_lt.mpr ht')]
  have hunion : Set.Icc (-1 : ℝ) 1 ∪ {t | 1 ≤ |t|} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro t
    rw [Set.mem_union]
    rcases le_total |t| 1 with h | h
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr h
  have hcont : ContinuousOn (fun t : ℝ => if |t| < 1 then F t else 0) Set.univ := by
    rw [← hunion]
    exact hmid.union_of_isClosed houter isClosed_Icc
      (isClosed_le continuous_const continuous_abs)
  exact continuousOn_univ.mp hcont

private theorem bump1_contDiff :
    ContDiff ℝ 2 (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0) := by
  have hder1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0)
      (if |t| < 1 then 3 * (1 - t ^ 2) ^ 2 * (-(2 * t)) else 0) t :=
    bump_hasDerivAt _ _ bump_poly_hasDerivAt (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hdg : deriv (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0)
      = (fun t : ℝ => if |t| < 1 then 3 * (1 - t ^ 2) ^ 2 * (-(2 * t)) else 0) :=
    funext fun t => (hder1 t).deriv
  have hder2 : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => if |t| < 1 then 3 * (1 - t ^ 2) ^ 2 * (-(2 * t)) else 0)
      (if |t| < 1 then 6 * (1 - t ^ 2) * (5 * t ^ 2 - 1) else 0) t :=
    bump_hasDerivAt _ _ bump_poly2_hasDerivAt (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hdg' : deriv (fun t : ℝ => if |t| < 1 then 3 * (1 - t ^ 2) ^ 2 * (-(2 * t)) else 0)
      = (fun t : ℝ => if |t| < 1 then 6 * (1 - t ^ 2) * (5 * t ^ 2 - 1) else 0) :=
    funext fun t => (hder2 t).deriv
  have hcont : Continuous
      (fun t : ℝ => if |t| < 1 then 6 * (1 - t ^ 2) * (5 * t ^ 2 - 1) else 0) := by
    apply bump_continuous
    · continuity
    · norm_num
    · norm_num
  have hC1 : ContDiff ℝ 1
      (deriv (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0)) := by
    rw [hdg]
    apply contDiff_one_iff_deriv.mpr
    constructor
    · exact fun t => (hder2 t).differentiableAt
    · rw [hdg']
      exact hcont
  show ContDiff ℝ (1 + 1) (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0)
  exact contDiff_succ_iff_deriv.mpr
    ⟨fun t => (hder1 t).differentiableAt, fun h => absurd h (by decide), hC1⟩

private theorem bump_contDiff_compactSupport :
    ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin 1) =>
      if |x 0| < 1 then (1 - (x 0)^2)^3 else 0)
    ∧ HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 1) =>
      if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) := by
  constructor
  · have hcomp : ContDiff ℝ 2
        ((fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0) ∘
          ⇑(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0)) :=
      bump1_contDiff.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).contDiff
    have hEq : (fun x : EuclideanSpace ℝ (Fin 1) =>
          if |x 0| < 1 then (1 - (x 0)^2)^3 else 0)
        = (fun t : ℝ => if |t| < 1 then (1 - t ^ 2) ^ 3 else 0) ∘
          ⇑(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0) := by
      funext x
      simp only [Function.comp_apply, PiLp.proj_apply]
    rw [hEq]
    exact hcomp
  · have hnorm : ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ = |x 0| := by
      intro x
      have h2 : ‖x‖ ^ 2 = (x 0) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]
      rw [← Real.sqrt_sq_eq_abs (x 0), ← h2, Real.sqrt_sq (norm_nonneg x)]
    have hsupp : Function.support (fun x : EuclideanSpace ℝ (Fin 1) =>
        if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) ⊆ Metric.closedBall 0 1 := by
      intro x hx
      rw [Function.mem_support] at hx
      have h1 : |x 0| < 1 := by
        by_contra h
        apply hx
        show (if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) = 0
        rw [ite_eq_right h]
      rw [Metric.mem_closedBall, dist_zero_right, hnorm x]
      exact le_of_lt h1
    have hsub : tsupport (fun x : EuclideanSpace ℝ (Fin 1) =>
        if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) ⊆ Metric.closedBall 0 1 :=
      closure_minimal hsupp Metric.isClosed_closedBall
    show IsCompact (tsupport _)
    exact (isCompact_closedBall 0 1).of_isClosed_subset isClosed_closure hsub

/-! ## E. Generator equals the Laplacian: bump in dimension `1`, constant `1` in dimension `0` -/

/-- Generator: the `L^p` heat-semigroup generator equals the Laplacian for the
constant function `1` in dimension `0` (boundary case: the space is a point,
so every function is compactly supported). -/
example : Filter.Tendsto
    (fun t : ℝ =>
      (eLpNorm (fun x : EuclideanSpace ℝ (Fin 0) => heatConvolution 0 (fun _ => (1 : ℝ)) t x
        - (fun _ => (1 : ℝ)) x
        - t * Laplacian.laplacian (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ)) x) 2 volume).toReal / t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  heat_semigroup_generator_eq_laplacian 0 (by norm_num) (by norm_num)
    contDiff_const (IsClosed.isCompact (isClosed_tsupport _))

/-- Generator: the `L^p` heat-semigroup generator equals the Laplacian for the
`(1 - x^2)^3` cutoff bump in dimension `1` (non-vacuous: the bump is nonzero). -/
example : Filter.Tendsto
    (fun t : ℝ =>
      (eLpNorm (fun x : EuclideanSpace ℝ (Fin 1) => heatConvolution 1 (fun x : EuclideanSpace ℝ (Fin 1) =>
          if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) t x
        - (fun x : EuclideanSpace ℝ (Fin 1) =>
          if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) x
        - t * Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin 1) =>
          (if |x 0| < 1 then (1 - (x 0)^2)^3 else 0 : ℝ)) x) 2 volume).toReal / t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  heat_semigroup_generator_eq_laplacian 1 (by norm_num) (by norm_num)
    bump_contDiff_compactSupport.1 bump_contDiff_compactSupport.2

/-- Generator in `ENNReal`: the `L^p` heat-semigroup generator equals the
Laplacian for the `(1 - x^2)^3` cutoff bump in dimension `1` (non-vacuous). -/
example : Filter.Tendsto
    (fun t : ℝ =>
      (eLpNorm (fun x : EuclideanSpace ℝ (Fin 1) => heatConvolution 1 (fun x : EuclideanSpace ℝ (Fin 1) =>
          if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) t x
        - (fun x : EuclideanSpace ℝ (Fin 1) =>
          if |x 0| < 1 then (1 - (x 0)^2)^3 else 0) x
        - t * Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin 1) =>
          (if |x 0| < 1 then (1 - (x 0)^2)^3 else 0 : ℝ)) x) 2 volume) / ENNReal.ofReal t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  heat_semigroup_generator_eq_laplacian_ennreal 1 (by norm_num) (by norm_num)
    bump_contDiff_compactSupport.1 bump_contDiff_compactSupport.2

/-- Generator in `ENNReal`: the `L^p` heat-semigroup generator equals the
Laplacian for the constant function `1` in dimension `0` (boundary case). -/
example : Filter.Tendsto
    (fun t : ℝ =>
      (eLpNorm (fun x : EuclideanSpace ℝ (Fin 0) => heatConvolution 0 (fun _ => (1 : ℝ)) t x
        - (fun _ => (1 : ℝ)) x
        - t * Laplacian.laplacian (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ)) x) 2 volume) / ENNReal.ofReal t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  heat_semigroup_generator_eq_laplacian_ennreal 0 (by norm_num) (by norm_num)
    contDiff_const (IsClosed.isCompact (isClosed_tsupport _))
