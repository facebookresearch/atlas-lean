/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.CramerDecompositionWanted

/-!
# Cramér's decomposition theorem

Cramér's decomposition of Gaussian sums into Gaussian summands.
-/

private lemma integrable_exp_mul_of_indep_add_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have hmap : Measure.map (fun ω => X ω + Y ω) μ =
      gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal :=
    hAdd.map_eq_gaussianReal
  have hLaw : HasLaw (fun ω => X ω + Y ω)
      (gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal) μ :=
    ⟨hAdd.aemeasurable, hmap⟩
  have hmgfS : mgf (fun ω => X ω + Y ω) μ t =
      Real.exp ((∫ ω, (X ω + Y ω) ∂μ) * t +
        ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * t ^ 2 / 2) :=
    mgf_gaussianReal hLaw t
  have hprod : mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
    hXY.mgf_add' hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hbridge : (fun ω => X ω + Y ω) = (X + Y) := rfl
  rw [hbridge] at hmgfS
  rw [hprod] at hmgfS
  have hpos : 0 < mgf X μ t * mgf Y μ t := by
    rw [hmgfS]; exact Real.exp_pos _
  have hXnn : 0 ≤ mgf X μ t := mgf_nonneg
  have hXpos : 0 < mgf X μ t := by
    by_contra h
    push Not at h
    have hzero : mgf X μ t = 0 := le_antisymm h hXnn
    rw [hzero, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  rw [mgf_pos_iff] at hXpos
  exact hXpos

private lemma complexMGF_add_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) (z : ℂ) :
    complexMGF (fun ω => X ω + Y ω) μ z
      = complexMGF X μ z * complexMGF Y μ z := by
  unfold complexMGF
  have hcont : Continuous (fun x : ℝ => Complex.exp (z * (x : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hcm : Measurable (fun x : ℝ => Complex.exp (z * (x : ℂ))) := hcont.measurable
  have hindep : ((fun x : ℝ => Complex.exp (z * (x : ℂ))) ∘ X) ⟂ᵢ[μ]
      ((fun x : ℝ => Complex.exp (z * (x : ℂ))) ∘ Y) :=
    hXY.comp hcm hcm
  have hXm : AEStronglyMeasurable (((fun x : ℝ => Complex.exp (z * (x : ℂ))) ∘ X)) μ :=
    (hcm.comp hX).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (((fun x : ℝ => Complex.exp (z * (x : ℂ))) ∘ Y)) μ :=
    (hcm.comp hY).aestronglyMeasurable
  have heq :=
    ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hindep hXm hYm
  simp only [Function.comp_apply] at heq
  have hexp : (fun ω => Complex.exp (z * (((fun ω => X ω + Y ω) ω : ℝ) : ℂ))) =
      (fun ω => Complex.exp (z * (X ω : ℂ)) * Complex.exp (z * (Y ω : ℂ))) := by
    funext ω
    simp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  exact heq

private lemma complexMGF_mul_eq_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ)
    (z : ℂ) :
    complexMGF X μ z * complexMGF Y μ z =
      Complex.exp (z * (∫ ω, (X ω + Y ω) ∂μ : ℝ) +
        ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * z ^ 2 / 2) := by
  have hmap : Measure.map (fun ω => X ω + Y ω) μ =
      gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal :=
    hAdd.map_eq_gaussianReal
  have hLaw : HasLaw (fun ω => X ω + Y ω)
      (gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal) μ :=
    ⟨hAdd.aemeasurable, hmap⟩
  have hgauss : complexMGF (fun ω => X ω + Y ω) μ z =
      Complex.exp (z * (∫ ω, (X ω + Y ω) ∂μ : ℝ) +
        ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * z ^ 2 / 2) :=
    complexMGF_gaussianReal hLaw z
  have hN2 := complexMGF_add_of_indepFun hX hY hXY z
  rw [← hN2]; exact hgauss

private lemma differentiable_complexMGF_of_integrableExpSet_eq_univ
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h : integrableExpSet X μ = Set.univ) :
    Differentiable ℂ (complexMGF X μ) := by
  have h1 : {z : ℂ | z.re ∈ interior (integrableExpSet X μ)} = Set.univ := by
    rw [h, interior_univ]; simp
  have h2 := differentiableOn_complexMGF (X := X) (μ := μ)
  rw [h1] at h2
  exact differentiableOn_univ.mp h2

private lemma norm_complexMGF_le_of_indep_add_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ)
    (z : ℂ) :
    ‖complexMGF X μ z‖ ≤ Real.exp ((∫ ω, X ω ∂μ) * z.re +
      ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * z.re ^ 2 / 2) := by
  have hYX : (fun ω => Y ω + X ω) = (fun ω => X ω + Y ω) := by
    funext ω; exact add_comm _ _
  have hAddYX : HasGaussianLaw (fun ω => Y ω + X ω) μ := hYX ▸ hAdd
  have hYexp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ :=
    fun t => integrable_exp_mul_of_indep_add_gaussian hY hX hXY.symm hAddYX t
  have hXset : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_indep_add_gaussian hX hY hXY hAdd t
  have hYset : integrableExpSet Y μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact hYexp t
  have hXint : Integrable X μ := integrable_of_mem_interior_integrableExpSet (by
    rw [hXset, interior_univ]; exact Set.mem_univ 0)
  have hYint : Integrable Y μ := integrable_of_mem_interior_integrableExpSet (by
    rw [hYset, interior_univ]; exact Set.mem_univ 0)
  set x : ℝ := z.re with hx
  have hprod : mgf X μ x * mgf Y μ x =
      Real.exp ((∫ ω, (X ω + Y ω) ∂μ) * x +
        ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) := by
    have h1 : mgf (X + Y) μ x = mgf X μ x * mgf Y μ x :=
      hXY.mgf_add' hX.aestronglyMeasurable hY.aestronglyMeasurable
    have hmap : Measure.map (fun ω => X ω + Y ω) μ =
        gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal :=
      hAdd.map_eq_gaussianReal
    have hLaw : HasLaw (fun ω => X ω + Y ω)
        (gaussianReal (∫ ω, (X ω + Y ω) ∂μ) (Var[fun ω => X ω + Y ω; μ]).toNNReal) μ :=
      ⟨hAdd.aemeasurable, hmap⟩
    have h2 : mgf (fun ω => X ω + Y ω) μ x =
        Real.exp ((∫ ω, (X ω + Y ω) ∂μ) * x +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) :=
      mgf_gaussianReal hLaw x
    have hbridge : (fun ω => X ω + Y ω) = (X + Y) := rfl
    rw [hbridge] at h2
    rw [← h1]; exact h2
  have hYpos : 0 < mgf Y μ x := mgf_pos (hYexp x)
  have hJen : Real.exp (x * (∫ ω, Y ω ∂μ)) ≤ mgf Y μ x := by
    have h1 : Integrable (fun ω => x * Y ω) μ := hYint.const_mul x
    have h2 : Integrable (Real.exp ∘ (fun ω => x * Y ω)) μ := by
      simpa [Function.comp_def] using hYexp x
    have h3 := convexOn_exp.map_integral_le (s := Set.univ)
      Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun ω => Set.mem_univ (x * Y ω))) h1 h2
    rw [integral_const_mul] at h3
    have h4 : (∫ ω, Real.exp (x * Y ω) ∂μ) = mgf Y μ x := rfl
    simpa [Function.comp_def, h4] using h3
  have hm : (∫ ω, (X ω + Y ω) ∂μ) = (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ :=
    integral_add hXint hYint
  have hle : mgf X μ x ≤ Real.exp ((∫ ω, X ω ∂μ) * x +
      ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) := by
    have e1 : mgf X μ x * mgf Y μ x =
        Real.exp ((∫ ω, X ω ∂μ) * x + x * (∫ ω, Y ω ∂μ) +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) := by
      rw [hprod, hm]; congr 1; ring
    have e2 : mgf X μ x =
        Real.exp ((∫ ω, X ω ∂μ) * x + x * (∫ ω, Y ω ∂μ) +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) / mgf Y μ x := by
      rw [eq_div_iff hYpos.ne']; exact e1
    rw [e2, div_le_iff₀ hYpos]
    have g1 : Real.exp ((∫ ω, X ω ∂μ) * x +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) *
        Real.exp (x * ∫ ω, Y ω ∂μ) =
        Real.exp ((∫ ω, X ω ∂μ) * x + x * (∫ ω, Y ω ∂μ) +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have g2 : Real.exp ((∫ ω, X ω ∂μ) * x +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) *
        Real.exp (x * ∫ ω, Y ω ∂μ) ≤
        Real.exp ((∫ ω, X ω ∂μ) * x +
          ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) * x ^ 2 / 2) * mgf Y μ x :=
      mul_le_mul_of_nonneg_left hJen (Real.exp_pos _).le
    rw [g1] at g2
    exact g2
  calc ‖complexMGF X μ z‖ ≤ mgf X μ x := norm_complexMGF_le_mgf
    _ ≤ _ := hle

private lemma exists_differentiable_exp_eq_of_ne_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∀ z, f z ≠ 0) (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, Complex.exp (g z) = f z := by
  have hderiv : Differentiable ℂ (deriv f) := hf.deriv
  have hh : Differentiable ℂ (fun z => deriv f z / f z) := hderiv.div hf hne
  obtain ⟨G, hG⟩ := hh.isExactOn_univ
  have hG' : ∀ z, HasDerivAt G (deriv f z / f z) z := fun z => hG z (Set.mem_univ z)
  have hGdiff : Differentiable ℂ G :=
    fun z => (hG' z).differentiableAt
  refine ⟨fun z => G z - G 0, hGdiff.sub_const _, by simp, ?_⟩
  have hgderiv : ∀ z, HasDerivAt (fun w => G w - G 0) (deriv f z / f z) z :=
    fun z => (hG' z).sub_const _
  have hexp : ∀ z, HasDerivAt (fun w => Complex.exp (-(G w - G 0)))
      (Complex.exp (-(G z - G 0)) * (-(deriv f z / f z))) z := by
    intro z
    have h2 : HasDerivAt (fun w => -(G w - G 0)) (-(deriv f z / f z)) z :=
      (hgderiv z).neg
    have h3 := h2.cexp
    simpa [Function.comp_def] using h3
  have hF : ∀ z, HasDerivAt (fun w => f w * Complex.exp (-(G w - G 0)))
      (deriv f z * Complex.exp (-(G z - G 0)) +
        f z * (Complex.exp (-(G z - G 0)) * (-(deriv f z / f z)))) z := by
    intro z
    exact ((hf z).hasDerivAt).mul (hexp z)
  have hFdiff : Differentiable ℂ (fun w => f w * Complex.exp (-(G w - G 0))) :=
    fun z => (hF z).differentiableAt
  have hFderiv0 : ∀ z, deriv (fun w => f w * Complex.exp (-(G w - G 0))) z = 0 := by
    intro z
    rw [(hF z).deriv]
    have hfz : f z ≠ 0 := hne z
    field_simp
    ring
  have hconst : ∀ x y, (fun w => f w * Complex.exp (-(G w - G 0))) x =
      (fun w => f w * Complex.exp (-(G w - G 0))) y :=
    is_const_of_deriv_eq_zero hFdiff hFderiv0
  intro z
  have h1 : f z * Complex.exp (-(G z - G 0)) = 1 := by
    have h := hconst z 0
    simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at h
    rw [h0] at h
    exact h
  have key : Complex.exp (G z - G 0) * Complex.exp (-(G z - G 0)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h4 : Complex.exp (G z - G 0) * (f z * Complex.exp (-(G z - G 0))) = f z := by
    calc Complex.exp (G z - G 0) * (f z * Complex.exp (-(G z - G 0)))
        = f z * (Complex.exp (G z - G 0) * Complex.exp (-(G z - G 0))) := by ring
      _ = f z := by rw [key, mul_one]
  rw [h1, mul_one] at h4
  change Complex.exp (G z - G 0) = f z
  exact h4

private lemma iteratedDeriv_eq_zero_of_re_le_quadratic
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    {K : ℝ} (hK : 0 < K) (hle : ∀ z, (g z).re ≤ K * (1 + ‖z‖ ^ 2))
    {n : ℕ} (hn : 3 ≤ n) : iteratedDeriv n g 0 = 0 := by
  by_contra hne
  have heps : 0 < ‖iteratedDeriv n g 0‖ := norm_pos_iff.mpr hne
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n g 0‖ * R ≤ 10 * n.factorial * K := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    set M : ℝ := K * (1 + 4 * R ^ 2) with hM
    have hMpos : 0 < M := mul_pos hK (by positivity)
    have hball : DifferentiableOn ℂ g (Metric.ball 0 (2 * R)) := hg.differentiableOn
    have hmaps : Set.MapsTo g (Metric.ball 0 (2 * R)) {z | z.re ≤ M} := by
      intro w hw
      change (g w).re ≤ M
      rw [Metric.mem_ball, dist_zero_right] at hw
      calc (g w).re ≤ K * (1 + ‖w‖ ^ 2) := hle w
        _ ≤ K * (1 + (2 * R) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right (pow_le_pow_left₀ (norm_nonneg _) hw.le 2) 1) hK.le
        _ = M := by rw [hM]; ring
    have hdiff : DiffContOnCl ℂ g (Metric.ball 0 R) := hg.diffContOnCl
    have hbound : ∀ z ∈ Metric.sphere 0 R, ‖g z‖ ≤ 2 * M := by
      intro z hz
      have hRw : ‖z‖ = R := by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        exact hz
      have hzball : z ∈ Metric.ball 0 (2 * R) := by
        rw [Metric.mem_ball, dist_zero_right, hRw]; linarith
      have hbc := Complex.borelCaratheodory_zero hMpos hball hmaps
        (by linarith : (0 : ℝ) < 2 * R) hzball hg0
      rw [hRw] at hbc
      have hrw : 2 * R - R = R := by ring
      rw [hrw, mul_div_cancel_right₀ _ hRpos.ne'] at hbc
      exact hbc
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (c := (0 : ℂ)) (R := R) (C := 2 * M) (f := g) n hRpos hdiff hbound
    have step1 : ‖iteratedDeriv n g 0‖ * R ^ n ≤ n.factorial * (2 * M) :=
      (le_div_iff₀ (pow_pos hRpos n)).mp hcauchy
    have step2 : (2 : ℝ) * M ≤ 10 * K * R ^ 2 := by
      have h1 : (1 : ℝ) ≤ R ^ 2 := by
        calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
          _ ≤ R ^ 2 := pow_le_pow_left₀ zero_le_one hR 2
      rw [hM]; nlinarith [hK, h1, sq_nonneg R]
    have step3 : ‖iteratedDeriv n g 0‖ * R ^ n ≤ n.factorial * (10 * K * R ^ 2) :=
      le_trans step1 (mul_le_mul_of_nonneg_left step2 (by positivity))
    have hn2 : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
    have step4 : R ^ (n - 2) * R ^ 2 = R ^ n := by rw [← pow_add, hn2]
    have step5 : (‖iteratedDeriv n g 0‖ * R ^ (n - 2)) * R ^ 2 ≤
        (10 * n.factorial * K) * R ^ 2 := by
      have htmp : ‖iteratedDeriv n g 0‖ * (R ^ (n - 2) * R ^ 2) ≤
          (10 * n.factorial * K) * R ^ 2 := by
        rw [step4]
        have hrw : (10 * n.factorial * K) * R ^ 2 =
            n.factorial * (10 * K * R ^ 2) := by ring
        rw [hrw]; exact step3
      calc (‖iteratedDeriv n g 0‖ * R ^ (n - 2)) * R ^ 2
          = ‖iteratedDeriv n g 0‖ * (R ^ (n - 2) * R ^ 2) := by ring
        _ ≤ _ := htmp
    have step6 : ‖iteratedDeriv n g 0‖ * R ^ (n - 2) ≤ 10 * n.factorial * K :=
      le_of_mul_le_mul_right step5 (pow_pos hRpos 2)
    have step7 : R ≤ R ^ (n - 2) := by
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ (n - 2) := pow_le_pow_right₀ hR (by omega)
    have step8 : ‖iteratedDeriv n g 0‖ * R ≤ ‖iteratedDeriv n g 0‖ * R ^ (n - 2) :=
      mul_le_mul_of_nonneg_left step7 (norm_nonneg _)
    linarith
  have hfact : (0 : ℝ) < n.factorial := by positivity
  set R0 : ℝ := 10 * n.factorial * K / ‖iteratedDeriv n g 0‖ + 1 with hR0
  have hR0ge : 1 ≤ R0 := by
    rw [hR0]
    exact le_add_of_nonneg_left (div_nonneg (by positivity) heps.le)
  have hbig := key R0 hR0ge
  have hR0gt : 10 * n.factorial * K / ‖iteratedDeriv n g 0‖ < R0 := by
    rw [hR0]; linarith
  have hgt : 10 * n.factorial * K < R0 * ‖iteratedDeriv n g 0‖ :=
    (div_lt_iff₀ heps).mp hR0gt
  have hcomm : R0 * ‖iteratedDeriv n g 0‖ = ‖iteratedDeriv n g 0‖ * R0 :=
    mul_comm _ _
  linarith

private lemma eq_quadratic_of_iteratedDeriv_eq_zero
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hvan : ∀ n : ℕ, 3 ≤ n → iteratedDeriv n g 0 = 0)
    (z : ℂ) : g z = g 0 + deriv g 0 * z + iteratedDeriv 2 g 0 / 2 * z ^ 2 := by
  have htaylor := Complex.taylorSeries_eq_of_entire' (0 : ℂ) z hg
  simp only [sub_zero] at htaylor
  have htsum : (∑' n, ((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0 * z ^ n) =
      ∑ k ∈ Finset.range 3, ((k.factorial : ℂ))⁻¹ * iteratedDeriv k g 0 * z ^ k := by
    apply tsum_eq_sum
    intro b hb
    rw [Finset.mem_range] at hb
    rw [hvan b (by omega)]
    simp
  rw [htsum] at htaylor
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at htaylor
  simp only [Finset.sum_range_zero] at htaylor
  rw [iteratedDeriv_zero, iteratedDeriv_one] at htaylor
  norm_num at htaylor
  linear_combination -htaylor

private lemma complexMGF_eq_exp_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ) :
    ∃ b c : ℂ, ∀ z, complexMGF X μ z = Complex.exp (b * z + c * z ^ 2) := by
  have hXset : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_indep_add_gaussian hX hY hXY hAdd t
  have hf : Differentiable ℂ (complexMGF X μ) :=
    differentiable_complexMGF_of_integrableExpSet_eq_univ hXset
  have hne : ∀ z, complexMGF X μ z ≠ 0 := by
    intro z
    have hN3 := complexMGF_mul_eq_gaussian hX hY hXY hAdd z
    have hnn : complexMGF X μ z * complexMGF Y μ z ≠ 0 := by
      rw [hN3]; exact Complex.exp_ne_zero _
    exact left_ne_zero_of_mul hnn
  have hf0 : complexMGF X μ 0 = 1 := by simp [complexMGF]
  obtain ⟨g, hgdiff, hg0, hgexp⟩ := exists_differentiable_exp_eq_of_ne_zero hf hne hf0
  set E : ℝ := ∫ ω, X ω ∂μ with hE
  set v : ℝ := ((Var[fun ω => X ω + Y ω; μ]).toNNReal : ℝ) with hv
  have hgrow : ∀ z, ‖complexMGF X μ z‖ ≤ Real.exp (E * z.re + v * z.re ^ 2 / 2) :=
    fun z => norm_complexMGF_le_of_indep_add_gaussian hX hY hXY hAdd z
  have hlog : ∀ z, (g z).re ≤ E * z.re + v * z.re ^ 2 / 2 := by
    intro z
    have hpos : 0 < ‖complexMGF X μ z‖ := norm_pos_iff.mpr (hne z)
    have hnorm : ‖complexMGF X μ z‖ = Real.exp (g z).re := by
      rw [← hgexp z, Complex.norm_exp]
    have hle := Real.log_le_log hpos (hgrow z)
    simp only [hnorm, Real.log_exp] at hle
    exact hle
  have hK : (0 : ℝ) < |E| + v + 1 := by
    have hvnn : (0 : ℝ) ≤ v := NNReal.coe_nonneg _
    have : (0 : ℝ) < |E| + 1 := by linarith [abs_nonneg E]
    linarith
  have hbound : ∀ z, (g z).re ≤ (|E| + v + 1) * (1 + ‖z‖ ^ 2) := by
    intro z
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hnorm : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]
    have hE2 : E * z.re ≤ |E| * ‖z‖ := by
      calc E * z.re ≤ |E * z.re| := le_abs_self _
        _ = |E| * |z.re| := abs_mul _ _
        _ ≤ |E| * ‖z‖ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have hvnn : (0 : ℝ) ≤ v := NNReal.coe_nonneg _
    have hx2 : z.re ^ 2 ≤ 1 + ‖z‖ ^ 2 := by
      have h1 : z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
      have h2 : |z.re| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h3 : ‖z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_left zero_le_one
      linarith
    have hv2 : v * z.re ^ 2 / 2 ≤ v * (1 + ‖z‖ ^ 2) := by
      have hgap : (0 : ℝ) ≤ (1 + ‖z‖ ^ 2) - z.re ^ 2 / 2 := by
        have hsq : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
        linarith
      nlinarith [mul_nonneg hvnn hgap]
    have hE3 : |E| * ‖z‖ ≤ |E| * (1 + ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
    have hT : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by positivity
    have h1 := hlog z
    linarith
  have hvan : ∀ n : ℕ, 3 ≤ n → iteratedDeriv n g 0 = 0 :=
    fun n hn => iteratedDeriv_eq_zero_of_re_le_quadratic hgdiff hg0 hK hbound hn
  have hquad : ∀ z, g z = g 0 + deriv g 0 * z + iteratedDeriv 2 g 0 / 2 * z ^ 2 :=
    fun z => eq_quadratic_of_iteratedDeriv_eq_zero hgdiff hvan z
  refine ⟨deriv g 0, iteratedDeriv 2 g 0 / 2, fun z => ?_⟩
  rw [← hgexp z, hquad z, hg0, zero_add]

private lemma hasGaussianLaw_left_of_indep_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ) :
    HasGaussianLaw X μ := by
  obtain ⟨b, c, hbc⟩ := complexMGF_eq_exp_quadratic hX hY hXY hAdd
  have hXset : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_indep_add_gaussian hX hY hXY hAdd t
  have h0mem : (0 : ℂ).re ∈ interior (integrableExpSet X μ) := by
    rw [hXset, interior_univ]; exact Set.mem_univ _
  have h0memR : (0 : ℝ) ∈ interior (integrableExpSet X μ) := by
    rw [hXset, interior_univ]; exact Set.mem_univ _
  have hmem : MemLp X 2 μ := memLp_of_mem_interior_integrableExpSet h0memR 2
  set E : ℝ := ∫ ω, X ω ∂μ with hE
  set Q : ℝ := ∫ ω, X ω ^ 2 ∂μ with hQ
  set σ : NNReal := Var[X; μ].toNNReal with hσ
  -- polynomial derivative
  have h1 : ∀ z, HasDerivAt (fun w => b * w) b z := by
    intro z
    simpa using (hasDerivAt_id z).const_mul b
  have h2 : ∀ z, HasDerivAt (fun w => c * w ^ 2) (2 * c * z) z := by
    intro z
    have h := (hasDerivAt_pow 2 z).const_mul c
    convert h using 1
    push_cast
    ring
  have hp : ∀ z, HasDerivAt (fun w => b * w + c * w ^ 2) (b + 2 * c * z) z :=
    fun z => (h1 z).add (h2 z)
  have hexp : ∀ z, HasDerivAt (fun w => Complex.exp (b * w + c * w ^ 2))
      (Complex.exp (b * z + c * z ^ 2) * (b + 2 * c * z)) z :=
    fun z => (hp z).cexp
  have hfderiv : ∀ z, HasDerivAt (complexMGF X μ)
      (complexMGF X μ z * (b + 2 * c * z)) z := by
    intro z
    have h := hexp z
    simp only [← hbc] at h
    exact h
  have hf0 : complexMGF X μ 0 = 1 := by simp [complexMGF]
  have hd1 : deriv (complexMGF X μ) 0 = b := by
    have h := (hfderiv 0).deriv
    rw [hf0] at h
    simpa using h
  have hderivfun : deriv (complexMGF X μ) =
      fun z => complexMGF X μ z * (b + 2 * c * z) :=
    funext fun z => (hfderiv z).deriv
  have hq : ∀ z, HasDerivAt (fun w => b + 2 * c * w) (2 * c) z := by
    intro z
    simpa using HasDerivAt.const_add b ((hasDerivAt_id z).const_mul (2 * c))
  have hd2 : deriv (deriv (complexMGF X μ)) 0 = 2 * c + b ^ 2 := by
    have h := (hfderiv 0).mul (hq 0)
    rw [hf0] at h
    have hder : deriv (fun z => complexMGF X μ z * (b + 2 * c * z)) 0 =
        1 * (b + 2 * c * 0) * (b + 2 * c * 0) + 1 * (2 * c) := h.deriv
    rw [hderivfun, hder]
    ring
  -- moments
  have e1 : iteratedDeriv 1 (complexMGF X μ) 0 = ((E : ℝ) : ℂ) := by
    have hm := ProbabilityTheory.iteratedDeriv_complexMGF (X := X) (μ := μ)
      (z := (0 : ℂ)) h0mem 1
    rw [hm, hE]
    simp only [pow_one, zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  have e2 : iteratedDeriv 2 (complexMGF X μ) 0 = ((Q : ℝ) : ℂ) := by
    have hm := ProbabilityTheory.iteratedDeriv_complexMGF (X := X) (μ := μ)
      (z := (0 : ℂ)) h0mem 2
    rw [hm, hQ]
    simp only [zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow]
    exact integral_ofReal
  have hbE : b = ((E : ℝ) : ℂ) := by
    rw [← hd1, ← iteratedDeriv_one]; exact e1
  have hi2 : iteratedDeriv 2 (complexMGF X μ) 0 =
      deriv (deriv (complexMGF X μ)) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hQc : 2 * c + b ^ 2 = ((Q : ℝ) : ℂ) := by
    rw [← hd2, ← hi2]; exact e2
  have hvar : Var[X; μ] = Q - E ^ 2 := by
    have h := variance_eq_sub hmem
    simp only [Pi.pow_apply] at h
    rw [h, ← hQ, ← hE]
  have hσr : ((σ : ℝ)) = Var[X; μ] := Real.coe_toNNReal _ (variance_nonneg X μ)
  have hQcE : 2 * c + ((E : ℝ) : ℂ) ^ 2 = ((Q : ℝ) : ℂ) := by
    rw [← hbE]; exact hQc
  have h2c : 2 * c = ((Var[X; μ] : ℝ) : ℂ) := by
    rw [hvar]
    push_cast
    linear_combination hQcE
  have hcV : c = (((σ : ℝ)) : ℂ) / 2 := by
    have hσc : (((σ : ℝ)) : ℂ) = ((Var[X; μ] : ℝ) : ℂ) := by rw [hσr]
    rw [hσc, ← h2c]
    ring
  -- identification
  have hpoint : ∀ z, complexMGF X μ z =
      complexMGF id (gaussianReal E σ) z := by
    intro z
    rw [hbc z, complexMGF_id_gaussianReal]
    congr 1
    rw [hbE, hcV]
    ring
  have hlaw : Measure.map X μ = gaussianReal E σ := by
    have hcm : complexMGF X μ = complexMGF id (gaussianReal E σ) := funext hpoint
    have hext := Measure.ext_of_complexMGF_eq hX.aemeasurable aemeasurable_id hcm
    rwa [Measure.map_id] at hext
  have hgauss : IsGaussian (Measure.map X μ) := by
    rw [hlaw]; exact isGaussian_gaussianReal _ _
  exact HasGaussianLaw.mk hX.aemeasurable hgauss

/--
**Cramér's decomposition theorem.** Let $X$ and $Y$ be measurable real random variables on a
probability space. If $X$ and $Y$ are independent and $X + Y$ has a Gaussian law, then $X$ and
$Y$ each have a Gaussian law. Here a Gaussian law may be degenerate, that is, a point mass.

Proves `Wanted` entry `cramer_decomposition`.

Source: H. Cramér, "Über eine Eigenschaft der normalen Verteilungsfunktion", Mathematische
Zeitschrift 41 (1936), 405–414, DOI 10.1007/BF01180430.
-/
theorem cramer_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ) :
    HasGaussianLaw X μ ∧ HasGaussianLaw Y μ := by
  refine ⟨hasGaussianLaw_left_of_indep_add hX hY hXY hAdd, ?_⟩
  have hYX : (fun ω => Y ω + X ω) = (fun ω => X ω + Y ω) := by
    funext ω; exact add_comm _ _
  have hAddYX : HasGaussianLaw (fun ω => Y ω + X ω) μ := hYX ▸ hAdd
  exact hasGaussianLaw_left_of_indep_add hY hX hXY.symm hAddYX

end MathlibExt.Probability.CramerDecompositionWanted
end
