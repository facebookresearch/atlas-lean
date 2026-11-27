/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import MathlibExt.Probability.Diffusion.JKOScheme
import MathlibExt.MeasureTheory.OptimalTransport.Existence
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability
import MathlibExt.InformationTheory.DonskerVaradhanFormula
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Existence and uniqueness of a JKO step

`existsUnique_isJKOStep` gives a unique minimizer of the Jordan–Kinderlehrer–Otto
objective for each admissible initial law.

Write `k = h / β` and tilt Lebesgue measure by the Gaussian weight `exp (-‖y‖² / (8k))`.
Up to a finite constant fixed by the first marginal, the objective on transport plans
is the sum of a nonnegative coercive transport cost, `h` times the potential energy, and `k` times
the relative entropy of the second marginal against this reference law. The second-moment
bound gives tight sublevels. Lower semicontinuity gives an optimal plan, and strict
convexity of relative entropy makes its second marginal unique.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal NNReal
open MathlibExt.Probability.Diffusion.JKOScheme
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.Probability.Diffusion.JKOSchemeWanted

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Entropy relative to a Gaussian reference measure -/

private theorem gaussian_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-a * ‖x‖ ^ 2)) := by
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (a : ℂ)) (by simpa) 0 (0 : E)).norm
  apply H.congr (ae_of_all _ fun x => ?_)
  simp [Complex.norm_exp, Complex.mul_re, ← Complex.ofReal_pow]

private theorem neg_mul_log_bound {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    -(t * Real.log t) ≤ u * t + Real.exp (-u) := by
  by_cases h : t = 0
  · simpa [h] using (Real.exp_pos (-u)).le
  have ht' := lt_of_le_of_ne ht (Ne.symm h)
  have hlog := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (-u)) ht')
  rw [Real.log_div (Real.exp_ne_zero _) h, Real.log_exp] at hlog
  have H := mul_le_mul_of_nonneg_right hlog ht
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ h, one_mul] at H
  linarith

private theorem negEntropyPart_bound {ρ : ProbabilityMeasure E} (hρ : IsAdmissible ρ)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal (-(((ρ : Measure E).rnDeriv volume x).toReal *
      Real.log ((ρ : Measure E).rnDeriv volume x).toReal))) ≤
      ENNReal.ofReal a * (∫⁻ x, ‖x‖ₑ ^ 2 ∂(ρ : Measure E)) +
        ∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2)) := by
  let f := (ρ : Measure E).rnDeriv volume
  have H x := neg_mul_log_bound (ENNReal.toReal_nonneg (a := f x)) (a * ‖x‖ ^ 2)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a * ‖x‖ ^ 2 * (f x).toReal + Real.exp (-a * ‖x‖ ^ 2)) := by
      apply lintegral_mono
      intro x
      simpa only [neg_mul] using ENNReal.ofReal_le_ofReal (H x)
    _ = ∫⁻ x, (ENNReal.ofReal a * (f x * ‖x‖ₑ ^ 2) +
        ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2))) := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top (ρ : Measure E) volume] with x hx
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha.le,
        ENNReal.ofReal_toReal hx.ne, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      dsimp [f]
      ac_rfl
    _ = _ := by
      have hm : Measurable fun x => f x * ‖x‖ₑ ^ 2 :=
        (Measure.measurable_rnDeriv _ _).mul (by fun_prop)
      rw [lintegral_add_left (f := fun x => ENNReal.ofReal a * (f x * ‖x‖ₑ ^ 2))
        (measurable_const.mul hm), lintegral_const_mul _ hm,
        lintegral_rnDeriv_mul hρ.1 (by fun_prop)]

-- The positive part may have infinite integral. The preceding bound controls the negative
-- part in both cases, so the change of reference law is an identity in the extended reals.
private theorem negEntropy_tilt {ρ : ProbabilityMeasure E} (hρ : IsAdmissible ρ)
    {φ : E → ℝ} (hi : Integrable φ (ρ : Measure E))
    (he : Integrable (fun x => Real.exp (φ x)) volume) :
    negEntropy (ρ : Measure E) = (klDiv (ρ : Measure E) (volume.tilted φ) : EReal) +
      ((∫ x, φ x ∂(ρ : Measure E)) - Real.log (∫ x, Real.exp (φ x)) : ℝ) := by
  let μ : Measure E := ρ
  let γ := (volume : Measure E).tilted φ
  let f := fun x : E => (μ.rnDeriv volume x).toReal * Real.log (μ.rnDeriv volume x).toReal
  have hγ : IsProbabilityMeasure γ := isProbabilityMeasure_tilted he
  have hμγ : μ ≪ γ := hρ.1.trans (absolutelyContinuous_tilted he)
  have hm : Measurable f := (Measure.measurable_rnDeriv μ volume).ennreal_toReal.mul
    (Real.measurable_log.comp (Measure.measurable_rnDeriv μ volume).ennreal_toReal)
  have hn : (∫⁻ x, ENNReal.ofReal (-f x)) ≠ ∞ := by
    have hb := negEntropyPart_bound hρ (a := 1) zero_lt_one
    exact (lt_of_le_of_lt hb (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hρ.2,
        (gaussian_integrable (E := E) (a := 1) zero_lt_one).lintegral_lt_top⟩)).ne
  change ((∫⁻ x, ENNReal.ofReal (f x)) : EReal) - ((∫⁻ x, ENNReal.ofReal (-f x)) : EReal) =
    (klDiv μ γ : EReal) + (((∫ x, φ x ∂μ) - Real.log (∫ x, Real.exp (φ x))) : ℝ)
  by_cases hf : Integrable f
  · have hl := (integrable_rnDeriv_mul_log_iff hρ.1).mp hf
    have ht := integrable_llr_tilted_right hρ.1 hi hl he
    have hkl := klDiv_ne_top hμγ ht
    rw [← EReal.coe_ennreal_toReal hf.lintegral_lt_top.ne, ← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_sub, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
      ← EReal.coe_ennreal_toReal hkl, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    rw [toReal_klDiv hμγ ht, probReal_univ, probReal_univ, add_sub_cancel_right]
    change (∫ x, (μ.rnDeriv volume x).toReal * Real.log (μ.rnDeriv volume x).toReal) = _
    rw [integral_rnDeriv_mul_log hρ.1, integral_llr_tilted_right hρ.1 hi he hl]
    ring
  · have hpos : (∫⁻ x, ENNReal.ofReal (f x)) = ∞ := by
      by_contra hp
      apply hf
      refine ⟨hm.aestronglyMeasurable, ?_⟩
      refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hp, hn.lt_top⟩)
      rw [← lintegral_add_left hm.ennreal_ofReal]
      apply lintegral_mono
      intro x
      rcases le_total 0 (f x) with hx | hx
      · simp [Real.eNorm_eq_ofReal hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx)]
      · simp [Real.eNorm_eq_ofReal_abs, abs_of_nonpos hx, ENNReal.ofReal_eq_zero.mpr hx]
    have hni : ¬ Integrable (llr μ γ) μ := by
      intro ht
      apply hf
      apply (integrable_rnDeriv_mul_log_iff hρ.1).mpr
      rw [integrable_congr (llr_tilted_right hρ.1 he)] at ht
      exact (ht.sub (hi.neg.add (integrable_const (Real.log (∫ x, Real.exp (φ x)))))).congr
        (ae_of_all _ fun x => by simp)
    rw [hpos, klDiv_of_not_integrable hni]
    simp [sub_eq_add_neg, hn]

/-! ## Strict convexity under mixtures -/

private noncomputable def mix {X : Type*} [MeasurableSpace X] (μ ν : ProbabilityMeasure X) :
    ProbabilityMeasure X :=
  ⟨(2 : ℝ≥0∞)⁻¹ • ((μ : Measure X) + (ν : Measure X)), ⟨by
    simp only [smul_apply, smul_eq_mul, add_apply, measure_univ]
    norm_num [ENNReal.inv_mul_cancel]⟩⟩

private theorem map_mix {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : ProbabilityMeasure X) {f : X → Y} (hf : Measurable f) :
    (mix μ ν).map f = mix (μ.map f) (ν.map f) := by
  apply Subtype.ext
  change Measure.map f ((2 : ℝ≥0∞)⁻¹ • ((μ : Measure X) + (ν : Measure X))) = _
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_add _ _ hf]
  rfl

private theorem kl_mix_lt {X : Type*} [MeasurableSpace X] (μ ν : ProbabilityMeasure X)
    (γ : Measure X) [IsProbabilityMeasure γ] (hne : μ ≠ ν)
    (hμ : klDiv (μ : Measure X) γ < ∞) (hν : klDiv (ν : Measure X) γ < ∞) :
    klDiv (mix μ ν : Measure X) γ < 2⁻¹ * (klDiv (μ : Measure X) γ + klDiv (ν : Measure X) γ) := by
  have hμa := (klDiv_ne_top_iff.mp hμ.ne).1
  have hνa := (klDiv_ne_top_iff.mp hν.ne).1
  have hma : (mix μ ν : Measure X) ≪ γ := (hμa.add_left hνa).smul_left _
  let f (μ : ProbabilityMeasure X) x := ((μ : Measure X).rnDeriv γ x).toReal
  let F (μ : ProbabilityMeasure X) x := ENNReal.ofReal (klFun (f μ x))
  have hF (m : ProbabilityMeasure X) : Measurable (F m) := by dsimp [F, f]; fun_prop
  have hm : f (mix μ ν) =ᵐ[γ] fun x => (1 / 2 : ℝ) * f μ x + (1 / 2 : ℝ) * f ν x := by
    filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ((μ : Measure X) + (ν : Measure X)) γ
      (show (2 : ℝ≥0∞)⁻¹ ≠ ∞ by simp), Measure.rnDeriv_add (μ : Measure X) ν γ,
      Measure.rnDeriv_lt_top (μ : Measure X) γ, Measure.rnDeriv_lt_top (ν : Measure X) γ]
      with x hx hy ht hu
    dsimp [f, mix]
    rw [hx, Pi.smul_apply, smul_eq_mul, hy, Pi.add_apply, ENNReal.toReal_mul,
      ENNReal.toReal_add ht.ne hu.ne]
    norm_num
    ring
  have hstrict : ∃ᵐ x ∂γ, f μ x ≠ f ν x := by
    by_contra! hall
    apply hne
    apply Subtype.ext
    change (μ : Measure X) = (ν : Measure X)
    rw [← Measure.withDensity_rnDeriv_eq (μ : Measure X) γ hμa,
      ← Measure.withDensity_rnDeriv_eq (ν : Measure X) γ hνa]
    apply withDensity_congr_ae
    filter_upwards [hall, Measure.rnDeriv_lt_top (μ : Measure X) γ,
      Measure.rnDeriv_lt_top (ν : Measure X) γ] with x hx h1 h2
    exact (ENNReal.toReal_eq_toReal_iff' h1.ne h2.ne).mp hx
  have hsum (x : X) :
      ENNReal.ofReal ((1 / 2 : ℝ) * klFun (f μ x) + (1 / 2 : ℝ) * klFun (f ν x)) =
      (2 : ℝ≥0∞)⁻¹ * (F μ x + F ν x) := by
    have h1 := klFun_nonneg (ENNReal.toReal_nonneg (a := (μ : Measure X).rnDeriv γ x))
    have h2 := klFun_nonneg (ENNReal.toReal_nonneg (a := (ν : Measure X).rnDeriv γ x))
    rw [← mul_add, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add h1 h2]
    simp [F, f, one_div, ENNReal.ofReal_inv_of_pos]
  have hle : F (mix μ ν) ≤ᵐ[γ] fun x => 2⁻¹ * (F μ x + F ν x) := by
    filter_upwards [hm] with x hx
    change ENNReal.ofReal (klFun (f (mix μ ν) x)) ≤ _
    rw [← hsum, hx]
    exact ENNReal.ofReal_le_ofReal (convexOn_klFun.2
      (show 0 ≤ f μ x from ENNReal.toReal_nonneg) (show 0 ≤ f ν x from ENNReal.toReal_nonneg)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  have hlt : ∃ᵐ x ∂γ, F (mix μ ν) x < 2⁻¹ * (F μ x + F ν x) := by
    apply (hstrict.and_eventually hm).mono
    rintro x ⟨hne', hx⟩
    change ENNReal.ofReal (klFun (f (mix μ ν) x)) < _
    rw [← hsum, hx]
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (klFun_nonneg (by positivity)) |>.mpr
    exact strictConvexOn_klFun.2
      (show 0 ≤ f μ x from ENNReal.toReal_nonneg) (show 0 ≤ f ν x from ENNReal.toReal_nonneg)
      hne' (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
  have hintegral : (∫⁻ x, 2⁻¹ * (F μ x + F ν x) ∂γ) =
      2⁻¹ * (klDiv (μ : Measure X) γ + klDiv (ν : Measure X) γ) := by
    rw [lintegral_const_mul (f := fun x => F μ x + F ν x) _ ((hF μ).add (hF ν)),
      lintegral_add_left (hF μ),
      klDiv_eq_lintegral_klFun_of_ac hμa, klDiv_eq_lintegral_klFun_of_ac hνa]
  rw [← hintegral, klDiv_eq_lintegral_klFun_of_ac hma]
  apply lintegral_strict_mono_of_ae_le_of_frequently_ae_lt _ _ hle (hlt.mono fun _ h => h.ne)
  · exact (measurable_const.mul ((hF μ).add (hF ν))).aemeasurable
  · apply ne_top_of_le_ne_top _ (lintegral_mono_ae hle)
    rw [hintegral]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨hμ.ne, hν.ne⟩)

/-! ## Minimization over transport plans with fixed first marginal -/

private noncomputable def loss (c : E × E → ℝ≥0∞) (k : ℝ≥0∞) (γ : Measure E)
    (π : ProbabilityMeasure (E × E)) :=
  (∫⁻ z, c z ∂(π : Measure (E × E))) + k * klDiv (π.map Prod.snd : Measure E) γ

private theorem compact_moment {X : Type*} [NormedAddCommGroup X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] {S : Set (ProbabilityMeasure X)} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hS : ∀ π ∈ S, (∫⁻ z, ‖z‖ₑ ^ 2 ∂(π : Measure X)) ≤ M) :
    IsCompact (closure S) := by
  apply isCompact_closure_of_isTightMeasureSet
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  lift M to ℝ≥0 using hM
  have hd : 0 < δ := by exact_mod_cast hδ
  let R : ℝ≥0 := max 1 ((M+1)/δ)
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  refine ⟨Metric.closedBall 0 (R : ℝ), isCompact_closedBall .., ?_⟩
  rintro _ ⟨π, hπ, rfl⟩
  have hs : (Metric.closedBall (0 : X) R)ᶜ ⊆ {z : X | (R : ℝ≥0∞) ≤ ‖z‖ₑ ^ 2} := by
    intro z hz
    have hz' : (R : ℝ) < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    change (R : ℝ≥0∞) ≤ ‖z‖ₑ ^ 2
    rw [eNorm_eq_nnNorm, ← ENNReal.coe_pow, ENNReal.coe_le_coe]
    have h : R ≤ ‖z‖₊ := by exact_mod_cast hz'.le
    exact h.trans <| le_self_pow₀ (hR.trans h) (by decide)
  refine (measure_mono hs).trans ((meas_ge_le_lintegral_div
    (f := fun z : X => ‖z‖ₑ ^ 2) (by fun_prop)
    (by exact_mod_cast hRpos.ne') ENNReal.coe_ne_top).trans ?_)
  refine le_trans (b := (M : ℝ≥0∞) / R) (by gcongr; exact hS π hπ) ?_
  refine le_trans ?_ hδε.le
  rw [← ENNReal.coe_div hRpos.ne', ENNReal.coe_le_coe]
  apply (div_le_iff₀ hRpos).mpr
  have h := (div_le_iff₀ hd).1 (le_max_right 1 ((M+1)/δ))
  rw [mul_comm]
  exact (self_le_add_right M 1).trans h

private theorem exists_plan {c : E × E → ℝ≥0∞} (hc : Continuous c)
    (hbound : ∀ z, ‖z‖ₑ ^ 2 ≤ 16 * c z) {k : ℝ≥0}
    (γ : Measure E) (hKL : LowerSemicontinuous (fun μ : ProbabilityMeasure E => klDiv μ γ))
    (μ : ProbabilityMeasure E) (π₀ : ProbabilityMeasure (E × E)) (hπ₀ : π₀.map Prod.fst = μ)
    (hfinite : loss c k γ π₀ < ∞) :
    ∃ π : ProbabilityMeasure (E × E), π.map Prod.fst = μ ∧ loss c k γ π < ∞ ∧
      ∀ π' : ProbabilityMeasure (E × E), π'.map Prod.fst = μ → loss c k γ π ≤ loss c k γ π' := by
  have hL : LowerSemicontinuous (loss c (k : ℝ≥0∞) γ) := by
    apply (MathlibExt.MeasureTheory.OptimalTransport.Existence.lowerSemicontinuous_lintegral
      hc).add
    exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous
      (hKL.comp (ProbabilityMeasure.continuous_map continuous_snd))
      (fun _ _ h => mul_le_mul_right h _)
  let u := loss c (k : ℝ≥0∞) γ π₀
  let S := {π : ProbabilityMeasure (E × E) | π.map Prod.fst = μ ∧ loss c k γ π ≤ u}
  have hs : IsClosed S :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
      (hL.isClosed_preimage u)
  have hb : ∀ π ∈ S, (∫⁻ z, ‖z‖ₑ ^ 2 ∂(π : Measure (E × E))) ≤ 16 * u := by
    intro π hπ
    calc
      _ ≤ ∫⁻ z, 16 * c z ∂(π : Measure (E × E)) := lintegral_mono hbound
      _ = 16 * ∫⁻ z, c z ∂(π : Measure (E × E)) := lintegral_const_mul _ hc.measurable
      _ ≤ _ := by
        gcongr
        exact (self_le_add_right _ _).trans hπ.2
  have hcompact := compact_moment (ENNReal.mul_ne_top (by norm_num) hfinite.ne) hb
  rw [hs.closure_eq] at hcompact
  have h₀ : π₀ ∈ S := ⟨hπ₀, le_rfl⟩
  obtain ⟨π, hπ, hmin⟩ := (hL.lowerSemicontinuousOn S).exists_isMinOn ⟨_, h₀⟩ hcompact
  refine ⟨π, hπ.1, hπ.2.trans_lt hfinite, ?_⟩
  intro π' hπ'
  rcases le_total (loss c k γ π') u with h | h
  · exact hmin ⟨hπ', h⟩
  · exact hπ.2.trans h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem plan_unique {c : E × E → ℝ≥0∞} {k : ℝ≥0} (hk : 0 < k)
    (γ : Measure E) [IsProbabilityMeasure γ] {π τ : ProbabilityMeasure (E × E)}
    (hfst : τ.map Prod.fst = π.map Prod.fst) (hf : loss c k γ π < ∞)
    (hmin : ∀ σ : ProbabilityMeasure (E × E), σ.map Prod.fst = π.map Prod.fst →
      loss c k γ π ≤ loss c k γ σ)
    (heq : loss c k γ τ = loss c k γ π) : π.map Prod.snd = τ.map Prod.snd := by
  by_contra hne
  have cut (σ : ProbabilityMeasure (E × E)) (h : loss c k γ σ < ∞) :
      klDiv (σ.map Prod.snd : Measure E) γ < ∞ := by
    have hh := (ENNReal.add_lt_top.mp h).2
    by_contra! he
    change (k : ℝ≥0∞) * klDiv (σ.map Prod.snd : Measure E) γ < ∞ at hh
    rw [top_le_iff.mp he, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hk.ne')] at hh
    exact hh.false
  have hlt := kl_mix_lt _ _ γ hne (cut _ hf) (cut _ (by rwa [heq]))
  have hmap : (mix π τ).map Prod.fst = π.map Prod.fst := by
    rw [map_mix _ _ measurable_fst, hfst]
    apply Subtype.ext
    change (2 : ℝ≥0∞)⁻¹ • (_ + _) = _
    ext s hs
    simp only [smul_apply, add_apply, smul_eq_mul, ← two_mul, ← mul_assoc]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    rfl
  have step := hmin _ hmap
  change loss c k γ π ≤ (∫⁻ z, c z ∂(mix π τ : Measure (E × E))) +
    ↑k * klDiv ((mix π τ).map Prod.snd : Measure E) γ at step
  rw [map_mix _ _ measurable_snd] at step
  change loss c k γ π ≤ (∫⁻ z, c z ∂((2 : ℝ≥0∞)⁻¹ •
    ((π : Measure (E × E)) + (τ : Measure (E × E))))) + _ at step
  rw [lintegral_smul_measure, lintegral_add_measure, smul_eq_mul] at step
  have hlt' := ENNReal.mul_lt_mul_right (ENNReal.coe_ne_zero.mpr hk.ne') ENNReal.coe_ne_top hlt
  have hh := ENNReal.add_lt_add_left (a := 2⁻¹ * ((∫⁻ z, c z ∂(π : Measure (E × E))) +
    ∫⁻ z, c z ∂(τ : Measure (E × E)) )) (by
      apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.add_ne_top.mpr ⟨(ENNReal.add_lt_top.mp hf).1.ne,
        (ENNReal.add_lt_top.mp (show loss c k γ τ < ∞ by rwa [heq])).1.ne⟩) hlt'
  apply (lt_irrefl (loss c k γ π)) (step.trans_lt (hh.trans_eq ?_))
  calc
    _ = 2⁻¹ * (loss c k γ π + loss c k γ τ) := by unfold loss; ring
    _ = _ := by
      rw [heq, ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ## The JKO objective in terms of transport plans -/

-- Subtract the second-moment term introduced by the tilted reference and add a term
-- depending only on the fixed first marginal. The resulting cost still controls both moments.
private noncomputable def quadratic (z : E × E) : ℝ :=
  dist z.1 z.2 ^ 2 / 2 + ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 / 8

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem sq_snd_le (z : E × E) :
    ‖z.2‖ ^ 2 ≤ 2 * (dist z.1 z.2 ^ 2 + ‖z.1‖ ^ 2) := by
  have hh : ‖z.2‖ ≤ dist z.1 z.2 + ‖z.1‖ := by
    simpa only [dist_zero_right, dist_comm z.2 z.1] using dist_triangle z.2 z.1 0
  have hs := pow_le_pow_left₀ (norm_nonneg z.2) hh 2
  nlinarith [sq_nonneg (dist z.1 z.2 - ‖z.1‖)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem quadratic_bound (z : E × E) : ‖z‖ ^ 2 ≤ 16 * quadratic z := by
  have hs := sq_snd_le z
  rw [Prod.norm_def, quadratic]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h <;> first | rw [max_eq_right h] | rw [max_eq_left h]
  all_goals
    nlinarith [sq_nonneg ‖z.1‖, sq_nonneg (dist z.1 z.2)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem quadratic_nonneg (z : E × E) : 0 ≤ quadratic z := by
  nlinarith [quadratic_bound z, sq_nonneg ‖z‖]

private noncomputable def cost (Ψ : E → ℝ) (h : ℝ) (z : E × E) : ℝ≥0∞ :=
  ENNReal.ofReal (quadratic z) + ENNReal.ofReal h * ENNReal.ofReal (Ψ z.2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cost_cont {Ψ : E → ℝ} (hc : Continuous Ψ) (h : ℝ) :
    Continuous (cost Ψ h) := by
  unfold cost
  have hQ : Continuous (quadratic (E := E)) := by unfold quadratic; fun_prop
  exact (ENNReal.continuous_ofReal.comp hQ).add
    ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp (hc.comp continuous_snd)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cost_bound (Ψ : E → ℝ) (h : ℝ) (z : E × E) : ‖z‖ₑ ^ 2 ≤ 16 * cost Ψ h z := by
  have hh := ENNReal.ofReal_le_ofReal (quadratic_bound z)
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_mul (by norm_num)] at hh
  refine hh.trans ?_
  norm_num
  exact mul_le_mul_right (self_le_add_right _ _) _

private theorem moment_integrable {μ : ProbabilityMeasure E} (hm : IsAdmissible μ) :
    Integrable (fun x : E => ‖x‖ ^ 2) (μ : Measure E) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [hasFiniteIntegral_iff_eNorm, Real.eNorm_eq_ofReal (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using! hm.2

private theorem int_quad {π : ProbabilityMeasure (E × E)}
    (h₁ : IsAdmissible (π.map Prod.fst)) (h₂ : IsAdmissible (π.map Prod.snd)) :
    Integrable (fun z : E × E => dist z.1 z.2 ^ 2) (π : Measure (E × E)) ∧
    Integrable quadratic (π : Measure (E × E)) ∧
    ∫ z, quadratic z ∂(π : Measure (E × E)) =
      (∫ z, dist z.1 z.2 ^ 2 ∂(π : Measure (E × E))) / 2 +
        (∫ x, ‖x‖ ^ 2 ∂(π.map Prod.fst : Measure E)) -
        (∫ x, ‖x‖ ^ 2 ∂(π.map Prod.snd : Measure E)) / 8 := by
  have hi₁ : Integrable (fun z : E × E => ‖z.1‖ ^ 2) (π : Measure (E × E)) :=
    (moment_integrable h₁).comp_measurable measurable_fst
  have hi₂ : Integrable (fun z : E × E => ‖z.2‖ ^ 2) (π : Measure (E × E)) :=
    (moment_integrable h₂).comp_measurable measurable_snd
  have hd : Integrable (fun z : E × E => dist z.1 z.2 ^ 2) (π : Measure (E × E)) := by
    apply ((hi₁.add hi₂).const_mul 2).mono' (by fun_prop)
    filter_upwards with z
    change ‖dist z.1 z.2 ^ 2‖ ≤ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hd' : dist z.1 z.2 ≤ ‖z.1‖ + ‖z.2‖ := dist_le_norm_add_norm ..
    have hs := pow_le_pow_left₀ dist_nonneg hd' 2
    nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖)]
  refine ⟨hd, ((hd.div_const 2).add hi₁).sub (hi₂.div_const 8), ?_⟩
  unfold quadratic
  simp only [ProbabilityMeasure.toMeasure_map, integral_map measurable_fst.aemeasurable
    (f := fun x : E => ‖x‖ ^ 2) (by fun_prop), integral_map measurable_snd.aemeasurable
    (f := fun x : E => ‖x‖ ^ 2) (by fun_prop)]
  rw [integral_sub (f := fun z : E × E => dist z.1 z.2 ^ 2 / 2 + ‖z.1‖ ^ 2)
    ((hd.div_const 2).add hi₁) (hi₂.div_const 8),
    integral_add (hd.div_const 2) hi₁, integral_div, integral_div]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem lintegral_sq_as_real {π : ProbabilityMeasure (E × E)}
    (hd : Integrable (fun z : E × E => dist z.1 z.2 ^ 2) (π : Measure (E × E))) :
    (∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π : Measure (E × E))) =
      ENNReal.ofReal (∫ z, dist z.1 z.2 ^ 2 ∂(π : Measure (E × E))) := by
  rw [ofReal_integral_eq_lintegral_ofReal hd (ae_of_all _ fun z => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow dist_nonneg, edist_dist, ENNReal.rpow_ofNat]

private noncomputable def tilt (k : ℝ) (x : E) := -(8 * k)⁻¹ * ‖x‖ ^ 2

private noncomputable def refLaw (k : ℝ) : Measure E := volume.tilted (tilt k)

private theorem tilt_integrable {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : E => Real.exp (tilt k x)) := gaussian_integrable (by positivity)

private noncomputable def shift (k : ℝ) (ρ : ProbabilityMeasure E) : ℝ :=
  (∫ x, ‖x‖ ^ 2 ∂(ρ : Measure E)) + k * Real.log (∫ x : E, Real.exp (tilt k x))

private noncomputable def planValue (Ψ : E → ℝ) (β h : ℝ) (π : ProbabilityMeasure (E × E)) :
    EReal :=
  ((∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π : Measure (E × E))) / 2 : ℝ≥0∞) +
    (h : EReal) * freeEnergy Ψ β (π.map Prod.snd : Measure E)

private theorem loss_eq (Ψ : E → ℝ) (hc : Continuous Ψ) {β h : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (π : ProbabilityMeasure (E × E)) (h₁ : IsAdmissible (π.map Prod.fst))
    (h₂ : IsAdmissible (π.map Prod.snd)) :
    (loss (cost Ψ h) (ENNReal.ofReal (h * β⁻¹)) (refLaw (h * β⁻¹)) π : EReal) =
      planValue Ψ β h π + (shift (h * β⁻¹) (π.map Prod.fst) : EReal) := by
  let k := h * β⁻¹
  have hk : 0 < k := mul_pos hh (inv_pos.mpr hβ)
  let m := π.map Prod.snd
  let G := refLaw (E := E) k
  let P := potentialEnergy Ψ (m : Measure E)
  let K := klDiv (m : Measure E) G
  let D := ∫ z, dist z.1 z.2 ^ 2 ∂(π : Measure (E × E))
  let X := ∫ x, ‖x‖ ^ 2 ∂(π.map Prod.fst : Measure E)
  let Y := ∫ x, ‖x‖ ^ 2 ∂(m : Measure E)
  let Z := Real.log (∫ x : E, Real.exp (tilt k x))
  obtain ⟨hd, hq, hv⟩ := int_quad h₁ h₂
  have he := negEntropy_tilt (φ := tilt k) h₂ ((moment_integrable h₂).const_mul (-(8 * k)⁻¹))
    (tilt_integrable hk)
  have hs : negEntropy (m : Measure E) = (K : EReal) + ((-(8 * k)⁻¹ * Y - Z : ℝ) : EReal) := by
    have hiφ : (∫ x, tilt k x ∂(m : Measure E)) = -(8 * k)⁻¹ * Y := integral_const_mul ..
    rw [hiφ] at he
    exact he
  have hQm : Measurable (fun z : E × E => ENNReal.ofReal (quadratic z)) := by
    unfold quadratic
    fun_prop
  have hL : (∫⁻ z, cost Ψ h z ∂(π : Measure (E × E))) =
      ENNReal.ofReal (D / 2 + X - Y / 8) + ENNReal.ofReal h * P := by
    unfold cost
    rw [lintegral_add_left hQm, ← ofReal_integral_eq_lintegral_ofReal hq
      (ae_of_all _ quadratic_nonneg), hv]
    congr 1
    rw [lintegral_const_mul _ (f := fun z : E × E => ENNReal.ofReal (Ψ z.2))
      (hc.measurable.comp measurable_snd |>.ennreal_ofReal)]
    congr 1
    exact (lintegral_map hc.measurable.ennreal_ofReal measurable_snd).symm
  have hq0 : 0 ≤ D / 2 + X - Y / 8 := hv ▸ integral_nonneg quadratic_nonneg
  have hd0 : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  unfold planValue freeEnergy loss
  rw [hL, lintegral_sq_as_real hd, hs]
  have hd' : ENNReal.ofReal D / 2 = ENNReal.ofReal (D / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change (↑((ENNReal.ofReal (D / 2 + X - Y / 8) + ENNReal.ofReal h * P) +
    ENNReal.ofReal k * K) : EReal) =
    (↑(ENNReal.ofReal D / 2) + (h : EReal) *
      ((P : EReal) + (β⁻¹ : ℝ) * ((K : EReal) + ((-(8 * k)⁻¹ * Y - Z : ℝ) : EReal)))) +
      ((X + k * Z : ℝ) : EReal)
  rw [hd']
  simp only [EReal.coe_ennreal_add, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left hq0, max_eq_left hh.le, max_eq_left hk.le,
    max_eq_left (div_nonneg hd0 (by norm_num : (0 : ℝ) ≤ 2))]
  have hki : k * (8 * k)⁻¹ = 1 / 8 := by field_simp [hk.ne']
  by_cases ht : K = ∞ <;> by_cases hp : P = ∞
  all_goals first | rw [ht] | rw [← EReal.coe_ennreal_toReal ht]
  all_goals first | rw [hp] | rw [← EReal.coe_ennreal_toReal hp]
  all_goals simp only [EReal.coe_ennreal_top, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_mul_top_of_pos hh, EReal.coe_mul_top_of_pos hk,
    EReal.coe_mul_top_of_pos (inv_pos.mpr hβ), EReal.top_add_top, EReal.top_add_coe,
    EReal.coe_add_top, EReal.coe_eq_coe_iff]
  change D / 2 + X - Y / 8 + h * P.toReal + k * K.toReal = _
  dsimp [k] at hki ⊢
  linear_combination (norm := ring_nf) Y * hki

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem wasserstein_sq (μ ν : ProbabilityMeasure E) :
    wasserstein 2 μ ν ^ (2 : ℝ) = transportCost 2 μ ν := by
  rw [wasserstein, ← ENNReal.rpow_mul]
  norm_num

private theorem exists_opt_plan (Ψ : E → ℝ) (β h : ℝ) (μ ν : ProbabilityMeasure E) :
    ∃ π : ProbabilityMeasure (E × E), π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      planValue Ψ β h π = jkoObjective Ψ β h μ ν := by
  obtain ⟨π, ⟨h1, h2⟩, hc⟩ :=
    MathlibExt.MeasureTheory.OptimalTransport.Existence.exists_isCoupling_lintegral_eq_transportCost
      2 μ ν
  have hfst : π.map Prod.fst = μ := Subtype.ext h1.symm
  have hsnd : π.map Prod.snd = ν := Subtype.ext h2.symm
  exact ⟨π, hfst, hsnd, by rw [planValue, jkoObjective, hsnd, hc, wasserstein_sq]⟩

private theorem objective_le_plan (Ψ : E → ℝ) (β h : ℝ) (π : ProbabilityMeasure (E × E)) :
    jkoObjective Ψ β h (π.map Prod.fst) (π.map Prod.snd) ≤ planValue Ψ β h π := by
  rw [jkoObjective, wasserstein_sq, planValue]
  apply add_le_add_left
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  gcongr
  exact transportCost_le_of_isCoupling ⟨rfl, rfl⟩

-- Condition the reference law on the unit ball. Both the potential and its density relative
-- to the reference are bounded on that ball.
private theorem exists_trial {Ψ : E → ℝ} (hc : Continuous Ψ) (h : ℝ) {k : ℝ} (hk : 0 < k)
    {μ : ProbabilityMeasure E} (hμ : IsAdmissible μ) :
    ∃ π : ProbabilityMeasure (E × E), π.map Prod.fst = μ ∧
      loss (cost Ψ h) (ENNReal.ofReal k) (refLaw k) π < ∞ := by
  let γ := refLaw (E := E) k
  have : IsProbabilityMeasure γ := isProbabilityMeasure_tilted (tilt_integrable hk)
  let B := Metric.closedBall (0 : E) 1
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBe : γ B ≠ 0 := by
    intro h0
    exact (Metric.measure_closedBall_pos volume (0 : E) one_pos).ne'
      (absolutelyContinuous_tilted (tilt_integrable hk) h0)
  let ν : ProbabilityMeasure E := ⟨ProbabilityTheory.cond γ B,
    ProbabilityTheory.cond_isProbabilityMeasure hBe⟩
  have hmass : ∀ᵐ x ∂(ν : Measure E), x ∈ B := ProbabilityTheory.ae_cond_mem hB
  have hνγ : (ν : Measure E) ≪ γ := ProbabilityTheory.cond_absolutelyContinuous
  have hν : IsAdmissible ν := by
    refine ⟨hνγ.trans (tilted_absolutelyContinuous _ _), ?_⟩
    have hnorm : ∀ᵐ x ∂(ν : Measure E), ‖x‖ₑ ^ 2 ≤ 1 := by
      filter_upwards [hmass] with x hx
      have h := Metric.mem_closedBall.mp hx
      simp only [dist_zero_right] at h
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_one.mpr (by simpa using pow_le_pow_left₀ (norm_nonneg x) h 2)
    exact (lintegral_mono_ae hnorm).trans_lt (by simp)
  have hK : klDiv (ν : Measure E) γ ≠ ∞ := by
    apply klDiv_ne_top hνγ
    apply (integrable_const (Real.log (γ B)⁻¹.toReal)).congr
    have h1 := Measure.rnDeriv_smul_left_of_ne_top (γ.restrict B) γ (ENNReal.inv_ne_top.mpr hBe)
    filter_upwards [hνγ.ae_le h1, hνγ.ae_le (Measure.rnDeriv_restrict_self γ hB), hmass]
      with x hx hy hxB
    change _ = Real.log (((γ B)⁻¹ • γ.restrict B).rnDeriv γ x).toReal
    rw [hx, Pi.smul_apply, smul_eq_mul, hy, Set.indicator_of_mem hxB]
    simp
  let π := μ.prod ν
  have hf : π.map Prod.fst = μ := ProbabilityMeasure.map_fst_prod μ ν
  have hs : π.map Prod.snd = ν := ProbabilityMeasure.map_snd_prod μ ν
  have hi := (int_quad (hf.symm ▸ hμ) (hs.symm ▸ hν)).2.1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hc.continuousOn
  have hpot : (∫⁻ x, ENNReal.ofReal (Ψ x) ∂(ν : Measure E)) < ∞ := by
    refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal C) ?_).trans_lt (by simp)
    filter_upwards [hmass] with x hx
    exact ENNReal.ofReal_le_ofReal ((le_abs_self (Ψ x)).trans (hC x hx))
  refine ⟨π, hf, ?_⟩
  unfold loss cost
  rw [hs, lintegral_add_left (f := fun z : E × E => ENNReal.ofReal (quadratic z))
    (by unfold quadratic; fun_prop), lintegral_const_mul _ (f := fun z : E × E =>
      ENNReal.ofReal (Ψ z.2)) (hc.measurable.comp measurable_snd |>.ennreal_ofReal)]
  have he : (∫⁻ z, ENNReal.ofReal (Ψ z.2) ∂(π : Measure (E × E))) =
      ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(ν : Measure E) := by
    rw [← hs, ProbabilityMeasure.toMeasure_map, lintegral_map hc.measurable.ennreal_ofReal
      measurable_snd]
  rw [he]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨hi.lintegral_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpot⟩,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.lt_top⟩

private theorem admissible_snd {Ψ : E → ℝ} (hc : Continuous Ψ) {k h : ℝ} (hk : 0 < k)
    {π : ProbabilityMeasure (E × E)}
    (hπ : loss (cost Ψ h) (ENNReal.ofReal k) (refLaw k) π < ∞) : IsAdmissible (π.map Prod.snd) := by
  obtain ⟨hi, hk'⟩ := ENNReal.add_lt_top.mp hπ
  have ht : klDiv (π.map Prod.snd : Measure E) (refLaw k) ≠ ∞ := by
    intro ht
    change ENNReal.ofReal k * klDiv (π.map Prod.snd : Measure E) (refLaw k) < ∞ at hk'
    rw [ht, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hk)] at hk'
    exact hk'.false
  refine ⟨(klDiv_ne_top_iff.mp ht).1.trans (tilted_absolutelyContinuous ..), ?_⟩
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map (f := fun x : E => ‖x‖ₑ ^ 2)
    (by fun_prop) measurable_snd]
  calc
    _ ≤ ∫⁻ z, 16 * cost Ψ h z ∂(π : Measure (E × E)) := by
      apply lintegral_mono
      intro z
      refine le_trans ?_ (cost_bound Ψ h z)
      change ‖z.2‖ₑ ^ 2 ≤ ‖z‖ₑ ^ 2
      apply pow_le_pow_left' _ 2
      rw [← ofReal_norm, ← ofReal_norm, Prod.norm_def]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    _ < ∞ := by
      rw [lintegral_const_mul _ (cost_cont hc h).measurable]
      exact ENNReal.mul_lt_top (by norm_num) hi

open MathlibExt.InformationTheory.DonskerVaradhan
open scoped BoundedContinuousFunction

-- Approximate the bounded measurable tests in the variational formula simultaneously in
-- the two measures. Clipping the approximants permits dominated convergence after exponentiation.
private theorem kl_lsc (γ : Measure E) [IsProbabilityMeasure γ] :
    LowerSemicontinuous fun μ : ProbabilityMeasure E => klDiv (μ : Measure E) γ := by
  let V (μ : ProbabilityMeasure E) (f : E → ℝ) :=
    ENNReal.ofReal ((∫ x, f x ∂(μ : Measure E)) - Real.log (∫ x, Real.exp (f x) ∂γ))
  have hV (μ : ProbabilityMeasure E) :
      klDiv (μ : Measure E) γ = ⨆ g : E →ᵇ ℝ, V μ g := by
    refine le_antisymm ?_ (iSup_le fun g => ofReal_integral_sub_log_integral_exp_le_klDiv
      g.continuous.measurable (fun x => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x))
    rw [klDiv_eq_iSup]
    refine iSup₂_le fun f ⟨hf, C, hC⟩ => ?_
    let η := (μ : Measure E) + γ
    have hf₁ := (memLp_one_iff_integrable.mpr (integrable_of_bounded (μ := η) hf hC).1)
    let r := (2 : ℝ≥0∞)⁻¹
    have hr (n : ℕ) : r ^ n ≠ 0 := pow_ne_zero n (by simp [r])
    choose g hg _ using fun n => hf₁.exists_boundedContinuous_eLpNorm_sub_le (by simp) (hr n)
    have hg' : Tendsto (fun n => eLpNorm ((g n : E → ℝ) - f) 1 η) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (show r < 1 by norm_num [r])) (by simp)
      exact Eventually.of_forall fun n => (eLpNorm_sub_comm ..).le.trans (hg n)
    obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by simp) hg').exists_seq_tendsto_ae
    let clip (t : ℝ) := min (max (-C) t) C
    have hclip : LipschitzWith 1 clip := (LipschitzWith.id.const_max (-C)).min_const C
    have hC₀ := (abs_nonneg (f 0)).trans (hC 0)
    let u (n : ℕ) := BoundedContinuousFunction.comp clip hclip (g (ns n))
    have hb (n : ℕ) (x : E) : |u n x| ≤ C :=
      abs_le.mpr ⟨le_min (le_max_left ..) (by linarith), min_le_right ..⟩
    have hu : ∀ᵐ x ∂η, Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
      filter_upwards [hns] with x hx
      have he : clip (f x) = f x := by
        simp [clip, max_eq_right (abs_le.mp (hC x)).1, min_eq_left (abs_le.mp (hC x)).2]
      rw [← he]
      exact (hclip.continuous.tendsto _).comp hx
    have hi : Tendsto (fun n => ∫ x, u n x ∂(μ : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) :=
      tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (u n).continuous.aestronglyMeasurable) (integrable_const _)
        (fun n => ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb n x)
        ((Measure.AbsolutelyContinuous.rfl.add_right γ).ae_le hu)
    have he : Tendsto (fun n => ∫ x, Real.exp (u n x) ∂γ) atTop (𝓝 (∫ x, Real.exp (f x) ∂γ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp C)
        (fun n => (Real.continuous_exp.comp (u n).continuous).aestronglyMeasurable)
        (integrable_const _)
      · intro n
        exact ae_of_all _ fun x => by
          simpa using Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n x))
      · have huγ : ∀ᵐ x ∂γ, Tendsto (fun n => u n x) atTop (𝓝 (f x)) :=
          (Measure.AbsolutelyContinuous.rfl.add_right' (μ : Measure E)).ae_le hu
        exact huγ.mono fun _ hx => Real.continuous_exp.continuousAt.tendsto.comp hx
    have hpos := (MeasureTheory.integral_exp_pos (integrable_of_bounded (μ := γ) hf hC).2).ne'
    apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp (hi.sub (he.log hpos)))
    exact Eventually.of_forall fun n => le_iSup (fun g : E →ᵇ ℝ => V μ g) (u n)
  simp_rw [hV]
  apply lowerSemicontinuous_iSup
  intro g
  exact (ENNReal.continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).sub
      continuous_const)).lowerSemicontinuous

private theorem step_of_plan {Ψ : E → ℝ} (hc : Continuous Ψ) {β h : ℝ} (hβ : 0 < β)
    (hh : 0 < h) {μ : ProbabilityMeasure E} (hμ : IsAdmissible μ) :
    ∃! ρ : ProbabilityMeasure E, IsJKOStep Ψ β h μ ρ := by
  let k := h * β⁻¹
  have hk : 0 < k := mul_pos hh (inv_pos.mpr hβ)
  let γ := refLaw (E := E) k
  have : IsProbabilityMeasure γ := isProbabilityMeasure_tilted (tilt_integrable hk)
  let L := loss (cost Ψ h) (ENNReal.ofReal k) γ
  obtain ⟨τ, hτ, ht⟩ := exists_trial hc h hk hμ
  obtain ⟨π, hp, hfinite, hmin⟩ := exists_plan (k := k.toNNReal) (cost_cont hc h)
    (cost_bound Ψ h) γ (kl_lsc γ) μ τ hτ ht
  have ha := admissible_snd hc hk hfinite
  have hshift {σ : ProbabilityMeasure (E × E)} (hfst : σ.map Prod.fst = μ)
      (had : IsAdmissible (σ.map Prod.snd)) :
      (L σ : EReal) = planValue Ψ β h σ + (shift k μ : EReal) := by
    simpa only [L, hfst] using loss_eq Ψ hc hβ hh σ (hfst.symm ▸ hμ) had
  have hle {σ : ProbabilityMeasure (E × E)} (hfst : σ.map Prod.fst = μ)
      (had : IsAdmissible (σ.map Prod.snd)) : planValue Ψ β h π ≤ planValue Ψ β h σ := by
    apply (EReal.addLECancellable_coe (shift k μ)).add_le_add_iff_right.mp
    rw [← hshift hp ha, ← hshift hfst had]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin σ hfst)
  have hj : jkoObjective Ψ β h μ (π.map Prod.snd) ≤ planValue Ψ β h π := by
    simpa only [hp] using objective_le_plan Ψ β h π
  refine ⟨π.map Prod.snd, ⟨ha, ?_⟩, ?_⟩
  · intro ν hν
    obtain ⟨σ, hfst, hsnd, hV⟩ := exists_opt_plan Ψ β h μ ν
    exact hj.trans ((hle hfst (hsnd.symm ▸ hν)).trans_eq hV)
  · intro ν hν
    obtain ⟨σ, hfst, hsnd, hV⟩ := exists_opt_plan Ψ β h μ ν
    have had := hsnd.symm ▸ hν.1
    have hle' : planValue Ψ β h σ ≤ planValue Ψ β h π := hV.le.trans ((hν.2 _ ha).trans hj)
    have he : L σ = L π := by
      apply EReal.coe_ennreal_eq_coe_ennreal_iff.mp
      rw [hshift hp ha, hshift hfst had, le_antisymm hle' (hle hfst had)]
    have heq := plan_unique (k := k.toNNReal) (Real.toNNReal_pos.mpr hk) γ (hfst.trans hp.symm)
      hfinite (fun σ hf => hmin σ (hf.trans hp)) he
    exact hsnd.symm.trans heq.symm

end

open scoped ContDiff

-- The fixed statement includes the standing assumptions on the potential from the JKO scheme.
set_option linter.unusedVariables false in
/-- **Existence and uniqueness of the JKO step.** Let `Ψ : E → ℝ` be smooth (`C^∞`), nonnegative,
with `|∇Ψ| ≤ C (Ψ + 1)`, and let `β > 0` and `h > 0`. For every admissible `ρ₀` (absolutely
continuous with finite second moment) there is exactly one admissible `ρ` minimizing
`½ W₂(ρ₀, ρ)² + h F(ρ)` over the admissible set, where `F(ρ) = ∫ Ψ ρ + β⁻¹ ∫ ρ log ρ`
(R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
equation*, SIAM J. Math. Anal. 29 (1998), Proposition 4.1, under the assumptions of Section 4). -/
public theorem existsUnique_isJKOStep {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ψ : E → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨ0 : ∀ x, 0 ≤ Ψ x)
    (hΨgrad : ∃ C : ℝ, ∀ x, ‖fderiv ℝ Ψ x‖ ≤ C * (Ψ x + 1))
    {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (ρ₀ : ProbabilityMeasure E) (hρ₀ : IsAdmissible ρ₀) :
    ∃! ρ : ProbabilityMeasure E, IsJKOStep Ψ β h ρ₀ ρ :=
  step_of_plan hΨ.continuous hβ hh hρ₀

end MathlibExt.Probability.Diffusion.JKOSchemeWanted
