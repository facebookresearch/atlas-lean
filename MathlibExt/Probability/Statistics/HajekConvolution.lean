/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Probability.Moments.IntegrableExpMul
import MathlibExt.Probability.Statistics.Contiguity

/-!
# Hájek's convolution theorem

`hajek_convolution`: in a locally asymptotically normal (LAN) sequence of experiments with a
one-dimensional local parameter `h` and information `I > 0`, the limit law `L` of every regular
estimator sequence is a convolution `N(0, I⁻¹) ∗ M`; so `N(0, I⁻¹)` is the best possible limit
(J. Hájek, "A characterization of limiting distributions of regular estimates",
*Z. Wahrscheinlichkeitstheorie verw. Geb.* 14 (1970) 323–330).

LAN is stated through log-likelihood ratios `log dP_{n,h}/dP_{n,0}` (Mathlib's `llr`).
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.Statistics.EfficiencyWanted

private theorem tight_of_tendsto {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X} (h : Tendsto μ atTop (𝓝 ν)) :
    IsTightMeasureSet (range fun n => (μ n : Measure X)) := by
  have hcl : IsCompact (closure (range μ)) :=
    h.isCompact_insert_range.closure_of_subset (subset_insert _ _)
  simpa [Set.range] using isTightMeasureSet_of_isCompact_closure hcl

private theorem joint_limit {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ℕ → ProbabilityMeasure (X × Y)) {ν : ProbabilityMeasure X} {ρ : ProbabilityMeasure Y}
    (h₁ : Tendsto (fun n => (μ n).map Prod.fst) atTop (𝓝 ν))
    (h₂ : Tendsto (fun n => (μ n).map Prod.snd) atTop (𝓝 ρ)) :
    ∃ (π : ProbabilityMeasure (X × Y)) (s : ℕ → ℕ), StrictMono s ∧
      Tendsto (μ ∘ s) atTop (𝓝 π) ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = ρ := by
  have ht : IsTightMeasureSet (range fun n => (μ n : Measure (X × Y))) := by
    apply IsTightMeasureSet.prodMk
    · simpa [← range_comp, Function.comp_def, Measure.fst] using tight_of_tendsto h₁
    · simpa [← range_comp, Function.comp_def, Measure.snd] using tight_of_tendsto h₂
  have hc : IsCompact (closure (range μ)) := isCompact_closure_of_isTightMeasureSet (by
    simpa [Set.range] using ht)
  obtain ⟨π, _, s, hs, hπ⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨π, s, hs, hπ, ?_, ?_⟩
  · exact tendsto_nhds_unique ((ProbabilityMeasure.continuous_map continuous_fst).tendsto π
      |>.comp hπ) (h₁.comp hs.tendsto_atTop)
  · exact tendsto_nhds_unique ((ProbabilityMeasure.continuous_map continuous_snd).tendsto π
      |>.comp hπ) (h₂.comp hs.tendsto_atTop)

private theorem law_pair_fst {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (P : ProbabilityMeasure Ω) {f : Ω → X} {g : Ω → Y}
    (hf : Measurable f) (hg : Measurable g) :
    (P.map (fun x => (f x, g x))).map Prod.fst = P.map f :=
  Subtype.ext (Measure.map_map measurable_fst (hf.prodMk hg))

private theorem law_pair_snd {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (P : ProbabilityMeasure Ω) {f : Ω → X} {g : Ω → Y}
    (hf : Measurable f) (hg : Measurable g) :
    (P.map (fun x => (f x, g x))).map Prod.snd = P.map g :=
  Subtype.ext (Measure.map_map measurable_snd (hf.prodMk hg))

private theorem law_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) (E : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (E n))
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n : Measure (Ω n)) {ω | ε ≤ |E n ω|})
      atTop (𝓝 0)) :
    Tendsto (fun n => (P n).map (E n)) atTop (𝓝 ⟨Measure.dirac 0, inferInstance⟩) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  by_cases hz : (0 : ℝ) ∈ F
  · simpa [Measure.dirac_apply' _ hF.measurableSet, hz] using
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n =>
        prob_le_one (μ := ((P n).map (E n) : Measure ℝ)) (s := F)))
  · obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hF.isOpen_compl 0 hz
    have hbnd (n : ℕ) : ((P n).map (E n) : Measure ℝ) F ≤
        (P n : Measure (Ω n)) {ω | ε ≤ |E n ω|} := by
      rw [ProbabilityMeasure.map_apply' _ (hm n).aemeasurable hF.measurableSet]
      apply measure_mono
      intro ω hω
      change ε ≤ |E n ω|
      apply le_of_not_gt
      intro hn
      exact hb (by simpa [Real.dist_eq] using hn) hω
    simpa [Measure.dirac_apply' _ hF.measurableSet, hz] using
      (show limsup (fun n => ((P n).map (E n) : Measure ℝ) F) atTop ≤ 0 from
        ((Filter.limsup_le_limsup (Eventually.of_forall hbnd))).trans
          (h ε hε).limsup_eq.le)

-- The cutoff vanishes at zero, where the real logarithm also represents zero likelihood.
private noncomputable def cut (k : ℕ) (u : ℝ) : ℝ := min (Real.exp u) (k * min |u| 1)

private theorem cut_nonneg (k : ℕ) (u : ℝ) : 0 ≤ cut k u := by
  unfold cut
  positivity

private theorem cut_le (k : ℕ) (u : ℝ) : cut k u ≤ k :=
  (min_le_right _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left (min_le_right |u| 1) k.cast_nonneg)

private theorem cut_limit (u : ℝ) (hu : u ≠ 0) :
    Tendsto (fun k => cut k u) atTop (𝓝 (Real.exp u)) := by
  have hp : 0 < min |u| 1 := lt_min (abs_pos.mpr hu) one_pos
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌈Real.exp u / min |u| 1⌉₊] with k hk
  exact (min_eq_left ((div_le_iff₀ hp).mp ((Nat.le_ceil _).trans (by exact_mod_cast hk)))).symm

private theorem cut_integral_le {Ω : Type*} [MeasurableSpace Ω] (P Q : ProbabilityMeasure Ω)
    (U : Ω → ℝ) (hU : Measurable U) (f : ℝ →ᵇ ℝ) (hf : 0 ≤ f) (k : ℕ) :
    ∫ ω, cut k (llr (Q : Measure Ω) P ω) * f (U ω) ∂(P : Measure Ω) ≤
      ∫ ω, f (U ω) ∂(Q : Measure Ω) := by
  let w := fun ω => ENNReal.ofReal (cut k (llr (Q : Measure Ω) P ω))
  have hm : Measurable w := by dsimp [w, cut]; fun_prop
  have hw : ∀ ω, w ω ≤ (Q : Measure Ω).rnDeriv P ω := by
    intro ω
    dsimp [w, cut, llr_def]
    by_cases hz : ((Q : Measure Ω).rnDeriv P ω).toReal = 0
    · simp [hz]
    · grw [min_le_left, Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))]
      exact ENNReal.ofReal_toReal_le
  have hle : (P : Measure Ω).withDensity w ≤ Q :=
    (withDensity_mono (Eventually.of_forall hw)).trans (Measure.withDensity_rnDeriv_le _ _)
  have hi : Integrable (fun ω => f (U ω)) (Q : Measure Ω) :=
    Integrable.of_bound (by fun_prop) ‖f‖ (Eventually.of_forall fun ω => f.norm_coe_le_norm _)
  have hb := integral_mono_measure hle (Eventually.of_forall fun ω => hf (U ω)) hi
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hb
  simpa only [w, ENNReal.toReal_ofReal (cut_nonneg _ _), smul_eq_mul] using! hb

-- Every cutoff gives a lower bound under the alternative, including its singular part.
-- Bounded convergence in law followed by dominated convergence removes the cutoff.
private theorem change_measure_le {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, ProbabilityMeasure (Ω n)) (U : ∀ n, Ω n → ℝ) (hU : ∀ n, Measurable (U n))
    (π : ProbabilityMeasure (ℝ × ℝ)) (L : ProbabilityMeasure ℝ)
    (hπ : Tendsto (fun n => (P n).map (fun ω => (U n ω, llr (Q n : Measure _) (P n) ω)))
      atTop (𝓝 π))
    (hL : Tendsto (fun n => (Q n).map (U n)) atTop (𝓝 L))
    (hz : ∀ᵐ z ∂(π : Measure (ℝ × ℝ)), z.2 ≠ 0)
    (hi : Integrable (fun z => Real.exp z.2) (π : Measure (ℝ × ℝ)))
    (f : ℝ →ᵇ ℝ) (hf : 0 ≤ f) :
    ∫ z, Real.exp z.2 * f z.1 ∂(π : Measure (ℝ × ℝ)) ≤ ∫ x, f x ∂(L : Measure ℝ) := by
  have hk (k : ℕ) : ∫ z, cut k z.2 * f z.1 ∂(π : Measure (ℝ × ℝ)) ≤ ∫ x, f x ∂(L : Measure ℝ) := by
    let g := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : ℝ × ℝ => cut k z.2 * f z.1) (by unfold cut; fun_prop) (k * ‖f‖) (fun z => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg _ _)]
        exact mul_le_mul (cut_le _ _) (f.norm_coe_le_norm _) (norm_nonneg _) k.cast_nonneg)
    apply le_of_tendsto_of_tendsto' (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hπ g)
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL f)
    intro n
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [integral_map ((hU n).prodMk (measurable_llr _ _)).aemeasurable
          g.continuous.aestronglyMeasurable, integral_map (hU n).aemeasurable
          f.continuous.aestronglyMeasurable]
    exact cut_integral_le (P n) (Q n) (U n) (hU n) f hf k
  apply le_of_tendsto' (x := atTop) _ hk
  apply tendsto_integral_of_dominated_convergence (fun z => Real.exp z.2 * ‖f‖)
  · intro k
    unfold cut
    fun_prop
  · exact hi.mul_const _
  · intro k
    apply Eventually.of_forall
    intro z
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg _ _)]
    exact mul_le_mul (min_le_left _ _) (f.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos _).le
  · filter_upwards [hz] with z h
    exact (cut_limit z.2 h).mul_const _

-- Along a further subsequence the LAN remainder has joint limit zero with the data.
private theorem lan_joint {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, ProbabilityMeasure (Ω n)) (D : ∀ n, Ω n → ℝ × ℝ)
    (hD : ∀ n, Measurable (D n)) (J : ProbabilityMeasure (ℝ × ℝ))
    (hj : Tendsto (fun n => (P n).map (D n)) atTop (𝓝 J))
    (a b : (ℝ × ℝ) → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hLAN : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n : Measure (Ω n))
      {ω | ε ≤ |llr (Q n : Measure _) (P n) ω - a (D n ω)|}) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun n => (P (s n)).map (fun ω =>
        (b (D (s n) ω), llr (Q (s n) : Measure _) (P (s n)) ω)))
        atTop (𝓝 (J.map (fun x => (b x, a x)))) := by
  let E := fun n ω => llr (Q n : Measure _) (P n) ω - a (D n ω)
  have hE (n : ℕ) : Measurable (E n) := (measurable_llr _ _).sub (ha.measurable.comp (hD n))
  let μ := fun n => (P n).map (fun ω => (D n ω, E n ω))
  obtain ⟨K, s, hs, hk, hk₁, hk₂⟩ := joint_limit μ
    (by simpa only [μ, law_pair_fst _ (hD _) (hE _)] using hj)
    (by simpa only [μ, law_pair_snd _ (hD _) (hE _)] using law_zero P E hE hLAN)
  let g := fun z : (ℝ × ℝ) × ℝ => (b z.1, z.2 + a z.1)
  have hg : Continuous g := (hb.comp continuous_fst).prodMk (continuous_snd.add
    (ha.comp continuous_fst))
  have hzero : ∀ᵐ z ∂(K : Measure ((ℝ × ℝ) × ℝ)), z.2 = 0 := by
    apply ae_of_ae_map (f := Prod.snd) (p := fun y : ℝ => y = 0) measurable_snd.aemeasurable
    change ∀ᵐ y ∂((K.map Prod.snd : ProbabilityMeasure ℝ) : Measure ℝ), y = 0
    rw [hk₂]
    simp
  have hpush : K.map g = J.map (fun x => (b x, a x)) := by
    rw [← hk₁]
    apply Subtype.ext
    exact (Measure.map_congr (hzero.mono fun z hz => by simp [g, hz])).trans
      (Measure.map_map (hb.prodMk ha).measurable measurable_fst).symm
  have hl := (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hk hg)
  rw [hpush] at hl
  refine ⟨s, hs, hl.congr fun n => ?_⟩
  apply Subtype.ext
  change (((P (s n) : Measure (Ω (s n))).map _).map g) = (P (s n) : Measure (Ω (s n))).map _
  rw [Measure.map_map hg.measurable ((hD _).prodMk (hE _))]
  simp [g, E, Function.comp_def]

private theorem tilt_charFun {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, ProbabilityMeasure (Ω n)) (U : ∀ n, Ω n → ℝ) (hU : ∀ n, Measurable (U n))
    (π : ProbabilityMeasure (ℝ × ℝ)) (L : ProbabilityMeasure ℝ)
    (hπ : Tendsto (fun n => (P n).map (fun ω => (U n ω, llr (Q n : Measure _) (P n) ω)))
      atTop (𝓝 π))
    (hL : Tendsto (fun n => (Q n).map (U n)) atTop (𝓝 L))
    (hz : ∀ᵐ z ∂(π : Measure (ℝ × ℝ)), z.2 ≠ 0)
    (h₁ : ∫⁻ z, ENNReal.ofReal (Real.exp z.2) ∂(π : Measure (ℝ × ℝ)) = 1) (t : ℝ) :
    (∫ z, (Real.exp z.2 : ℂ) * Complex.exp (t * z.1 * Complex.I)
      ∂(π : Measure (ℝ × ℝ))) = charFun (L : Measure ℝ) t := by
  let w := fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.2)
  let ν := (π : Measure (ℝ × ℝ)).withDensity w
  have : IsProbabilityMeasure ν := ⟨by simpa [ν, w, withDensity_apply] using h₁⟩
  let ρ : ProbabilityMeasure ℝ := ⟨ν.map Prod.fst, inferInstance⟩
  have hi : Integrable (fun z => Real.exp z.2) (π : Measure (ℝ × ℝ)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le), h₁]
    exact ENNReal.one_lt_top
  -- The tilted limit has mass one, so the lower bounds on nonnegative tests determine its law.
  have heq : L = ρ := by
    apply tendsto_nhds_unique (tendsto_const_nhds (x := L) (f := atTop (α := ℕ)))
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    apply BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral
    intro f hf
    change ∫ x, f x ∂(ν.map Prod.fst) ≤ _
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable, liminf_const,
      integral_withDensity_eq_integral_toReal_smul (show Measurable w by dsimp [w]; fun_prop)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [w, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using!
      change_measure_le P Q U hU π L hπ hL hz hi f hf
  rw [heq, charFun_apply_real]
  change _ = ∫ x, _ ∂(ν.map Prod.fst)
  rw [integral_map measurable_fst.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul (show Measurable w by dsimp [w]; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [w, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]

private theorem limit_tilt {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, ProbabilityMeasure (Ω n)) (D : ∀ n, Ω n → ℝ × ℝ)
    (hD : ∀ n, Measurable (D n)) (J : ProbabilityMeasure (ℝ × ℝ)) (L : ProbabilityMeasure ℝ)
    (hj : Tendsto (fun n => (P n).map (D n)) atTop (𝓝 J))
    {v : ℝ≥0} (hv : 0 < v) (hG : (J : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 v)
    {h : ℝ} (hh : h ≠ 0)
    (hLAN : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n : Measure (Ω n))
      {ω | ε ≤ |llr (Q n : Measure _) (P n) ω - (h * (D n ω).2 - h ^ 2 * v / 2)|})
      atTop (𝓝 0))
    (hreg : Tendsto (fun n => (Q n).map (fun ω => (D n ω).1 - h)) atTop (𝓝 L))
    (t : ℝ) :
    (∫ x, (Real.exp (h * x.2 - h ^ 2 * v / 2) : ℂ) *
      Complex.exp (t * (x.1 - h : ℝ) * Complex.I) ∂(J : Measure (ℝ × ℝ))) =
      charFun (L : Measure ℝ) t := by
  let a := fun x : ℝ × ℝ => h * x.2 - h ^ 2 * v / 2
  let b := fun x : ℝ × ℝ => x.1 - h
  let g := fun x => (b x, a x)
  have hg : Measurable g := by dsimp [g, a, b]; fun_prop
  obtain ⟨s, hs, hl⟩ := lan_joint P Q D hD J hj a b (by dsimp [a]; fun_prop)
    (by dsimp [b]; fun_prop) hLAN
  have hz : ∀ᵐ z ∂((J.map g : ProbabilityMeasure _) : Measure (ℝ × ℝ)), z.2 ≠ 0 := by
    apply (ae_map_iff hg.aemeasurable
      (isClosed_eq continuous_snd continuous_const).isOpen_compl.measurableSet).mpr
    have : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv.ne'
    have hne : ∀ᵐ x ∂(J : Measure (ℝ × ℝ)), x.2 ≠ h * v / 2 := by
      apply ae_of_ae_map (f := Prod.snd) (p := fun y : ℝ => y ≠ h * v / 2)
        measurable_snd.aemeasurable
      rw [hG]
      simp [ae_iff]
    filter_upwards [hne] with x hx
    change h * x.2 - h ^ 2 * v / 2 ≠ 0
    intro he
    apply hx
    apply mul_left_cancel₀ hh
    linarith only [he, show h ^ 2 * (v : ℝ) / 2 = h * (h * v / 2) by ring]
  have h₁ : ∫⁻ z, ENNReal.ofReal (Real.exp z.2)
      ∂((J.map g : ProbabilityMeasure _) : Measure (ℝ × ℝ)) = 1 := by
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map (by fun_prop) hg]
    change ∫⁻ x, (fun y : ℝ => ENNReal.ofReal (Real.exp (h * y - h ^ 2 * v / 2))) x.2
      ∂(J : Measure (ℝ × ℝ)) = 1
    rw [← lintegral_map (f := fun y : ℝ => ENNReal.ofReal (Real.exp (h * y - h ^ 2 * v / 2)))
      (by fun_prop) measurable_snd, hG]
    have H := congrArg (fun m : Measure ℝ => m univ)
      (Contiguity.gaussianReal_withDensity_exp h v)
    simpa [withDensity_apply] using H
  have he := tilt_charFun (fun n => P (s n)) (fun n => Q (s n))
    (fun n ω => b (D (s n) ω)) (fun n => (measurable_fst.comp (hD _)).sub_const h)
    (J.map g) L hl (hreg.comp hs.tendsto_atTop) hz h₁ t
  rw [ProbabilityMeasure.toMeasure_map, integral_map hg.aemeasurable (by fun_prop)] at he
  exact he

-- Gaussian exponential moments dominate the derivative on each complex ball of radius one.
open Complex in
private theorem analytic_transform (J : ProbabilityMeasure (ℝ × ℝ)) (t : ℝ)
    (hi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * x.2)) (J : Measure (ℝ × ℝ))) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ x, exp (t * x.1 * I + z * x.2) ∂(J : Measure (ℝ × ℝ)))
      univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  apply Differentiable.differentiableOn
  intro z
  let F := fun (w : ℂ) (x : ℝ × ℝ) => exp (t * x.1 * I + w * x.2)
  have hnorm (w : ℂ) (x : ℝ × ℝ) : ‖F w x‖ = Real.exp (w.re * x.2) := by
    simp [F, norm_exp, add_re, mul_re, mul_im]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun w x => F w x * x.2)
    (bound := fun x => |x.2| * Real.exp (z.re * x.2 + |x.2|))
    (Metric.ball_mem_nhds z one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt
  · exact .of_forall fun w => by dsimp [F]; fun_prop
  · apply (hi z.re).mono' (by dsimp [F]; fun_prop)
    exact .of_forall fun x => (hnorm z x).le
  · dsimp [F]
    fun_prop
  · apply ae_of_all
    intro x w hw
    rw [norm_mul, hnorm, norm_real, Real.norm_eq_abs, mul_comm]
    gcongr
    calc w.re * x.2 = z.re * x.2 + (w - z).re * x.2 := by rw [sub_re]; ring
      _ ≤ z.re * x.2 + |x.2| := by
        apply add_le_add_right
        calc (w - z).re * x.2 ≤ |(w - z).re * x.2| := le_abs_self _
          _ ≤ 1 * |x.2| := by
            rw [abs_mul]
            gcongr
            exact (abs_re_le_norm _).trans
              (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw))
          _ = _ := one_mul _
  · simpa using integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := fun x : ℝ × ℝ => x.2) (v := z.re) (t := 2) (x := 1)
      (hi _) (hi _) zero_le_one (by norm_num) 1
  · apply ae_of_all
    intro x w _
    dsimp [F]
    convert ((hasDerivAt_id w).mul_const (x.2 : ℂ)).const_add
      ((t : ℂ) * x.1 * I) |>.cexp using 1 <;> simp

open Complex in
private theorem convolution_of_transform (J : ProbabilityMeasure (ℝ × ℝ)) (L : ProbabilityMeasure ℝ)
    {v : ℝ≥0} (hv : 0 < v) (hG : (J : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 v)
    (htilt : ∀ h t : ℝ, (∫ x, (Real.exp (h * x.2 - h ^ 2 * v / 2) : ℂ) *
      exp (t * (x.1 - h : ℝ) * I) ∂(J : Measure (ℝ × ℝ))) = charFun (L : Measure ℝ) t) :
    ∃ M : ProbabilityMeasure ℝ, (L : Measure ℝ) = gaussianReal 0 v⁻¹ ∗ (M : Measure ℝ) := by
  let R := fun x : ℝ × ℝ => x.1 - x.2 / v
  have hR : Measurable R := by dsimp [R]; fun_prop
  refine ⟨J.map R, Measure.ext_of_charFun (funext fun t => ?_)⟩
  let F := fun z : ℂ => ∫ x, exp (t * x.1 * I + z * x.2) ∂(J : Measure (ℝ × ℝ))
  let G := fun z : ℂ => exp (z ^ 2 * v / 2 + t * z * I) * charFun (L : Measure ℝ) t
  have hF : AnalyticOnNhd ℂ F univ := by
    apply analytic_transform
    intro r
    apply Integrable.comp_measurable (g := fun y : ℝ => Real.exp (r * y)) _ measurable_snd
    rw [hG]
    exact integrable_exp_mul_gaussianReal _
  have hG' : AnalyticOnNhd ℂ G univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    apply Differentiable.differentiableOn
    dsimp [G]
    fun_prop
  have hreal (h : ℝ) : F h = G h := by
    dsimp [F, G]
    rw [← htilt h t, ← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [ofReal_exp, ← mul_assoc, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have heq : F = G := by
    apply hF.eq_of_frequently_eq hG' (z₀ := 0)
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨by simpa using (continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin (s := {0}ᶜ) (a := (0 : ℝ))] with x hx
          simpa using (show x ≠ 0 from hx)⟩
    exact ht.frequently (Frequently.of_forall hreal)
  -- At this imaginary argument the transform is the characteristic function of the residual.
  let z : ℂ := -(t : ℂ) * I / v
  have hchar : charFun ((J.map R : ProbabilityMeasure ℝ) : Measure ℝ) t = F z := by
    rw [charFun_apply_real, ProbabilityMeasure.toMeasure_map, integral_map hR.aemeasurable
      (by fun_prop)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp [R, z]
    congr 1
    push_cast
    ring
  rw [charFun_conv, hchar, heq, charFun_gaussianReal]
  dsimp [G, z]
  rw [← mul_assoc, ← exp_add]
  have hv' : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  convert (one_mul (charFun (L : Measure ℝ) t)).symm using 2
  rw [← exp_zero]
  congr 1
  push_cast
  field_simp
  ring_nf
  simp [I_sq]

/-- **Hájek's convolution theorem** (J. Hájek, *Z. Wahrscheinlichkeitstheorie verw. Geb.* 14
(1970) 323–330; here with a one-dimensional parameter). For each `n` let
`(P n h)_{h ∈ ℝ}` be a family of probability measures on `Ω n` (the local experiments
`P_{θ + h/√n}^n`), locally asymptotically normal at `0` with central sequence `Δ n` and
information `I > 0`: `Δ n ⇝ N(0, I)` under `P n 0`, and for every `h`,
`log dP_{n,h}/dP_{n,0} - (h Δ_n - h² I / 2) → 0` in `P n 0`-probability. Let `T n` be
*regular* estimators of the local parameter: for every `h`, the law of `T n - h` under `P n h`
converges weakly to one and the same law `L`. Then `L = N(0, I⁻¹) ∗ M` for some probability
measure `M`. -/
theorem hajek_convolution {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ℝ → ProbabilityMeasure (Ω n)) (Δ : ∀ n, Ω n → ℝ) (hΔ : ∀ n, Measurable (Δ n))
    {I : ℝ≥0} (hI : 0 < I)
    (hΔlim : Tendsto (fun n => (P n 0).map (Δ n)) atTop
      (𝓝 ⟨gaussianReal 0 I, inferInstance⟩))
    (hLAN : ∀ h ε : ℝ, 0 < ε → Tendsto (fun n => (P n 0 : Measure (Ω n))
      {ω | ε ≤ |llr (P n h : Measure (Ω n)) (P n 0 : Measure (Ω n)) ω -
        (h * Δ n ω - h ^ 2 * I / 2)|}) atTop (𝓝 0))
    (T : ∀ n, Ω n → ℝ) (hT : ∀ n, Measurable (T n)) (L : ProbabilityMeasure ℝ)
    (hreg : ∀ h : ℝ, Tendsto (fun n => (P n h).map (fun ω => T n ω - h)) atTop (𝓝 L)) :
    ∃ M : ProbabilityMeasure ℝ, (L : Measure ℝ) = gaussianReal 0 I⁻¹ ∗ (M : Measure ℝ) := by
  let D := fun n (ω : Ω n) => (T n ω, Δ n ω)
  have hD (n : ℕ) : Measurable (D n) := (hT n).prodMk (hΔ n)
  let μ := fun n => (P n 0).map (D n)
  obtain ⟨J, s, hs, hj, h₁, h₂⟩ := joint_limit μ
    (by simpa only [μ, D, law_pair_fst _ (hT _) (hΔ _), sub_zero] using hreg 0)
    (by simpa only [μ, D, law_pair_snd _ (hT _) (hΔ _)] using hΔlim)
  have hG : (J : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 I := congrArg Subtype.val h₂
  apply convolution_of_transform J L hI hG
  intro h t
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, sub_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [← h₁, charFun_apply_real, ProbabilityMeasure.toMeasure_map,
      integral_map measurable_fst.aemeasurable (by fun_prop)]
  · exact limit_tilt (fun n => P (s n) 0) (fun n => P (s n) h) (fun n => D (s n))
      (fun n => hD _) J L hj hI hG hh (fun ε hε => (hLAN h ε hε).comp hs.tendsto_atTop)
      ((hreg h).comp hs.tendsto_atTop) t

end MathlibExt.Probability.Statistics.EfficiencyWanted
