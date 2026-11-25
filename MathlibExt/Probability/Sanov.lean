/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LargeDeviationPrinciple
public import MathlibExt.Probability.SampleEmpiricalMeasure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Probability.Independence.Basic
import MathlibExt.InformationTheory.DonskerVaradhanFormula
import MathlibExt.Probability.CramerUpperBound
import MathlibExt.Probability.LDPProduct
import MathlibExt.Probability.Statistics.WaldInequalities
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Sanov's theorem

The empirical measures `Lₙ = (1/n) ∑_{i<n} δ_{Xᵢ}` of an i.i.d. sample with law `α` on a
Polish space satisfy the large deviation principle on the space of probability measures, with
the topology of weak convergence, and the rate function is the relative entropy
`β ↦ KL(β ‖ α)`. This is the result that identifies the Kullback–Leibler divergence of
information theory as a large deviation rate. The theorem also proves that relative entropy
has compact finite sublevel sets.

Varadhan's proof: the upper bound for small neighbourhoods follows from Chebyshev's inequality
and the Donsker–Varadhan variational formula for relative entropy
(`MathlibExt.InformationTheory.DonskerVaradhan.klDiv_eq_iSup`), the upper bound
for closed sets from exponential tightness of `Lₙ`, and the lower bound from tilting the
sample to i.i.d. `β` and the law of large numbers. Exponential tightness and the open-set lower
bound give compactness of the relative entropy sublevel sets.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 3, Theorem 1.1 in the notes' numbering
(https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf); originally I. N. Sanov, *Mat. Sb.*
42 (84) (1957), 11–44. See also S. R. S. Varadhan, "Large deviations", *Ann. Probab.* 36 (2008),
Section 1 (arXiv:0804.2330).
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction
open scoped BigOperators
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.SampleEmpiricalMeasure
open MathlibExt.InformationTheory.DonskerVaradhan

namespace MathlibExt.Probability.SanovWanted

section

variable {X : Type*} [MeasurableSpace X]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Xs : ℕ → Ω → X}

private theorem measurable_empirical (hmeas : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [smul_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_eq_mul]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (hmeas i)))

private theorem integral_empirical [MeasurableSingletonClass X] (x : ℕ → X)
    {n : ℕ} (hn : 0 < n) (f : X → ℝ) :
    ∫ y, f y ∂(sampleEmpiricalMeasure x n : Measure X) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (x i) := by
  rw [toMeasure_sampleEmpiricalMeasure x hn.ne', integral_smul_measure,
    integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · exact fun i _ => integrable_dirac (by simp)

private theorem integral_exp_pos (α : ProbabilityMeasure X) {f : X → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    0 < ∫ x, Real.exp (f x) ∂(α : Measure X) := by
  have hi := (integrable_of_bounded (μ := (α : Measure X)) hf hC).2
  simpa [mgf] using (mgf_pos (X := f) (t := 1) (by simpa using hi))

private theorem empirical_chernoff [MeasurableSingletonClass X]
    (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X))
    {n : ℕ} (hn : 0 < n) {A : Set (ProbabilityMeasure X)} (hA : MeasurableSet A)
    {f : X → ℝ} (hf : Measurable f) {C q : ℝ} (hC : ∀ x, |f x| ≤ C)
    (h : ∀ β ∈ A, q ≤ (∫ x, f x ∂(β : Measure X)) -
      Real.log (∫ x, Real.exp (f x) ∂(α : Measure X))) :
    P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) A ≤
      ENNReal.ofReal (Real.exp (-(n * q))) := by
  rw [Measure.map_apply (measurable_empirical hmeas n) hA]
  rw [← neg_mul]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  apply ENNReal.ofReal_le_ofReal
  have hident : ∀ i, IdentDistrib (Xs i) (Xs 0) P P := fun i =>
    ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩
  have hi : Integrable (fun ω => Real.exp (1 * f (Xs 0 ω))) P := by
    simpa only [one_mul, Function.comp_apply] using
      (integrable_of_bounded (μ := P) (hf.comp (hmeas 0)) (fun ω => hC (Xs 0 ω))).2
  apply CramerUpperBound.measure_empiricalMean_le_of_threshold
    (X := fun i => f ∘ Xs i) (fun i => hf.comp (hmeas i))
    (hindep.comp (fun _ => f) (fun _ => hf)) (fun i => (hident i).comp hf) hi hn
  intro ω hω
  have hh := h _ hω
  rw [integral_empirical _ hn] at hh
  have heq : mgf (f ∘ Xs 0) P 1 = ∫ x, Real.exp (f x) ∂(α : Measure X) := by
    rw [mgf, ← hlaw 0, integral_map (hmeas 0).aemeasurable hf.exp.aestronglyMeasurable]
    simp
  simpa only [Function.comp_apply, one_mul, heq] using hh

/-! ## The local bounds and exponential tightness -/

section Polish

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

private theorem abs_exp_sub_le {C x y : ℝ} (hx : x ≤ C) (hy : y ≤ C) :
    |Real.exp x - Real.exp y| ≤ Real.exp C * |x - y| := by
  simp only [← Real.norm_eq_abs]
  apply (convex_Iic C).norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (fun x _ => Real.differentiableAt_exp) _ hy hx
  intro z hz
  rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hz

private theorem klDiv_eq_iSup_continuous (α β : ProbabilityMeasure X) :
    klDiv (β : Measure X) (α : Measure X) =
      ⨆ f : X →ᵇ ℝ, ENNReal.ofReal ((∫ x, f x ∂(β : Measure X)) -
        Real.log (∫ x, Real.exp (f x) ∂(α : Measure X))) := by
  let D : ℝ≥0∞ := ⨆ f : X →ᵇ ℝ, ENNReal.ofReal ((∫ x, f x ∂(β : Measure X)) -
    Real.log (∫ x, Real.exp (f x) ∂(α : Measure X)))
  change _ = D
  refine le_antisymm ?_ (iSup_le fun f => ?_)
  swap
  · exact ofReal_integral_sub_log_integral_exp_le_klDiv f.continuous.measurable
      (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
  rw [klDiv_eq_iSup]
  refine iSup₂_le fun f ⟨hf, C, hC⟩ => ?_
  -- Clip the continuous approximants so that exponentiation preserves L¹ convergence.
  let M := |C|
  have hM : ∀ x, |f x| ≤ M := fun x => (hC x).trans (le_abs_self C)
  let μ := (α : Measure X) + (β : Measure X)
  have hi : Integrable f μ := (integrable_of_bounded hf hM).1
  have hApprox (n : ℕ) : ∃ g : X →ᵇ ℝ, (∫ x, ‖f x - g x‖ ∂μ) ≤ ((n : ℝ) + 1)⁻¹ ∧
      Integrable g μ :=
    hi.exists_boundedContinuous_integral_sub_le
      (show 0 < ((n : ℝ) + 1)⁻¹ by positivity)
  choose g hgn hgi using hApprox
  let clip (t : ℝ) := min (max (-M) t) M
  have hclip : LipschitzWith 1 clip := (LipschitzWith.id.const_max (-M)).min_const M
  let v (n : ℕ) := BoundedContinuousFunction.comp clip hclip (g n)
  have hclip_id (x : X) : clip (f x) = f x := by
    have hx := abs_le.mp (hM x)
    simp [clip, max_eq_right hx.1, min_eq_left hx.2]
  have hv (n : ℕ) (x : X) : |v n x| ≤ M := by
    apply abs_le.mpr
    have hM0 : 0 ≤ M := abs_nonneg C
    change -M ≤ clip (g n x) ∧ clip (g n x) ≤ M
    exact ⟨le_min (le_max_left _ _) (neg_nonpos.mpr hM0 |>.trans hM0), min_le_right _ _⟩
  have herr (n : ℕ) (x : X) : ‖f x - v n x‖ ≤ ‖f x - g n x‖ := by
    change ‖f x - clip (g n x)‖ ≤ _
    simpa only [dist_eq_norm, hclip_id, NNReal.coe_one, one_mul] using
      hclip.dist_le_mul (f x) (g n x)
  have hErr (ν : Measure X) (hle : ν ≤ μ) (n : ℕ) :
      (∫ x, ‖f x - v n x‖ ∂ν) ≤ ((n : ℝ) + 1)⁻¹ := by
    have hi' : Integrable (fun x => ‖f x - g n x‖) μ := (hi.sub (hgi n)).norm
    exact (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hi'.mono_measure hle) (Eventually.of_forall (herr n))).trans
      ((integral_mono_measure hle (Eventually.of_forall fun _ => norm_nonneg _) hi').trans (hgn n))
  have hα : (α : Measure X) ≤ μ := by intro s; simp [μ]
  have hβ : (β : Measure X) ≤ μ := by intro s; simp [μ]
  have hz : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have htβ : Tendsto (fun n => ∫ x, v n x ∂(β : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(β : Measure X))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hz
    rw [norm_sub_rev, ← integral_sub (hi.mono_measure hβ)
      (integrable_of_bounded (v n).continuous.measurable (hv n)).1]
    exact (norm_integral_le_integral_norm _).trans (hErr _ hβ n)
  have htα : Tendsto (fun n => ∫ x, Real.exp (v n x) ∂(α : Measure X)) atTop
      (𝓝 (∫ x, Real.exp (f x) ∂(α : Measure X))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa using hz.const_mul (Real.exp M))
    rw [norm_sub_rev, ← integral_sub (integrable_of_bounded hf hM).2
      (integrable_of_bounded (v n).continuous.measurable (hv n)).2]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc
      _ ≤ ∫ x, Real.exp M * ‖f x - v n x‖ ∂(α : Measure X) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        · exact (((hi.mono_measure hα).sub
            (integrable_of_bounded (v n).continuous.measurable (hv n)).1).norm).const_mul _
        · exact Eventually.of_forall fun x => by
            simpa only [Real.norm_eq_abs] using abs_exp_sub_le
              ((abs_le.mp (hM x)).2) ((abs_le.mp (hv n x)).2)
      _ ≤ _ := by rw [integral_const_mul]; gcongr; exact hErr _ hα n
  apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp
    (htβ.sub (htα.log (integral_exp_pos α hf hM).ne')))
  exact Eventually.of_forall fun n => le_iSup (f := fun u : X →ᵇ ℝ =>
    ENNReal.ofReal ((∫ x, u x ∂(β : Measure X)) -
      Real.log (∫ x, Real.exp (u x) ∂(α : Measure X)))) (v n)

private theorem entropy_lowerSemicontinuous (α : ProbabilityMeasure X) :
    LowerSemicontinuous (fun β : ProbabilityMeasure X =>
      klDiv (β : Measure X) (α : Measure X)) := by
  simp_rw [klDiv_eq_iSup_continuous α]
  exact lowerSemicontinuous_iSup fun f => (ENNReal.continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const)).lowerSemicontinuous

variable [OpensMeasurableSpace (ProbabilityMeasure X)]

private theorem local_upper
    (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X))
    (β : ProbabilityMeasure X) {q : ℝ} (hq : 0 ≤ q)
    (hqβ : (q : EReal) < (klDiv (β : Measure X) (α : Measure X) : EReal)) :
    ∃ A : Set (ProbabilityMeasure X), IsOpen A ∧ β ∈ A ∧ ∀ n : ℕ, 0 < n →
      P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) A ≤
        ENNReal.ofReal (Real.exp (-(n * q))) := by
  have hqcoe : (ENNReal.ofReal q : EReal) = q := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast hq)]
  rw [← hqcoe, EReal.coe_ennreal_lt_coe_ennreal_iff,
    klDiv_eq_iSup_continuous, lt_iSup_iff] at hqβ
  obtain ⟨f, hf⟩ := hqβ
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq] at hf
  let A : Set (ProbabilityMeasure X) := {γ | q < (∫ x, f x ∂(γ : Measure X)) -
    Real.log (∫ x, Real.exp (f x) ∂(α : Measure X))}
  have hA : IsOpen A := isOpen_lt continuous_const
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub continuous_const)
  exact ⟨A, hA, hf, fun n hn => empirical_chernoff hmeas hindep α hlaw hn hA.measurableSet
    f.continuous.measurable (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    (fun _ hγ => hγ.le)⟩

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [OpensMeasurableSpace (ProbabilityMeasure X)] in
private theorem exp_indicator_integral_le (α : ProbabilityMeasure X) {B : Set X}
    (hB : MeasurableSet B) {t : ℝ} (hsmall : (α : Measure X) B ≤ ENNReal.ofReal (Real.exp (-t))) :
    (∫ x, Real.exp (B.indicator (fun _ => t) x) ∂(α : Measure X)) ≤ 2 := by
  have heq : (fun x => Real.exp (B.indicator (fun _ => t) x)) =
      fun x => B.indicator (fun _ => Real.exp t) x + Bᶜ.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [heq, integral_add ((integrable_const _).indicator hB)
    ((integrable_const _).indicator hB.compl), integral_indicator_const _ hB,
    integral_indicator_const _ hB.compl, smul_eq_mul, smul_eq_mul, mul_one]
  have h1 : (α : Measure X).real B * Real.exp t ≤ 1 := by
    calc
      _ ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal (by positivity) hsmall)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linarith [measureReal_le_one (μ := (α : Measure X)) (s := Bᶜ)]

omit [OpensMeasurableSpace (ProbabilityMeasure X)] in
private theorem exists_compact_empirical_tail
    (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X))
    (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ∃ K : Set (ProbabilityMeasure X), IsCompact K ∧ ∀ n : ℕ, 0 < n →
      P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) Kᶜ ≤
        ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  -- Require progressively less mass outside compacts with progressively smaller α-tails.
  let ε (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  let t (k : ℕ) : ℝ := (ℓ + (k + 1) + 1) / ε k
  have ht (k : ℕ) : 0 ≤ t k := by dsimp [t]; positivity
  have htight := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (α : Measure X)))
  have hex (k : ℕ) := htight (ENNReal.ofReal (Real.exp (-t k))) (by positivity)
  choose K hK hsmall using hex
  let S : Set (ProbabilityMeasure X) := {β | ∀ k : ℕ,
    (β : Measure X) (K k)ᶜ ≤ ENNReal.ofReal (ε k)}
  have hS : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun δ hδ => ?_
    have he : Tendsto (fun k => ENNReal.ofReal (ε k)) atTop (𝓝 0) := by
      have he' : Tendsto ε atTop (𝓝 0) :=
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto 0).comp he'
    obtain ⟨k, hk⟩ := (he.eventually_lt_const hδ).exists
    exact ⟨K k, hK k, fun ν ⟨β, hβ, heq⟩ => heq ▸ (hβ k).trans hk.le⟩
  refine ⟨closure S, hS, fun n hn => ?_⟩
  let A (k : ℕ) : Set (ProbabilityMeasure X) :=
    {β | ENNReal.ofReal (ε k) < (β : Measure X) (K k)ᶜ}
  have hs : (closure S)ᶜ ⊆ ⋃ k, A k := by
    intro β hβ
    have hmem : β ∉ S := fun h => hβ (subset_closure h)
    simpa only [S, A, mem_ofPred_eq, not_forall, not_le, mem_iUnion] using hmem
  refine (measure_mono hs).trans ((measure_iUnion_le A).trans ?_)
  calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(n * (ℓ + (k + 1))))) := by
      apply tsum_le_tsum
      intro k
      have hB := (hK k).isClosed.measurableSet.compl
      have hAm : MeasurableSet (A k) := measurableSet_lt measurable_const
        ((Measure.measurable_coe hB).comp measurable_subtype_coe)
      let f : X → ℝ := ((K k)ᶜ).indicator (fun _ => t k)
      have hf : Measurable f := measurable_const.indicator hB
      have hfB (x : X) : |f x| ≤ t k := by
        by_cases hx : x ∈ (K k)ᶜ <;> simp [f, hx, ht k, abs_of_nonneg (ht k)]
      refine empirical_chernoff hmeas hindep α hlaw hn hAm hf hfB fun β hβ => ?_
      have hβ' : ε k ≤ (β : Measure X).real (K k)ᶜ := by
        exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hβ.le
      have hE : Real.log (∫ x, Real.exp (f x) ∂(α : Measure X)) ≤ 1 :=
        (Real.log_le_sub_one_of_pos (integral_exp_pos α hf hfB)).trans
          (by linarith [exp_indicator_integral_le α hB (hsmall k _ (mem_singleton _))])
      have hmul := mul_le_mul_of_nonneg_right hβ' (ht k)
      have htε : ε k * t k = ℓ + (k + 1) + 1 := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (hε k).ne'
      rw [htε] at hmul
      rw [show (∫ x, f x ∂(β : Measure X)) = _ from integral_indicator_const _ hB,
        smul_eq_mul]
      linarith
    _ ≤ ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) :=
      tsum_le_tsum (fun k => by simpa only [mul_neg] using
        LDPProduct.ofReal_exp_le_inv_two_pow_mul hn k ℓ)
    _ = _ := by rw [ENNReal.tsum_mul_right, LDPProduct.tsum_inv_two_pow_succ, one_mul]

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [OpensMeasurableSpace (ProbabilityMeasure X)] in
private theorem ae_tendsto_average
    (β : ProbabilityMeasure X) {f : X → ℝ} (hf : Measurable f)
    (hi : Integrable f (β : Measure X)) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => (β : Measure X)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (x i)) / n) atTop
        (𝓝 (∫ y, f y ∂(β : Measure X))) := by
  let μ := fun _ : ℕ => (β : Measure X)
  have hp (i : ℕ) := measurePreserving_eval_infinitePi μ i
  have hind : iIndepFun (fun (i : ℕ) (x : ℕ → X) => f (x i)) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (fun _ => hf)
  have hident (i : ℕ) : IdentDistrib (fun x : ℕ → X => f (x i))
      (fun x : ℕ → X => f (x 0)) (Measure.infinitePi μ) (Measure.infinitePi μ) :=
    (show IdentDistrib (fun x : ℕ → X => x i) (fun x : ℕ → X => x 0)
      (Measure.infinitePi μ) (Measure.infinitePi μ) from
      ⟨(hp i).measurable.aemeasurable, (hp 0).measurable.aemeasurable,
        (hp i).map_eq.trans (hp 0).map_eq.symm⟩).comp hf
  have h := strong_law_ae_real (fun (i : ℕ) (x : ℕ → X) => f (x i))
    ((hp 0).integrable_comp_of_integrable hi) (fun _ _ hij => hind.indepFun hij) hident
  have heq : (∫ x : ℕ → X, f (x 0) ∂Measure.infinitePi μ) =
      ∫ y, f y ∂(β : Measure X) := by
    change _ = ∫ y, f y ∂μ 0
    rw [← (hp 0).map_eq, integral_map (hp 0).measurable.aemeasurable hf.aestronglyMeasurable]
  rwa [heq] at h

omit [OpensMeasurableSpace (ProbabilityMeasure X)] in
private theorem ae_eventually_empirical_mem
    {β : ProbabilityMeasure X} {U : Set (ProbabilityMeasure X)} (hU : IsOpen U) (hβ : β ∈ U) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => (β : Measure X)),
      ∀ᶠ n in atTop, sampleEmpiricalMeasure x n ∈ U := by
  let e (f : X →ᵇ ℝ) (γ : ProbabilityMeasure X) := ∫ x, f x ∂(γ : Measure X)
  have hfilter : (⨅ f : X →ᵇ ℝ, comap (e f) (𝓝 (e f β))) ≤ 𝓝 β := by
    have h : Tendsto id (⨅ f : X →ᵇ ℝ, comap (e f) (𝓝 (e f β))) (𝓝 β) := by
      refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f => ?_
      exact tendsto_iff_comap.mpr (iInf_le _ f)
    simpa only [Tendsto, map_id] using h
  -- A given weak neighborhood only requires convergence for finitely many tests.
  obtain ⟨s, hs⟩ := (mem_iInf_finite U).mp (hfilter (hU.mem_nhds hβ))
  have hf (f : X →ᵇ ℝ) : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => (β : Measure X)),
      Tendsto (fun n => e f (sampleEmpiricalMeasure x n)) atTop (𝓝 (e f β)) := by
    have hfm := f.continuous.measurable
    filter_upwards [ae_tendsto_average β hfm ((integrable_of_bounded hfm
      (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)).1)] with x hx
    refine hx.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    change _ = ∫ y, f y ∂(sampleEmpiricalMeasure x n : Measure X)
    rw [integral_empirical _ hn, div_eq_mul_inv, mul_comm]
  filter_upwards [s.eventually_all.mpr (fun f _ => hf f)] with x hx
  have ht : Tendsto (fun n => sampleEmpiricalMeasure x n) atTop
      (⨅ f ∈ s, comap (e f) (𝓝 (e f β))) :=
    tendsto_iInf.mpr fun f => tendsto_iInf.mpr fun hf => tendsto_comap_iff.mpr (hx f hf)
  exact ht hs

private theorem empirical_lower_product
    (α β : ProbabilityMeasure X) {U : Set (ProbabilityMeasure X)} (hU : IsOpen U) (hβ : β ∈ U)
    (hKL : klDiv (β : Measure X) (α : Measure X) ≠ ⊤) {r : ℝ}
    (hr : (klDiv (β : Measure X) (α : Measure X)).toReal < r) :
    ∀ᶠ n : ℕ in atTop,
      (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n * r))) ≤
        (Measure.infinitePi (fun _ : ℕ => (α : Measure X)))
          ((fun x => sampleEmpiricalMeasure x n) ⁻¹' U) := by
  obtain ⟨hAC, hInt⟩ := klDiv_ne_top_iff.mp hKL
  let μ := Measure.infinitePi (fun _ : ℕ => (α : Measure X))
  let ν := Measure.infinitePi (fun _ : ℕ => (β : Measure X))
  let ρ := (β : Measure X).rnDeriv (α : Measure X)
  -- Restrict the target neighborhood to samples with bounded likelihood ratio.
  let A (n : ℕ) : Set (ℕ → X) := {x | sampleEmpiricalMeasure x n ∈ U ∧
    ∏ i ∈ Finset.range n, ρ (x i) ≤ ENNReal.ofReal (Real.exp (n * r))}
  have hcoord {n i : ℕ} (hi : i < n) :
      Measurable[observationFiltration X n] (fun x : ℕ → X => x i) := by
    change Measurable[MeasurableSpace.pi.comap (Finset.range n).restrict] (fun x : ℕ → X => x i)
    exact (@measurable_pi_apply (Finset.range n) (fun _ => X) (fun _ => inferInstance)
      ⟨i, Finset.mem_range.mpr hi⟩).comp (comap_measurable _)
  have hA {n : ℕ} (hn : 0 < n) : MeasurableSet[observationFiltration X n] (A n) := by
    let Y (i : ℕ) (x : ℕ → X) := if i < n then x i else x 0
    have hY (i : ℕ) : Measurable[observationFiltration X n] (Y i) := by
      by_cases hi : i < n
      · simpa [Y, hi] using hcoord hi
      · simpa [Y, hi] using hcoord hn
    have hEq (x : ℕ → X) : sampleEmpiricalMeasure (fun i => Y i x) n =
        sampleEmpiricalMeasure x n := by
      apply Subtype.ext
      change (sampleEmpiricalMeasure (fun i => Y i x) n : Measure X) =
        (sampleEmpiricalMeasure x n : Measure X)
      rw [toMeasure_sampleEmpiricalMeasure _ hn.ne', toMeasure_sampleEmpiricalMeasure _ hn.ne']
      congr 1
      exact Finset.sum_congr rfl fun i hi => by simp [Y, Finset.mem_range.mp hi]
    have hset : {x | sampleEmpiricalMeasure x n ∈ U} =
        (fun x => sampleEmpiricalMeasure (fun i => Y i x) n) ⁻¹' U := by
      ext x
      change sampleEmpiricalMeasure x n ∈ U ↔ sampleEmpiricalMeasure (fun i => Y i x) n ∈ U
      rw [hEq]
    change MeasurableSet[observationFiltration X n] ({x | sampleEmpiricalMeasure x n ∈ U} ∩
      {x | ∏ i ∈ Finset.range n, ρ (x i) ≤ ENNReal.ofReal (Real.exp (n * r))})
    rw [hset]
    exact ((measurable_empirical hY n) hU.measurableSet).inter
      (measurableSet_le (Finset.measurable_prod _ fun i hi =>
        (Measure.measurable_rnDeriv _ _).comp (hcoord (Finset.mem_range.mp hi))) measurable_const)
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_empirical (fun i => measurable_pi_apply i) n hU.measurableSet).inter
      (measurableSet_le (Finset.measurable_prod _ fun i _ =>
        (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply i)) measurable_const)
  have hρ : ∀ᵐ x ∂ν, ∀ i, 0 < ρ (x i) ∧ ρ (x i) ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    apply ae_of_ae_map (p := fun y => 0 < ρ y ∧ ρ y ≠ ⊤)
      (measurable_pi_apply (X := fun _ => X) i).aemeasurable
    rw [show ν = Measure.infinitePi (fun _ : ℕ => (β : Measure X)) from rfl,
      Measure.infinitePi_map_eval]
    exact (Measure.rnDeriv_pos hAC).and
      (hAC.ae_le ((Measure.rnDeriv_lt_top _ _).mono fun _ hx => hx.ne))
  have hllr := ae_tendsto_average β (measurable_llr _ _) hInt
  rw [← toReal_klDiv_of_measure_eq hAC (by simp)] at hllr
  have hev : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ A n ↔ x ∈ (univ : Set (ℕ → X)) := by
    filter_upwards [ae_eventually_empirical_mem hU hβ, hρ, hllr] with x hx hρx hllrx
    filter_upwards [hx, hllrx.eventually_lt_const hr, eventually_gt_atTop 0] with n hxn hlt hn
    simp only [A, mem_ofPred_eq, mem_univ, iff_true]
    refine ⟨hxn, ?_⟩
    have hexp : ∏ i ∈ Finset.range n, ρ (x i) =
        ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n,
          llr (β : Measure X) (α : Measure X) (x i))) := by
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [llr, Real.exp_log (ENNReal.toReal_pos (hρx i).1.ne' (hρx i).2),
        ENNReal.ofReal_toReal (hρx i).2]
    rw [hexp]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
      have hlt' := (div_lt_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp hlt
      exact (mul_comm r (n : ℝ) ▸ hlt').le))
  have hlim : Tendsto (fun n => ν (A n)) atTop (𝓝 1) := by
    rw [← measure_univ (μ := ν)]
    exact tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop .univ hAm hev
  filter_upwards [hlim.eventually_const_lt (show (2⁻¹ : ℝ≥0∞) < 1 by norm_num),
    eventually_gt_atTop 0] with n hnβ hn
  have hChange : ν (A n) ≤ ENNReal.ofReal (Real.exp (n * r)) * μ (A n) := by
    rw [show ν (A n) = _ from infinitePi_apply_eq_setLIntegral_prod_rnDeriv
      (α : Measure X) (β : Measure X) hAC n (hA hn), ← setLIntegral_const]
    exact lintegral_mono_ae (ae_restrict_of_forall_mem (hAm n) fun x hx => hx.2)
  have hcancel : ENNReal.ofReal (Real.exp (n * r)) * ENNReal.ofReal (Real.exp (-(n * r))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc
    _ ≤ ν (A n) * ENNReal.ofReal (Real.exp (-(n * r))) := mul_le_mul' hnβ.le le_rfl
    _ ≤ (ENNReal.ofReal (Real.exp (n * r)) * μ (A n)) *
        ENNReal.ofReal (Real.exp (-(n * r))) := mul_le_mul' hChange le_rfl
    _ = μ (A n) := by rw [mul_right_comm, hcancel, one_mul]
    _ ≤ _ := measure_mono fun x hx => hx.1

open VaradhanIntegralLemma (coe_le_inv_mul_log_iff inv_mul_log_le_coe_iff)

omit [IsProbabilityMeasure P] in
private theorem empirical_point_lower
    (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X))
    {β : ProbabilityMeasure X} {U : Set (ProbabilityMeasure X)} (hU : IsOpen U) (hβ : β ∈ U) :
    -(klDiv (β : Measure X) (α : Measure X) : EReal) ≤
      liminf (fun n : ℕ => (n : EReal)⁻¹ * ENNReal.log
        (P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) U)) atTop := by
  by_cases ht : klDiv (β : Measure X) (α : Measure X) = ⊤
  · simp [ht]
  rw [← EReal.coe_ennreal_toReal ht, ← EReal.coe_neg]
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  obtain ⟨a, hba, ha⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  rw [EReal.coe_lt_coe_iff] at ha
  obtain ⟨r, hr, hra⟩ : ∃ r : ℝ, (klDiv (β : Measure X) (α : Measure X)).toReal < r ∧ r < -a :=
    exists_between (by linarith)
  refine hba.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  have hfull : Measurable (fun (ω : Ω) (i : ℕ) => Xs i ω) := measurable_pi_iff.mpr hmeas
  have hp : P.map (fun (ω : Ω) (i : ℕ) => Xs i ω) =
      Measure.infinitePi (fun _ : ℕ => (α : Measure X)) := by
    rw [hindep.map_fun_eq_infinitePi_map hmeas]
    simp_rw [hlaw]
  filter_upwards [empirical_lower_product α β hU hβ ht hr,
    LDPProduct.eventually_mul_ofReal_exp_le (M := 2) (by simp) hra,
    eventually_gt_atTop 0] with n hn hfactor hn0
  rw [coe_le_inv_mul_log_iff hn0]
  have heq : P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) U =
      Measure.infinitePi (fun _ : ℕ => (α : Measure X))
        ((fun x => sampleEmpiricalMeasure x n) ⁻¹' U) := by
    have hm := measurable_empirical (fun i : ℕ => measurable_pi_apply (X := fun _ => X) i) n
    rw [← hp, ← Measure.map_apply hm hU.measurableSet, Measure.map_map hm hfull]
    rfl
  rw [heq]
  apply le_trans _ hn
  calc
    _ = (2⁻¹ : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-(n * -a)))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp),
        one_mul, mul_neg, neg_neg]
    _ ≤ _ := mul_le_mul' le_rfl hfactor

private theorem empirical_upper
    (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X))
    {F : Set (ProbabilityMeasure X)} (hF : IsClosed F) :
    limsup (fun n : ℕ => (n : EReal)⁻¹ * ENNReal.log
      (P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) F)) atTop ≤
      -(⨅ β ∈ F, (klDiv (β : Measure X) (α : Measure X) : EReal)) := by
  let μ (n : ℕ) := P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n)
  change limsup (fun n : ℕ => (n : EReal)⁻¹ * ENNReal.log (μ n F)) atTop ≤ _
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  by_cases hc0 : 0 ≤ c
  · refine le_trans ?_ hc0
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← EReal.coe_zero, inv_mul_log_le_coe_iff hn]
    have : IsProbabilityMeasure (μ n) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_empirical hmeas n).aemeasurable).2
        inferInstance
    simpa using (prob_le_one : μ n F ≤ 1)
  rw [EReal.neg_lt_comm] at hc
  obtain ⟨q, hcq, hqF⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  obtain ⟨q', hcq', hq'q⟩ := EReal.lt_iff_exists_real_btwn.mp hcq
  have hq0 : 0 ≤ q := by
    have hc' : (0 : EReal) ≤ -c := EReal.neg_nonneg.mpr (lt_of_not_ge hc0).le
    exact_mod_cast hc'.trans hcq.le
  have hq'c : ((-q' : ℝ) : EReal) ≤ c := by
    rw [EReal.coe_neg, EReal.neg_le]
    exact hcq'.le
  refine le_trans ?_ hq'c
  obtain ⟨K, hK, htail⟩ := exists_compact_empirical_tail hmeas hindep α hlaw q hq0
  have hcover : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n : ℕ, 0 < n →
      μ n (F ∩ K) ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) := by
    refine (hK.inter_left hF).induction_on
      (p := fun S => ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n : ℕ, 0 < n →
        μ n S ≤ M * ENNReal.ofReal (Real.exp (-(n * q)))) ?_ ?_ ?_ ?_
    · exact ⟨0, by simp, fun n hn => by simp⟩
    · rintro S T hST ⟨M, hM, hT⟩
      exact ⟨M, hM, fun n hn => (measure_mono hST).trans (hT n hn)⟩
    · rintro S T ⟨M, hM, hS⟩ ⟨N, hN, hT⟩
      refine ⟨M + N, ENNReal.add_ne_top.mpr ⟨hM, hN⟩, fun n hn => ?_⟩
      rw [add_mul]
      exact (measure_union_le _ _).trans (add_le_add (hS n hn) (hT n hn))
    · intro β hβ
      have hr : (q : EReal) < (klDiv (β : Measure X) (α : Measure X) : EReal) :=
        hqF.trans_le (iInf₂_le (f := fun γ (_ : γ ∈ F) =>
          (klDiv (γ : Measure X) (α : Measure X) : EReal)) β hβ.1)
      obtain ⟨A, hA, hβA, hbound⟩ := local_upper hmeas hindep α hlaw β hq0 hr
      exact ⟨A, mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hβA), 1, by simp,
        fun n hn => by simpa using hbound n hn⟩
  obtain ⟨M, hM, hMbound⟩ := hcover
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_gt_atTop 0, LDPProduct.eventually_mul_ofReal_exp_le
    (M := M + 1) (ENNReal.add_ne_top.mpr ⟨hM, by simp⟩) (EReal.coe_lt_coe_iff.mp hq'q)] with n hn hb
  rw [inv_mul_log_le_coe_iff hn, mul_neg]
  calc
    μ n F ≤ μ n (F ∩ K) + μ n Kᶜ := by
      refine (measure_mono (show F ⊆ (F ∩ K) ∪ Kᶜ from ?_)).trans (measure_union_le _ _)
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    _ ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) +
        ENNReal.ofReal (Real.exp (-(n * q))) := add_le_add (hMbound n hn) (htail n hn)
    _ = (M + 1) * ENNReal.ofReal (Real.exp (-(n * q))) := by rw [add_mul, one_mul]
    _ ≤ _ := hb

end Polish

end

public section

open VaradhanIntegralLemma (inv_mul_log_le_coe_iff)

/-- **Sanov's theorem.** Let `X` be a Polish space with its Borel σ-algebra and let
`X₀, X₁, …` be measurable, independent random variables in `X`, each with law `α`. Then the
laws of the empirical measures `Lₙ = (1/n) ∑_{i<n} δ_{Xᵢ}`, viewed as random elements of the
space of probability measures on `X` with the topology of weak convergence, satisfy the large
deviation principle with the good rate function `β ↦ KL(β ‖ α)`.
The statement assumes that the open sets of the weak topology on probability measures are
measurable for Mathlib's (Giry) σ-algebra. This holds on Polish spaces, where the weak topology
is second countable and generated by Giry-measurable maps, but Mathlib does not yet provide this
instance, so the entry cannot be applied until it is proved.
Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 3, Theorem 1.1. -/
theorem satisfiesLDP_sampleEmpiricalMeasure {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace (ProbabilityMeasure X)]
    {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Xs : ℕ → Ω → X} (hmeas : ∀ i, Measurable (Xs i)) (hindep : iIndepFun Xs P)
    (α : ProbabilityMeasure X) (hlaw : ∀ i, P.map (Xs i) = (α : Measure X)) :
    SatisfiesLDP (fun n => P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n))
        (fun β : ProbabilityMeasure X => klDiv (β : Measure X) (α : Measure X)) ∧
      IsGoodRateFunction (fun β : ProbabilityMeasure X => klDiv (β : Measure X) (α : Measure X))
    := by
  have hRate : IsRateFunction (fun β : ProbabilityMeasure X =>
      klDiv (β : Measure X) (α : Measure X)) := ⟨entropy_lowerSemicontinuous α⟩
  refine ⟨⟨hRate, ?_, fun _ hF => empirical_upper hmeas hindep α hlaw hF⟩, ⟨hRate, ?_⟩⟩
  · intro U hU
    rw [EReal.neg_le]
    refine le_iInf₂ fun β hβ => ?_
    rw [← EReal.neg_le]
    exact empirical_point_lower hmeas hindep α hlaw hU hβ
  · intro a
    -- A point outside this compact would force its entropy to be at least ℓ.
    let ℓ : ℝ := max a 0 + 1
    have hℓ : 0 ≤ ℓ := (le_max_right a 0).trans (le_add_of_nonneg_right zero_le_one)
    obtain ⟨K, hK, htail⟩ := exists_compact_empirical_tail hmeas hindep α hlaw ℓ hℓ
    refine hK.of_isClosed_subset ?_ ?_
    · exact hRate.lowerSemicontinuous.isClosed_preimage _
    · intro β hβ
      by_contra hβK
      have hlo := empirical_point_lower hmeas hindep α hlaw hK.isClosed.isOpen_compl hβK
      have hup : limsup (fun n : ℕ => (n : EReal)⁻¹ * ENNReal.log
          (P.map (fun ω => sampleEmpiricalMeasure (fun i => Xs i ω) n) Kᶜ)) atTop ≤
          ((-ℓ : ℝ) : EReal) := by
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [inv_mul_log_le_coe_iff hn, mul_neg]
        exact htail n hn
      have hle := hlo.trans ((liminf_le_limsup).trans hup)
      rw [EReal.coe_neg, EReal.neg_le_neg_iff] at hle
      have hβ' : (klDiv (β : Measure X) (α : Measure X) : EReal) ≤ (max a 0 : ℝ) := by
        change klDiv (β : Measure X) (α : Measure X) ≤ ENNReal.ofReal a at hβ
        refine (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hβ).trans_eq ?_
        rw [EReal.coe_ennreal_ofReal]
      have hlt : ((max a 0 : ℝ) : EReal) < (ℓ : EReal) := by
        rw [EReal.coe_lt_coe_iff]
        exact lt_add_one _
      exact (not_lt_of_ge (hle.trans hβ')) hlt

end

end MathlibExt.Probability.SanovWanted
