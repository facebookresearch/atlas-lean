/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GenericChainingGaussian
import MathlibExt.Analysis.SpecialFunctions.LogSumExp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Sudakov minoration

The expected maximum of a finite centred Gaussian process is bounded below in terms of its
canonical separation and the logarithm of its cardinality.

For Gibbs weights `pᵢ ∝ exp(b Xᵢ)`, rotate two independent copies of the process.
Differentiating the rotation identity yields
`E ∑ᵢ pᵢ Xᵢ = (b / 2) ∑ᵢⱼ E[pᵢ pⱼ] d(i,j)²`.
Separation therefore bounds `E ∑ᵢ pᵢ (1 - pᵢ)` from above in terms of the expected maximum.
Conversely, if one weight is large, the maximum score must exceed the arithmetic mean by
a multiple of `log |T| / b`. Taking `b = √(log |T|) / a` balances the two bounds.
-/

public section

namespace MathlibExt.Probability.MajorizingMeasureWanted

open MeasureTheory ProbabilityTheory MathlibExt.Probability.GenericChaining
open scoped ENNReal Topology

section

variable {T : Type*} [Fintype T] [Nonempty T]

private noncomputable abbrev weight (b : ℝ) (x : T → ℝ) :=
  Real.softmax (fun i => b * x i)

private noncomputable def average (p v : T → ℝ) : ℝ := ∑ i, p i * v i

omit [Nonempty T] in
private lemma average_le {p v : T → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {c : ℝ} (hv : ∀ i, v i ≤ c) : average p v ≤ c := by
  calc
    _ ≤ ∑ i, p i * c := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hp i)
    _ = c := by rw [← Finset.sum_mul, hs, one_mul]

omit [Nonempty T] in
private lemma abs_average_le {p v : T → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {c : ℝ} (hv : ∀ i, |v i| ≤ c) : |average p v| ≤ c := by
  calc
    _ ≤ ∑ i, |p i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = average p (fun i => |v i|) := by simp [average, abs_mul, abs_of_nonneg (hp _)]
    _ ≤ c := average_le hp hs hv

@[fun_prop] private lemma continuous_weight (b : ℝ) (i : T) :
    Continuous fun x : T → ℝ => weight b x i := by
  unfold weight Real.softmax
  exact (by fun_prop : Continuous fun x : T → ℝ => Real.exp (b * x i)).div
    (by fun_prop) (fun x => (Real.sum_exp_pos _).ne')

private lemma weight_hasDerivAt (b t : ℝ) {x : ℝ → T → ℝ} {v : T → ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (i : T) :
    HasDerivAt (fun s => weight b (x s) i)
      (b * weight b (x t) i * (v i - average (weight b (x t)) v)) t := by
  let e := fun s j => Real.exp (b * x s j)
  have he (j : T) : HasDerivAt (fun s => e s j) (e t j * (b * v j)) t :=
    ((hx j).const_mul b).exp
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => he j)
  have hn : (∑ j, e t j) ≠ 0 := (Real.sum_exp_pos _).ne'
  apply ((he i).div hs hn).congr_deriv
  change _ = b * (e t i / ∑ j, e t j) *
    (v i - ∑ j, e t j / (∑ k, e t k) * v j)
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  have hsum : ∑ j, e t j * (b * v j) = b * ∑ j, e t j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  field_simp

-- The second derivative of log-sum-exp is a weighted sum of squared increments.
private noncomputable def spread (p v : T → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * p j * (v i - v j) ^ 2

omit [Nonempty T] in
private lemma spread_eq {p : T → ℝ} (v : T → ℝ) (hs : ∑ i, p i = 1) :
    spread p v = 2 * (average p (fun i => v i ^ 2) - (average p v) ^ 2) := by
  have row (i : T) : ∑ j, p i * p j * (v i - v j) ^ 2 =
      p i * v i ^ 2 - 2 * p i * v i * average p v + p i * average p (fun j => v j ^ 2) := by
    simp only [average, Finset.mul_sum]
    rw [← mul_one (p i * v i ^ 2), ← hs, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [spread, row, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hs, one_mul, average]
  rw [show ∑ i, 2 * p i * v i = 2 * ∑ i, p i * v i by
    simp only [Finset.mul_sum, mul_assoc]]
  ring

private noncomputable abbrev rot (t : ℝ) (z : (T → ℝ) × (T → ℝ)) := ContinuousLinearMap.rotation t z

omit [Nonempty T] in
private lemma rot_deriv (t : ℝ) (z : (T → ℝ) × (T → ℝ)) (i : T) :
    HasDerivAt (fun s => (rot s z).1 i) ((rot t z).2 i) t ∧
    HasDerivAt (fun s => (rot s z).2 i) (-(rot t z).1 i) t := by
  constructor
  · exact ((Real.hasDerivAt_cos t).mul_const (z.1 i)).add
      ((Real.hasDerivAt_sin t).mul_const (z.2 i))
  · convert ((Real.hasDerivAt_sin t).neg.mul_const (z.1 i)).add
      ((Real.hasDerivAt_cos t).mul_const (z.2 i)) using 1
    · rfl
    simp only [rot, ContinuousLinearMap.rotation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

private noncomputable def score (b : ℝ) (z : (T → ℝ) × (T → ℝ)) :=
  average (weight b z.1) z.2

private noncomputable def scoreDeriv (b : ℝ) (z : (T → ℝ) × (T → ℝ)) :=
  b / 2 * spread (weight b z.1) z.2 - average (weight b z.1) z.1

private lemma score_hasDerivAt (b t : ℝ) (z : (T → ℝ) × (T → ℝ)) :
    HasDerivAt (fun s => score b (rot s z)) (scoreDeriv b (rot t z)) t := by
  let x := (rot t z).1
  let v := (rot t z).2
  let p := weight b x
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (weight_hasDerivAt b t (fun j => (rot_deriv t z j).1) i).mul (rot_deriv t z i).2)).congr_deriv
  change ∑ i, (b * p i * (v i - average p v) * v i + p i * -x i) =
    b / 2 * spread p v - average p x
  rw [spread_eq (p := p) _ (Real.sum_softmax _)]
  have h (i : T) : b * p i * (v i - average p v) * v i + p i * -x i =
      b * (p i * v i ^ 2) - b * average p v * (p i * v i) - p i * x i := by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, average]
  ring

omit [Nonempty T] in
private lemma rot_bound (t : ℝ) (z : (T → ℝ) × (T → ℝ)) (i : T) :
    |(rot t z).1 i| ≤ 2 * ‖z‖ ∧ |(rot t z).2 i| ≤ 2 * ‖z‖ := by
  have hx : |z.1 i| ≤ ‖z‖ := (norm_le_pi_norm _ i).trans (norm_fst_le z)
  have hy : |z.2 i| ≤ ‖z‖ := (norm_le_pi_norm _ i).trans (norm_snd_le z)
  change |Real.cos t * z.1 i + Real.sin t * z.2 i| ≤ _ ∧
    |-Real.sin t * z.1 i + Real.cos t * z.2 i| ≤ _
  constructor <;> grw [abs_add_le, abs_mul, abs_mul]
  · grw [Real.abs_cos_le_one, Real.abs_sin_le_one, hx, hy]
    linarith
  · grw [abs_neg, Real.abs_cos_le_one, Real.abs_sin_le_one, hx, hy]
    linarith

private lemma abs_scoreDeriv_le (b t : ℝ) (z : (T → ℝ) × (T → ℝ)) :
    |scoreDeriv b (rot t z)| ≤ (|b| / 2 * 16) * ‖z‖ ^ 2 + 2 * ‖z‖ := by
  let p := weight b (rot t z).1
  let v := (rot t z).2
  have hp (i : T) : 0 ≤ p i := (Real.softmax_pos _ _).le
  have hs : ∑ i, p i = 1 := Real.sum_softmax _
  have hv (i : T) : |v i| ≤ 2 * ‖z‖ := (rot_bound t z i).2
  have hdiff (i j : T) : |(v i - v j) ^ 2| ≤ 16 * ‖z‖ ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h := (abs_sub (v i) (v j)).trans (add_le_add (hv i) (hv j))
    nlinarith [sq_nonneg (‖z‖), mul_self_le_mul_self (abs_nonneg _) h]
  have hspread : |spread p v| ≤ 16 * ‖z‖ ^ 2 := by
    unfold spread
    simp_rw [mul_assoc, ← Finset.mul_sum]
    exact abs_average_le hp hs fun i => abs_average_le hp hs (hdiff i)
  unfold scoreDeriv
  grw [abs_sub, abs_mul, abs_div, hspread,
    abs_average_le hp hs (fun i => (rot_bound t z i).1)]
  norm_num
  linarith

private lemma continuous_score (b : ℝ) : Continuous (score (T := T) b) := by
  have hw (i : T) : Continuous fun z : (T → ℝ) × (T → ℝ) => weight b z.1 i :=
    (continuous_weight b i).comp continuous_fst
  unfold score average
  fun_prop (disch := assumption)

private lemma continuous_scoreDeriv (b : ℝ) : Continuous (scoreDeriv (T := T) b) := by
  have hw (i : T) : Continuous fun z : (T → ℝ) × (T → ℝ) => weight b z.1 i :=
    (continuous_weight b i).comp continuous_fst
  unfold scoreDeriv spread average
  fun_prop (disch := assumption)

private lemma integral_scoreDeriv (μ : Measure (T → ℝ)) [IsGaussian μ] (hμ : μ[id] = 0)
    (b : ℝ) : Integrable (scoreDeriv b) (μ.prod μ) ∧ ∫ z, scoreDeriv b z ∂μ.prod μ = 0 := by
  let ν := μ.prod μ
  have hnorm : Integrable (fun z => ‖z‖) ν := IsGaussian.integrable_id.norm
  have hsq : Integrable (fun z => ‖z‖ ^ 2) ν := IsGaussian.memLp_two_id.norm.integrable_sq
  have h0 (z : (T → ℝ) × (T → ℝ)) : rot 0 z = z := by
    simp [rot, ContinuousLinearMap.rotation_apply]
  have hscore : Integrable (score b) ν :=
    hnorm.mono' (continuous_score b).aestronglyMeasurable <| ae_of_all _ fun z =>
      abs_average_le (fun i => (Real.softmax_pos _ i).le) (Real.sum_softmax _)
        (fun i => (norm_le_pi_norm _ i).trans (norm_snd_le z))
  have hinv (t : ℝ) : (∫ z, score b (rot t z) ∂ν) = ∫ z, score b z ∂ν := by
    have hm : MeasurePreserving (ContinuousLinearMap.rotation t) ν ν :=
      ⟨(ContinuousLinearMap.rotation t).continuous.measurable, IsGaussian.map_rotation_eq_self hμ t⟩
    simpa only [hm.map_eq] using
      (integral_map (μ := ν) hm.measurable.aemeasurable
        (continuous_score b).aestronglyMeasurable).symm
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ))
    (F := fun t z => score b (rot t z)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((continuous_score b).comp (ContinuousLinearMap.rotation t).continuous).aestronglyMeasurable)
    (by simpa only [h0] using hscore)
    (F' := fun t z => scoreDeriv b (rot t z))
    (by simpa only [h0] using (continuous_scoreDeriv b).aestronglyMeasurable (μ := ν))
    (ae_of_all _ fun z t _ => abs_scoreDeriv_le b t z)
    ((hsq.const_mul _).add (hnorm.const_mul _))
    (ae_of_all _ fun z t _ => score_hasDerivAt b t z)
  constructor
  · simpa only [h0] using hd.1
  · simpa only [h0, hinv, deriv_const] using hd.2.deriv.symm

private noncomputable def center (x : T → ℝ) := (∑ i, x i) / Fintype.card T

omit [Fintype T] [Nonempty T] in
private lemma le_maximum [Finite T] (x : T → ℝ) (i : T) : x i ≤ ⨆ j, x j :=
  le_ciSup (Set.finite_range x).bddAbove i

private lemma center_le (x : T → ℝ) : center x ≤ ⨆ i, x i := by
  apply (div_le_iff₀ (by positivity : 0 < (Fintype.card T : ℝ))).mpr
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => le_maximum x i)

private lemma weight_le_one (b : ℝ) (x : T → ℝ) (i : T) : weight b x i ≤ 1 := by
  rw [← Real.sum_softmax (fun j => b * x j)]
  exact Finset.single_le_sum (fun j _ => (Real.softmax_pos _ j).le) (Finset.mem_univ i)

private noncomputable def offDiag (p : T → ℝ) := average p (fun i => 1 - p i)

-- When the maximum is close to the arithmetic mean, no Gibbs weight can be close to one.
private lemma log_card_le (hn : 2 ≤ Fintype.card T) {b : ℝ} (hb : 0 ≤ b) (x : T → ℝ) :
    Real.log (Fintype.card T) ≤
      4 * Real.log (Fintype.card T) * offDiag (weight b x) +
        2 * b * ((⨆ i, x i) - center x) := by
  let n : ℝ := Fintype.card T
  let r := b * ((⨆ i, x i) - center x)
  have hn' : 2 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hr : 0 ≤ r := mul_nonneg hb (sub_nonneg.mpr (center_le x))
  have hp (i : T) : 0 ≤ weight b x i := (Real.softmax_pos _ _).le
  change Real.log n ≤ 4 * Real.log n * offDiag (weight b x) + _
  by_cases h : r ≤ Real.log n / 2
  · let u := fun i => b * x i + -(b * center x)
    have hden : n ≤ ∑ i, Real.exp (u i) := by
      calc
        n = ∑ i, (u i + 1) := by
          simp only [u, center, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, mul_one]
          change n = b * (∑ i, x i) + n * -(b * ((∑ i, x i) / n)) + n
          field_simp
          ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => Real.add_one_le_exp _
    have hexp : Real.exp (Real.log n / 2) ^ 2 = n := by
      rw [sq, ← Real.exp_add, add_halves, Real.exp_log hn0]
    have hsmall (i : T) : weight b x i ≤ 3 / 4 := by
      rw [weight, ← Real.softmax_add_const _ (-(b * center x))]
      change Real.exp (u i) / (∑ j, Real.exp (u j)) ≤ _
      apply (div_le_iff₀ (hn0.trans_le hden)).mpr
      have hu : u i ≤ Real.log n / 2 := le_trans (by
        dsimp [u, r]
        nlinarith [mul_le_mul_of_nonneg_left (le_maximum x i) hb] : u i ≤ r) h
      nlinarith [Real.exp_le_exp.mpr hu, sq_nonneg (Real.exp (Real.log n / 2) - 1)]
    have hoff : 1 / 4 ≤ offDiag (weight b x) := by
      calc
        (1 : ℝ) / 4 = ∑ i, weight b x i * (1 / 4) := by
          rw [← Finset.sum_mul, Real.sum_softmax, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by linarith [hsmall i]) (hp i)
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hoff)]
  · have hoff : 0 ≤ offDiag (weight b x) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sub_nonneg.mpr (weight_le_one b x i))
    dsimp [r] at h
    nlinarith [mul_nonneg hl hoff]

omit [Fintype T] [Nonempty T] in
private lemma integrable_sq_diff [Finite T] (μ : Measure (T → ℝ)) [IsGaussian μ] (i j : T) :
    Integrable (fun y : T → ℝ => (y i - y j) ^ 2) μ := by
  let _ := Fintype.ofFinite T
  have h : MemLp (id : (T → ℝ) → T → ℝ) 2 μ := IsGaussian.memLp_two_id
  exact ((h.eval i).sub (h.eval j)).integrable_sq

omit [Nonempty T] in
private lemma integral_spread_ge (μ : Measure (T → ℝ)) [IsGaussian μ] (a : ℝ)
    (hsep : ∀ i j : T, i ≠ j → a ^ 2 ≤ ∫ y, (y i - y j) ^ 2 ∂μ)
    {p : T → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    a ^ 2 * offDiag p ≤ ∫ y, spread p y ∂μ := by
  classical
  have hterm (i j : T) := (integrable_sq_diff μ i j).const_mul (p i * p j)
  simp only [spread,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j)),
    integral_finsetSum _ (fun j _ => hterm _ j), integral_const_mul]
  have hrow (i : T) : a ^ 2 * (p i * (1 - p i)) ≤
      ∑ j, p i * p j * (∫ y, (y i - y j) ^ 2 ∂μ) := by
    have he : ∑ j, (p j - if j = i then p i else 0) = 1 - p i := by
      simp [Finset.sum_sub_distrib, hs]
    rw [← he, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i
    · subst j
      simp
    · rw [ite_eq_right hj, sub_zero, mul_comm (a ^ 2)]
      exact mul_le_mul_of_nonneg_left (hsep i j (Ne.symm hj)) (mul_nonneg (hp i) (hp j))
  simpa only [offDiag, average, Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hrow i)

private lemma gaussian_bound (μ : Measure (T → ℝ)) [IsGaussian μ]
    (hcen : ∀ i, ∫ x, x i ∂μ = 0) {a : ℝ} (ha : 0 ≤ a)
    (hsep : ∀ i j : T, i ≠ j → a ^ 2 ≤ ∫ y, (y i - y j) ^ 2 ∂μ) :
    a / 10 * Real.sqrt (Real.log (Fintype.card T)) ≤ ∫ x, ⨆ i, x i ∂μ := by
  let m := fun x : T → ℝ => ⨆ i, x i
  have heval (i : T) : Integrable (fun x : T → ℝ => x i) μ := IsGaussian.integrable_id.eval i
  have hm : Integrable m μ := by
    refine IsGaussian.integrable_id.norm.mono'
      (Measurable.iSup (fun i : T => measurable_pi_apply i)).aestronglyMeasurable ?_
    refine ae_of_all _ fun x => ?_
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    change ‖⨆ j, x j‖ ≤ ‖x‖
    rw [← hi]
    exact norm_le_pi_norm x i
  have hM : 0 ≤ ∫ x, m x ∂μ := by
    let i : T := Classical.choice inferInstance
    simpa only [hcen i] using integral_mono (heval i) hm (fun x => le_maximum x i)
  by_cases hcard : 2 ≤ Fintype.card T
  swap
  · have h1 : Fintype.card T = 1 := by have := Fintype.card_pos (α := T); omega
    simpa [h1, m] using hM
  obtain rfl | ha := ha.eq_or_lt
  · simpa [m] using hM
  let l := Real.log (Fintype.card T)
  have hl : 0 < l := Real.log_pos (by exact_mod_cast (show 1 < Fintype.card T by omega))
  let b := Real.sqrt l / a
  have hb : 0 < b := div_pos (Real.sqrt_pos.mpr hl) ha
  let p := weight (T := T) b
  let q := fun x => offDiag (p x)
  have hq : Integrable q μ := by
    have hc : Continuous q := by
      have hw := continuous_weight (T := T) b
      unfold q p offDiag average
      fun_prop (disch := assumption)
    apply (integrable_const (μ := μ) (1 : ℝ)).mono' hc.aestronglyMeasurable
    refine ae_of_all _ fun x => abs_average_le
      (fun i => (Real.softmax_pos _ _).le) (Real.sum_softmax _) (fun i => ?_)
    rw [abs_of_nonneg (sub_nonneg.mpr (weight_le_one b x i))]
    linarith [Real.softmax_pos (fun i => b * x i) i]
  have hμ : μ[id] = 0 := by
    ext i
    exact (eval_integral heval i).trans (hcen i)
  obtain ⟨hDi, hD⟩ := integral_scoreDeriv μ hμ b
  have hf (x : T → ℝ) : Integrable (fun y => spread (p x) y) μ := by
    apply integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (integrable_sq_diff μ i j).const_mul _
  have hpt (x : T → ℝ) :
      b / 2 * a ^ 2 * q x - m x ≤ ∫ y, scoreDeriv b (x, y) ∂μ := by
    change _ ≤ ∫ y, b / 2 * spread (p x) y - average (p x) x ∂μ
    rw [integral_sub ((hf x).const_mul (b / 2)) (integrable_const (average (p x) x)),
      integral_const_mul, integral_const, probReal_univ, one_smul]
    have hs := integral_spread_ge μ a hsep (p := p x)
      (fun i => (Real.softmax_pos _ i).le) (Real.sum_softmax _)
    have hav := average_le (fun i => (Real.softmax_pos (fun j => b * x j) i).le)
      (Real.sum_softmax _) (le_maximum x)
    change _ ≤ b / 2 * (∫ y, spread (p x) y ∂μ) - average (p x) x
    dsimp only [q, m]
    linarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ b / 2 by positivity)]
  have henergy := integral_mono ((hq.const_mul (b / 2 * a ^ 2)).sub hm)
    hDi.integral_prod_left hpt
  simp only [Pi.sub_apply] at henergy
  rw [← integral_prod _ hDi, hD, integral_sub (hq.const_mul _) hm,
    integral_const_mul] at henergy
  have hc : Integrable center μ := (integrable_finsetSum _ (fun i _ => heval i)).div_const _
  have hc0 : ∫ x, center x ∂μ = 0 := by
    simp [center, integral_div, integral_finsetSum _ (fun i _ => heval i), hcen]
  have hgap : Integrable (fun x => m x - center x) μ := hm.sub hc
  have hent := integral_mono (integrable_const (μ := μ) l)
    ((hq.const_mul (4 * l)).add (hgap.const_mul (2 * b))) (log_card_le hcard hb.le)
  simp only [Pi.add_apply] at hent
  simp only [integral_const, probReal_univ, one_smul, integral_add (hq.const_mul (4 * l))
    (hgap.const_mul (2 * b)), integral_const_mul, integral_sub hm hc, hc0, sub_zero] at hent
  have hb2 : b ^ 2 * a ^ 2 = l := by
    rw [← mul_pow, div_mul_cancel₀ _ ha.ne', Real.sq_sqrt hl.le]
  have hfinal : l ≤ 10 * b * ∫ x, m x ∂μ := by
    nlinarith only [hent, mul_nonneg hb.le (neg_nonneg.mpr henergy),
      congrArg (fun r : ℝ => r * ∫ x, q x ∂μ) hb2]
  change a / 10 * Real.sqrt l ≤ ∫ x, m x ∂μ
  apply le_of_mul_le_mul_left (a := b) (by
    calc
      b * (a / 10 * Real.sqrt l) = l / 10 := by
        dsimp only [b]
        field_simp
        nlinarith [Real.sq_sqrt hl.le]
      _ ≤ _ := by linarith) hb

end

/-- **Sudakov minoration** (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, Lemma 2.10.2). There is a universal constant `L₁ > 0` such that for every centred
Gaussian process `(X_t)_{t ∈ T}` on a finite nonempty set whose points are pairwise `a`-separated
for the canonical distance (`d(s, t) ≥ a` whenever `s ≠ t`), `E sup_{t ∈ T} X_t ≥
(a / L₁) √(log card T)`. -/
theorem sudakov_minoration :
    ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (T : Type*) [Fintype T] [Nonempty T] (X : T → Ω → ℝ) (a : ℝ),
      (∀ t, Measurable (X t)) → IsGaussian (P.map fun ω t => X t ω) →
      (∀ t, ∫ ω, X t ω ∂P = 0) → 0 ≤ a →
      (∀ s t, s ≠ t → ENNReal.ofReal a ≤ canonicalDist P X s t) →
        a / L₁ * Real.sqrt (Real.log (Fintype.card T)) ≤ ∫ ω, ⨆ t, X t ω ∂P := by
  refine ⟨10, by norm_num, ?_⟩
  intro Ω _ P _ T _ _ X a hX hG hcen ha hsep
  let Y : Ω → T → ℝ := fun ω t => X t ω
  have hY : Measurable Y := Measurable.of_eval hX
  let μ := P.map Y
  have hmean (i : T) : ∫ x, x i ∂μ = 0 := by
    rw [integral_map hY.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    exact hcen i
  have hdist (i j : T) (h : i ≠ j) : a ^ 2 ≤ ∫ y, (y i - y j) ^ 2 ∂μ := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
    have hs := hsep i j h
    rw [canonicalDist_eq_ofReal_sqrt (memLp_sub_of_isGaussian P X hX hG i j)] at hs
    have hd := (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hs
    exact (Real.le_sqrt (by positivity) (integral_nonneg fun _ => sq_nonneg _)).mp hd
  have bound := gaussian_bound μ hmean ha hdist
  rwa [integral_map hY.aemeasurable
    (Measurable.iSup (fun i : T => measurable_pi_apply i)).aestronglyMeasurable] at bound

end MathlibExt.Probability.MajorizingMeasureWanted
