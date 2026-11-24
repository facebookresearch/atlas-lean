/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Probability.Distributions.Gaussian.Fernique
import MathlibExt.Analysis.SpecialFunctions.LogSumExp
import MathlibExt.Probability.GaussianLipschitzConcentration
import MathlibExt.Probability.Statistics.SteinLemma

/-!
# Largest singular value of a standard Gaussian matrix

We prove the one-sided Gaussian tail bound for the largest singular value of a rectangular
matrix with independent standard normal entries.

To bound the mean by `√n + √d`, we use the Gaussian comparison argument on finite nets of
the two unit spheres. Gaussian integration by parts makes the expected log-sum-exp monotone
along a trigonometric interpolation between the two processes. The operator norm is
`1`-Lipschitz in the Euclidean norm of the entries, so one-sided Gaussian concentration gives
the tail above the mean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace MathlibExt.Probability.GaussianRandomMatrixWanted

section

open Finset Set Filter
open scoped Topology RealInnerProductSpace

private noncomputable def gaussianPi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

private instance gaussianPi_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (gaussianPi ι) := by
  unfold gaussianPi
  infer_instance

private lemma integrable_coordinate {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun x => x i) (gaussianPi ι) :=
  integrable_eval IsGaussian.integrable_id

private lemma integral_mul_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    {f df : (ι → ℝ) → ℝ}
    (hd : ∀ x t, HasDerivAt (fun s => f (Function.update x i s))
      (df (Function.update x i t)) t)
    (hdf : Integrable df (gaussianPi ι))
    (hf : Integrable (fun x => x i * f x) (gaussianPi ι)) :
    ∫ x, x i * f x ∂gaussianPi ι = ∫ x, df x ∂gaussianPi ι := by
  let e := (Fintype.equivFin ι).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hE : MeasurePreserving E (gaussianPi (Fin (Fintype.card ι))) (gaussianPi ι) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  let j := e.symm i
  have hEapp (y : Fin (Fintype.card ι) → ℝ) (k : ι) : E y k = y (e.symm k) := by
    simp [E, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hupdate (y : Fin (Fintype.card ι) → ℝ) (t : ℝ) :
      E (Function.update y j t) = Function.update (E y) i t := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [hEapp, j]
    · rw [hEapp, Function.update_of_ne (e.symm.injective.ne hk), Function.update_of_ne hk, hEapp]
  rw [← hE.integral_comp' (fun x => x i * f x), ← hE.integral_comp' df]
  simp only [hEapp]
  have h := integral_sub_mul_pi_gaussianReal (fun _ : Fin (Fintype.card ι) => 0) j
    (h := f ∘ E) (dh := df ∘ E)
  simp only [sub_zero, Function.comp_apply] at h
  apply h
  · exact ae_of_all _ fun y t => by simpa only [hupdate] using hd (E y) t
  · exact (hE.integrable_comp_emb E.measurableEmbedding).2 hdf
  · have hf' := (hE.integrable_comp_emb E.measurableEmbedding).2 hf
    change Integrable (fun y => E y i * f (E y)) _ at hf'
    change Integrable (fun y => y j * f (E y)) (gaussianPi (Fin (Fintype.card ι)))
    simpa only [hEapp, j] using hf'

/-! ### Gaussian comparison on finite index sets -/

private lemma softmax_le_one {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ) (i : I) :
    Real.softmax z i ≤ 1 := by
  rw [← Real.sum_softmax z]
  exact single_le_sum (fun j _ => (Real.softmax_pos z j).le) (mem_univ i)

private lemma hasDerivAt_softmax {I : Type*} [Fintype I] [Nonempty I] {z : ℝ → I → ℝ}
    {v : I → ℝ} {t : ℝ} (hz : ∀ i, HasDerivAt (fun s => z s i) (v i) t) (i : I) :
    HasDerivAt (fun s => Real.softmax (z s) i)
      (Real.softmax (z t) i * (v i - ∑ j, Real.softmax (z t) j * v j)) t := by
  have hsum := HasDerivAt.fun_sum (u := univ) fun j _ => (hz j).exp
  convert (hz i).exp.div hsum (Real.sum_exp_pos (z t)).ne' using 1
  all_goals first
    | rfl
    | simp only [Real.softmax, div_mul_eq_mul_div, ← sum_div]
      field_simp

private lemma hasDerivAt_logSumExp_curve {I : Type*} [Fintype I] [Nonempty I] {z : ℝ → I → ℝ}
    {v : I → ℝ} {t : ℝ} (hz : ∀ i, HasDerivAt (fun s => z s i) (v i) t) :
    HasDerivAt (fun s => Real.logSumExp (z s))
      (∑ i, Real.softmax (z t) i * v i) t := by
  have hsum := HasDerivAt.fun_sum (u := univ) fun j _ => (hz j).exp
  convert hsum.log (Real.sum_exp_pos (z t)).ne' using 1
  · rfl
  · rw [sum_div]
    exact sum_congr rfl fun i _ => by rw [Real.softmax, div_mul_eq_mul_div]

private lemma abs_weighted_sum_le {I : Type*} [Fintype I] [Nonempty I] (z v : I → ℝ)
    {C : ℝ} (h : ∀ i, |v i| ≤ C) : |∑ i, Real.softmax z i * v i| ≤ C := by
  calc
    _ ≤ ∑ i, |Real.softmax z i * v i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.softmax z i * C := sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_pos (Real.softmax_pos z i)]
      exact mul_le_mul_of_nonneg_left (h i) (Real.softmax_pos z i).le
    _ = C := by rw [← sum_mul, Real.sum_softmax, one_mul]

private lemma logSumExp_ge {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ) (i : I) :
    z i ≤ Real.logSumExp z := by
  rw [← Real.log_exp (z i)]
  exact Real.log_le_log (Real.exp_pos _) (single_le_sum (fun j _ => (Real.exp_pos _).le)
    (mem_univ i))

private lemma logSumExp_le {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ)
    {C : ℝ} (h : ∀ i, z i ≤ C) : Real.logSumExp z ≤ C + Real.log (Fintype.card I) := by
  rw [Real.logSumExp, add_comm, ← Real.log_exp C,
    ← Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (Real.exp_ne_zero _)]
  apply Real.log_le_log (Real.sum_exp_pos z)
  simpa using (sum_le_sum (s := (univ : Finset I)) fun i _ => Real.exp_le_exp.mpr (h i))

private lemma integrable_logSumExp {ι I : Type*} [Fintype ι] [Fintype I] [Nonempty I]
    (A : I → ι → ℝ) : Integrable (fun x => Real.logSumExp (fun i => ∑ k, A i k * x k))
      (gaussianPi ι) := by
  let bound (x : ι → ℝ) := ∑ i, ∑ k, |A i k| * |x k|
  have hb : Integrable bound (gaussianPi ι) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (integrable_coordinate k).abs.const_mul _
  have hb' (x : ι → ℝ) (i : I) : |∑ k, A i k * x k| ≤ bound x := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp_rw [abs_mul]
    exact single_le_sum (f := fun j => ∑ k, |A j k| * |x k|)
      (fun j _ => sum_nonneg fun k _ => by positivity) (mem_univ i)
  refine (hb.add (integrable_const (Real.log (Fintype.card I)))).mono' ?_ ?_
  · exact Real.measurable_log.comp (by fun_prop) |>.aestronglyMeasurable
  filter_upwards with x
  have hcard : 0 ≤ Real.log (Fintype.card I) :=
    Real.log_nonneg (by exact_mod_cast (Fintype.card_pos (α := I)))
  rw [Real.norm_eq_abs, abs_le, Pi.add_apply]
  refine ⟨?_, logSumExp_le _ fun i => (le_abs_self _).trans (hb' x i)⟩
  let i := Classical.arbitrary I
  have h₁ := neg_le_abs (∑ k, A i k * x k)
  have h₂ := hb' x i
  have h₃ := logSumExp_ge (fun i => ∑ k, A i k * x k) i
  linarith


/-- Finite Gaussian comparison via interpolation of the expected log-sum-exp. -/
private lemma integral_logSumExp_le {ι I : Type*} [Fintype ι] [Fintype I] [Nonempty I]
    (A B : I → ι → ℝ) (hdisj : ∀ i j k, A i k * B j k = 0)
    (hcmp : ∀ i j, ∑ k, A i k * (A i k - A j k) ≤ ∑ k, B i k * (B i k - B j k)) :
    ∫ x, Real.logSumExp (fun i => ∑ k, A i k * x k) ∂gaussianPi ι ≤
      ∫ x, Real.logSumExp (fun i => ∑ k, B i k * x k) ∂gaussianPi ι := by
  classical
  let W (t : ℝ) (i : I) (k : ι) := Real.cos t * A i k + Real.sin t * B i k
  let V (t : ℝ) (i : I) (k : ι) := -Real.sin t * A i k + Real.cos t * B i k
  let z (t : ℝ) (x : ι → ℝ) (i : I) := ∑ k, W t i k * x k
  let p (t : ℝ) (x : ι → ℝ) (i : I) := Real.softmax (z t x) i
  let F (t : ℝ) (x : ι → ℝ) := Real.logSumExp (z t x)
  let G (t : ℝ) (x : ι → ℝ) := ∑ i, p t x i * ∑ k, V t i k * x k
  let C (i : I) (k : ι) := |A i k| + |B i k|
  have hC (t : ℝ) (i : I) (k : ι) : |W t i k| ≤ C i k ∧ |V t i k| ≤ C i k := by
    have hmul (r a : ℝ) (hr : |r| ≤ 1) : |r * a| ≤ |a| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hr
    constructor
    · exact (abs_add_le _ _).trans (add_le_add (hmul _ _ (Real.abs_cos_le_one t))
        (hmul _ _ (Real.abs_sin_le_one t)))
    · exact (abs_add_le _ _).trans (add_le_add (hmul _ _ (by simpa using Real.abs_sin_le_one t))
        (hmul _ _ (Real.abs_cos_le_one t)))
  have hp (t : ℝ) (i : I) : Continuous fun x => p t x i := by
    unfold p Real.softmax z
    exact (by fun_prop : Continuous fun x : ι → ℝ => Real.exp (∑ k, W t i k * x k)).div
      (by fun_prop) (fun x => (Real.sum_exp_pos (z t x)).ne')
  have hG (t : ℝ) : Continuous (G t) := by
    unfold G
    fun_prop
  have hF (t : ℝ) : Continuous (F t) := by
    unfold F Real.logSumExp z
    exact Continuous.log (by fun_prop) fun x => (Real.sum_exp_pos (z t x)).ne'
  have hd (t : ℝ) :
      HasDerivAt (fun s => ∫ x, F s x ∂gaussianPi ι) (∫ x, G t x ∂gaussianPi ι) t := by
    let bound (x : ι → ℝ) := ∑ i, ∑ k, C i k * |x k|
    have hbound : Integrable bound (gaussianPi ι) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        (integrable_coordinate k).abs.const_mul _
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
      (bound := bound) (F := F) (F' := G) univ_mem
      (Eventually.of_forall fun s => (hF s).aestronglyMeasurable)
      (integrable_logSumExp (W t)) (hG t).aestronglyMeasurable
      (ae_of_all _ fun x s _ => ?_) hbound (ae_of_all _ fun x s _ => ?_)).2
    · rw [Real.norm_eq_abs]
      refine abs_weighted_sum_le _ _ fun i => (abs_sum_le_sum_abs _ _).trans ?_
      simp_rw [abs_mul]
      exact (sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hC s i k).2 (abs_nonneg _))
        |>.trans (single_le_sum (f := fun j => ∑ k, C j k * |x k|)
          (fun j _ => sum_nonneg fun k _ => by dsimp [C]; positivity)
          (mem_univ i))
    · refine hasDerivAt_logSumExp_curve fun i => HasDerivAt.fun_sum fun k _ => ?_
      exact (((Real.hasDerivAt_cos s).mul_const (A i k)).add
        ((Real.hasDerivAt_sin s).mul_const (B i k))).mul_const (x k)
  -- The coordinate derivative of the softmax supplies the integration-by-parts term.
  let q (t : ℝ) (i : I) (k : ι) (x : ι → ℝ) :=
    p t x i * (W t i k - ∑ j, p t x j * W t j k)
  have hq (t : ℝ) (i : I) (k : ι) : Integrable (q t i k) (gaussianPi ι) := by
    refine (integrable_const (C i k + ∑ j, C j k)).mono' ?_ ?_
    · have hcont : Continuous (q t i k) := by unfold q; fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards with x
      have hpabs : |p t x i| ≤ 1 := by
        rw [abs_of_pos (Real.softmax_pos (z t x) i)]
        exact softmax_le_one _ _
      have hw : |∑ j, p t x j * W t j k| ≤ ∑ j, C j k := by
        refine abs_weighted_sum_le _ _ fun j => (hC t j k).1.trans ?_
        exact single_le_sum (f := fun l => C l k) (fun l _ => by dsimp [C]; positivity) (mem_univ j)
      change |q t i k x| ≤ _
      dsimp only [q]
      rw [abs_mul]
      calc
        _ ≤ 1 * |W t i k - ∑ j, p t x j * W t j k| :=
          mul_le_mul_of_nonneg_right hpabs (abs_nonneg _)
        _ ≤ C i k + ∑ j, C j k := by
          rw [one_mul]
          exact (abs_sub _ _).trans (add_le_add (hC t i k).1 hw)
  have hpint (t : ℝ) (i : I) (k : ι) :
      Integrable (fun x => x k * p t x i) (gaussianPi ι) := by
    refine (integrable_coordinate k).abs.mono'
      (((continuous_apply k).mul (hp t i)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.softmax_pos (z t x) i)]
    exact mul_le_of_le_one_right (abs_nonneg _) (softmax_le_one _ _)
  have hstein (t : ℝ) (i : I) (k : ι) :
      ∫ x, x k * p t x i ∂gaussianPi ι = ∫ x, q t i k x ∂gaussianPi ι := by
    refine integral_mul_coordinate k (fun x s => ?_) (hq t i k) (hpint t i k)
    refine hasDerivAt_softmax (z := fun s => z t (Function.update x k s))
      (v := fun j => W t j k) (fun j => ?_) i
    change HasDerivAt (fun s => ∑ l, W t j l * Function.update x k s l) (W t j k) s
    have hs : HasDerivAt (fun s => ∑ l, W t j l * Function.update x k s l)
        (∑ l, if l = k then W t j l else 0) s := by
      refine HasDerivAt.fun_sum fun l _ => ?_
      by_cases hl : l = k
      · subst l
        simpa using (hasDerivAt_id s).const_mul (W t j k)
      · simpa [Function.update_of_ne hl, hl] using hasDerivAt_const s (W t j l * x l)
    simpa using hs
  have hpair (t : ℝ) (i j : I) :
      ∑ k, V t i k * (W t i k - W t j k) =
        Real.sin t * Real.cos t *
          ((∑ k, B i k * (B i k - B j k)) - ∑ k, A i k * (A i k - A j k)) := by
    simp_rw [mul_sub, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    dsimp [V, W]
    linear_combination
      (Real.cos t ^ 2) * hdisj i i k - (Real.cos t ^ 2) * hdisj j i k -
      (Real.sin t ^ 2) * hdisj i i k + (Real.sin t ^ 2) * hdisj i j k
  have hweighted (t : ℝ) (x : ι → ℝ) :
      ∑ i, ∑ k, V t i k * q t i k x =
        ∑ i, ∑ j, (p t x i * p t x j) * ∑ k, V t i k * (W t i k - W t j k) := by
    refine sum_congr rfl fun i _ => ?_
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    have hone : ∑ j, p t x j = 1 := Real.sum_softmax _
    simp_rw [mul_sub, show ∀ j, p t x i * p t x j * (V t i k * W t i k) =
      (p t x i * (V t i k * W t i k)) * p t x j from fun j => by ring,
      show ∀ j, p t x i * p t x j * (V t i k * W t j k) =
      (p t x i * V t i k) * (p t x j * W t j k) from fun j => by ring,
      sum_sub_distrib, ← mul_sum, hone, mul_one]
    dsimp [q]
    ring
  have hn (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
      0 ≤ ∫ x, G t x ∂gaussianPi ι := by
    have hg : G t = fun x => ∑ i, ∑ k, V t i k * (x k * p t x i) := by
      ext x
      unfold G
      simp_rw [mul_sum]
      exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
    have hEq : ∫ x, G t x ∂gaussianPi ι =
        ∫ x, (∑ i, ∑ k, V t i k * q t i k x) ∂gaussianPi ι := by
      rw [hg, integral_finsetSum, integral_finsetSum]
      · refine sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum, integral_finsetSum]
        · simp_rw [integral_const_mul, hstein]
        · exact fun k _ => (hq t i k).const_mul _
        · exact fun k _ => (hpint t i k).const_mul _
      · exact fun i _ => integrable_finsetSum _ fun k _ => (hq t i k).const_mul _
      · exact fun i _ => integrable_finsetSum _ fun k _ => (hpint t i k).const_mul _
    rw [hEq]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    refine integral_nonneg fun x => ?_
    rw [hweighted]
    refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
    rw [hpair]
    exact mul_nonneg (mul_nonneg (Real.softmax_pos _ _).le (Real.softmax_pos _ _).le)
      (mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hcmp i j)))
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t).deriv]; exact hn t (interior_subset ht))
  have hh := hmono (left_mem_Icc.mpr Real.pi_div_two_pos.le)
    (right_mem_Icc.mpr Real.pi_div_two_pos.le) Real.pi_div_two_pos.le
  simpa [F, z, W] using hh

private lemma integral_le_of_finite_comparison {ι I : Type*} [Fintype ι] [Finite I]
    [Nonempty I] (A B : I → ι → ℝ) (hdisj : ∀ i j k, A i k * B j k = 0)
    (hcmp : ∀ i j, ∑ k, A i k * (A i k - A j k) ≤ ∑ k, B i k * (B i k - B j k))
    {L U : (ι → ℝ) → ℝ} (hL : Integrable L (gaussianPi ι)) (hU : Integrable U (gaussianPi ι))
    (hlo : ∀ x, ∃ i, L x ≤ ∑ k, A i k * x k) (hhi : ∀ x i, ∑ k, B i k * x k ≤ U x) :
    ∫ x, L x ∂gaussianPi ι ≤ ∫ x, U x ∂gaussianPi ι := by
  let : Fintype I := Fintype.ofFinite I
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let c := Real.log (Fintype.card I)
  let r := (c + 1) / ε
  have hc : 0 ≤ c := Real.log_nonneg (by exact_mod_cast (Fintype.card_pos (α := I)))
  have hr : 0 < r := div_pos (by linarith) hε
  have hrε : c ≤ r * ε := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hε.ne']
    linarith
  let A' (i : I) (k : ι) := r * A i k
  let B' (i : I) (k : ι) := r * B i k
  have hscale (D : I → ι → ℝ) (i j : I) :
      ∑ k, (r * D i k) * (r * D i k - r * D j k) =
        r ^ 2 * ∑ k, D i k * (D i k - D j k) := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have hcompare := integral_logSumExp_le A' B'
    (fun i j k => by dsimp [A', B']; linear_combination (r ^ 2) * hdisj i j k)
    (fun i j => by
      dsimp [A', B']
      rw [hscale, hscale]
      exact mul_le_mul_of_nonneg_left (hcmp i j) (sq_nonneg _))
  have h₁ : r * (∫ x, L x ∂gaussianPi ι) ≤
      ∫ x, Real.logSumExp (fun i => ∑ k, A' i k * x k) ∂gaussianPi ι := by
    rw [← integral_const_mul]
    refine integral_mono (hL.const_mul r) (integrable_logSumExp A') fun x => ?_
    obtain ⟨i, hi⟩ := hlo x
    refine (mul_le_mul_of_nonneg_left hi hr.le).trans ?_
    rw [mul_sum]
    simpa only [A', mul_assoc] using logSumExp_ge (fun i => ∑ k, A' i k * x k) i
  have h₂ : (∫ x, Real.logSumExp (fun i => ∑ k, B' i k * x k) ∂gaussianPi ι) ≤
      r * (∫ x, U x ∂gaussianPi ι) + c := by
    have heq : (∫ x : ι → ℝ, c ∂gaussianPi ι) = c := by simp
    rw [← integral_const_mul, ← heq, ← integral_add (hU.const_mul r) (integrable_const c)]
    refine integral_mono (integrable_logSumExp B') ((hU.const_mul r).add (integrable_const c))
      fun x => logSumExp_le _ fun i => ?_
    simp_rw [B', mul_assoc, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (hhi x i) hr.le
  have h := h₁.trans (hcompare.trans h₂)
  apply le_of_mul_le_mul_left _ hr
  rw [mul_add]
  linarith

/-! ### The mean of the Gaussian operator norm -/

private noncomputable def matrixMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Matrix m n ℝ ≃ₗ[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

private noncomputable def matrixOf {m n : Type*} (x : EuclideanSpace ℝ (m × n)) :
    Matrix m n ℝ := Matrix.of fun i j => x.ofLp (i, j)

private lemma norm_matrixMap_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (x : EuclideanSpace ℝ (m × n)) : ‖matrixMap (matrixOf x)‖ ≤ ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq x,
    EuclideanSpace.real_norm_sq_eq u, Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private noncomputable def operatorNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (x : EuclideanSpace ℝ (m × n)) : ℝ := ‖matrixMap (matrixOf x)‖

private lemma lipschitzWith_operatorNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    LipschitzWith 1 (operatorNorm (m := m) (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  change |‖matrixMap (matrixOf x)‖ - ‖matrixMap (matrixOf y)‖| ≤ ‖x - y‖
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← map_sub]
  exact norm_matrixMap_le (x - y)

private lemma integral_norm_pi_le {ι : Type*} [Fintype ι] :
    (∫ x : ι → ℝ, ‖WithLp.toLp 2 x‖ ∂gaussianPi ι) ≤ Real.sqrt (Fintype.card ι) := by
  have hmap : (gaussianPi ι).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι) :=
    map_pi_eq_stdGaussian
  have hto : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) := by fun_prop
  have h2 : MemLp (fun x : EuclideanSpace ℝ ι => ‖x‖) 2 (stdGaussian _) :=
    IsGaussian.memLp_two_id.norm
  have hnorm : MemLp (fun x : ι → ℝ => ‖WithLp.toLp 2 x‖) 2 (gaussianPi ι) :=
    (hmap ▸ h2).comp_of_map hto.aemeasurable
  have hsq (i : ι) : Integrable (fun x : ι → ℝ => x i ^ 2) (gaussianPi ι) := by
    have h : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) :=
      IsGaussian.memLp_two_id.integrable_sq
    exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable h
  have hmoment : (∫ t : ℝ, t ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_integral (μ := gaussianReal 0 1) (X := id) aemeasurable_id
    simpa using h.symm
  have hmomentPi : (∫ x : ι → ℝ, ‖WithLp.toLp 2 x‖ ^ 2 ∂gaussianPi ι) = Fintype.card ι := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum _ (fun i _ => hsq i)]
    have hi (i : ι) : (∫ x : ι → ℝ, x i ^ 2 ∂gaussianPi ι) = 1 :=
      (integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
        (f := fun t => t ^ 2) (by fun_prop)).trans hmoment
    simp [hi]
  have hv := variance_nonneg (fun x : ι → ℝ => ‖WithLp.toLp 2 x‖) (gaussianPi ι)
  rw [variance_eq_sub hnorm] at hv
  simp only [Pi.pow_apply, hmomentPi] at hv
  exact Real.le_sqrt_of_sq_le (sub_nonneg.mp hv)

private lemma measurePreserving_inl {α β : Type*} [Fintype α] [Fintype β] :
    MeasurePreserving (fun x : (α ⊕ β) → ℝ => fun i : α => x (.inl i))
      (gaussianPi (α ⊕ β)) (gaussianPi α) :=
  measurePreserving_fst.comp
    (measurePreserving_sumPiEquivProdPi (fun _ : α ⊕ β => gaussianReal 0 1))

private lemma measurePreserving_inr {α β : Type*} [Fintype α] [Fintype β] :
    MeasurePreserving (fun x : (α ⊕ β) → ℝ => fun i : β => x (.inr i))
      (gaussianPi (α ⊕ β)) (gaussianPi β) :=
  measurePreserving_snd.comp
    (measurePreserving_sumPiEquivProdPi (fun _ : α ⊕ β => gaussianReal 0 1))

private lemma integrable_pi_norm {ι : Type*} [Fintype ι] :
    Integrable (fun x : ι → ℝ => ‖WithLp.toLp 2 x‖) (gaussianPi ι) := by
  have h : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) (stdGaussian _) :=
    IsGaussian.integrable_id.norm
  rw [← map_pi_eq_stdGaussian] at h
  exact h.comp_measurable (by fun_prop)

private lemma integral_comp_preserving {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {ν : Measure α} {g : Ω → α} (hg : MeasurePreserving g μ ν)
    {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, f (g x) ∂μ = ∫ y, f y ∂ν := by
  rw [← integral_map hg.measurable.aemeasurable (hg.map_eq ▸ hf.aestronglyMeasurable), hg.map_eq]

private lemma real_inner_eq_dot {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    ⟪u, v⟫ = ∑ i, u.ofLp i * v.ofLp i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

private lemma bilinear_form_approx {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (T : E →L[ℝ] F)
    {u u' : E} {v v' : F} (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) {ε : ℝ}
    (huu : ‖u - u'‖ ≤ ε) (hvv : ‖v - v'‖ ≤ ε) :
    ⟪T u, v⟫ ≤ ⟪T u', v'⟫ + 2 * ε * ‖T‖ := by
  have h₁ : ⟪T (u - u'), v⟫ ≤ ‖T‖ * ε := by
    simpa only [hv, mul_one] using (real_inner_le_norm (T (u - u')) v).trans
      (mul_le_mul_of_nonneg_right ((T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left huu (norm_nonneg _))) (norm_nonneg _))
  have h₂ : ⟪T u', v - v'⟫ ≤ ‖T‖ * ε := by
    have hTu : ‖T u'‖ ≤ ‖T‖ := by simpa [hu'] using T.le_opNorm u'
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul hTu hvv (norm_nonneg _) (norm_nonneg _))
  rw [map_sub, inner_sub_left] at h₁
  rw [inner_sub_right] at h₂
  linarith

private lemma norm_eq_bilinear_of_nonempty {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    [ProperSpace E] [Nontrivial E] [Nontrivial F] (T : E →L[ℝ] F) :
    ∃ u v, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪T u, v⟫ = ‖T‖ := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) T.continuous.norm.continuousOn
  have hu' : ‖u‖ = 1 := by simpa [Metric.mem_sphere] using hu
  have hT : ‖T u‖ = ‖T‖ := le_antisymm (by simpa [hu'] using T.le_opNorm u)
    (ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun w hw => hmax (by
      simpa [Metric.mem_sphere] using hw))
  by_cases h : T u = 0
  · obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : F))).mpr zero_le_one
    refine ⟨u, v, hu', by simpa [Metric.mem_sphere] using hv, ?_⟩
    simp [h, ← hT]
  · have hn : ‖T u‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨u, ‖T u‖⁻¹ • T u, hu', ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hn]
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← hT, pow_two, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

set_option maxHeartbeats 600000 in
-- The net comparison elaborates several nested finite sums over subtype and product indices.
private lemma integral_operatorNorm_le (n d : ℕ) [Nonempty (Fin n)] [Nonempty (Fin d)] :
    (∫ x, operatorNorm x ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) ≤
      Real.sqrt n + Real.sqrt d := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let H := EuclideanSpace ℝ (Fin n)
  let K := Fin n × Fin d
  let J := K ⊕ (Fin n ⊕ Fin d)
  let σ (x : K → ℝ) := operatorNorm (WithLp.toLp 2 x)
  let U (x : J → ℝ) :=
    ‖WithLp.toLp 2 (fun i : Fin n => x (.inr (.inl i)))‖ +
    ‖WithLp.toLp 2 (fun j : Fin d => x (.inr (.inr j)))‖
  have hσ : Integrable σ (gaussianPi K) := by
    refine integrable_pi_norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (lipschitzWith_operatorNorm.continuous.comp (by fun_prop)).aestronglyMeasurable
    · change |‖matrixMap (matrixOf (WithLp.toLp 2 x))‖| ≤ _
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_matrixMap_le _
  have hmK : MeasurePreserving (fun x : J → ℝ => fun i : K => x (.inl i))
      (gaussianPi J) (gaussianPi K) := measurePreserving_inl
  have hmN : MeasurePreserving (fun x : J → ℝ => fun i : Fin n => x (.inr (.inl i)))
      (gaussianPi J) (gaussianPi (Fin n)) :=
    measurePreserving_inl.comp measurePreserving_inr
  have hmD : MeasurePreserving (fun x : J → ℝ => fun i : Fin d => x (.inr (.inr i)))
      (gaussianPi J) (gaussianPi (Fin d)) :=
    measurePreserving_inr.comp measurePreserving_inr
  have hN : Integrable (fun x : J → ℝ =>
      ‖WithLp.toLp 2 (fun i : Fin n => x (.inr (.inl i)))‖) (gaussianPi J) :=
    hmN.integrable_comp_of_integrable integrable_pi_norm
  have hD : Integrable (fun x : J → ℝ =>
      ‖WithLp.toLp 2 (fun j : Fin d => x (.inr (.inr j)))‖) (gaussianPi J) :=
    hmD.integrable_comp_of_integrable integrable_pi_norm
  have hU : Integrable U (gaussianPi J) := hN.add hD
  have hUb : (∫ x, U x ∂gaussianPi J) ≤ Real.sqrt n + Real.sqrt d := by
    dsimp only [U]
    rw [integral_add hN hD]
    rw [integral_comp_preserving hmN integrable_pi_norm,
      integral_comp_preserving hmD integrable_pi_norm]
    exact add_le_add (by simpa using integral_norm_pi_le (ι := Fin n))
      (by simpa using integral_norm_pi_le (ι := Fin d))
  have hmap : (gaussianPi K).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ K) :=
    map_pi_eq_stdGaussian
  rw [← hmap, integral_map (by fun_prop) lipschitzWith_operatorNorm.continuous.aestronglyMeasurable]
  change (∫ x, σ x ∂gaussianPi K) ≤ _
  let s : Set (E × H) := Metric.sphere 0 1 ×ˢ Metric.sphere 0 1
  have hs : IsCompact s := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hsne : s.Nonempty :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).prod (NormedSpace.sphere_nonempty.mpr zero_le_one)
  refine le_of_forall_pos_le_add fun η hη => ?_
  let a := ∫ x, σ x ∂gaussianPi K
  let ε := (η / 2) / (|a| + 1)
  have ha : 0 < |a| + 1 := by positivity
  have hε : 0 < ε := div_pos (half_pos hη) ha
  have hη' : 2 * ε * a ≤ η := by
    have heq : 2 * ε * a = η * (a / (|a| + 1)) := by
      dsimp only [ε]
      ring
    rw [heq]
    apply mul_le_of_le_one_right hη.le
    rw [div_le_one ha]
    linarith [le_abs_self a]
  obtain ⟨t, hts, htfin, hcover⟩ := hs.finite_cover_balls hε
  have hnear (w : E × H) (hw : w ∈ s) : ∃ i : t, dist w i.1 < ε := by
    obtain ⟨i, hit, hd⟩ := by simpa only [Set.mem_iUnion, Metric.mem_ball] using hcover hw
    exact ⟨⟨i, hit⟩, hd⟩
  let : Fintype t := htfin.fintype
  have : Nonempty t := by
    obtain ⟨w, hw⟩ := hsne
    obtain ⟨i, _⟩ := hnear w hw
    exact ⟨i⟩
  have hunit (i : t) : ‖i.1.1‖ = 1 ∧ ‖i.1.2‖ = 1 := by
    simpa [s, Metric.mem_sphere] using hts i.2
  -- The first process is bilinear in the matrix entries. The comparison process
  -- uses two independent Gaussian vectors in the remaining coordinates.
  let A (i : t) : J → ℝ := Sum.elim (fun k => i.1.2.ofLp k.1 * i.1.1.ofLp k.2) (fun _ => 0)
  let B (i : t) : J → ℝ := Sum.elim (fun _ => 0) (Sum.elim i.1.2.ofLp i.1.1.ofLp)
  have hAA (i j : t) : ∑ k, A i k * A j k = ⟪i.1.2, j.1.2⟫ * ⟪i.1.1, j.1.1⟫ := by
    rw [real_inner_eq_dot (ι := Fin n) i.1.2 j.1.2,
      real_inner_eq_dot (ι := Fin d) i.1.1 j.1.1]
    simp only [A, J, K, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero,
      add_zero, Fintype.sum_prod_type]
    rw [sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  have hBB (i j : t) : ∑ k, B i k * B j k = ⟪i.1.2, j.1.2⟫ + ⟪i.1.1, j.1.1⟫ := by
    rw [real_inner_eq_dot (ι := Fin n) i.1.2 j.1.2,
      real_inner_eq_dot (ι := Fin d) i.1.1 j.1.1]
    simp [B, J, Fintype.sum_sum_type]
  have hcmp (i j : t) : ∑ k, A i k * (A i k - A j k) ≤ ∑ k, B i k * (B i k - B j k) := by
    simp only [mul_sub, sum_sub_distrib, hAA, hBB, real_inner_self_eq_norm_sq,
      (hunit i).1, (hunit i).2, one_pow, mul_one]
    have hv : ⟪i.1.2, j.1.2⟫ ≤ 1 := by
      simpa [(hunit i).2, (hunit j).2] using real_inner_le_norm i.1.2 j.1.2
    have hu : ⟪i.1.1, j.1.1⟫ ≤ 1 := by
      simpa [(hunit i).1, (hunit j).1] using real_inner_le_norm i.1.1 j.1.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hu)]
  -- The finite net captures the norm up to twice its radius times the norm.
  let L (x : J → ℝ) := σ (fun i => x (.inl i)) - (2 * ε) * σ (fun i => x (.inl i))
  have hσJ : Integrable (fun x : J → ℝ => σ fun i => x (.inl i)) (gaussianPi J) :=
    hmK.integrable_comp_of_integrable hσ
  have hL : Integrable L (gaussianPi J) := hσJ.sub (hσJ.const_mul _)
  have hlo (x : J → ℝ) : ∃ i, L x ≤ ∑ k, A i k * x k := by
    let M := matrixMap (matrixOf (WithLp.toLp 2 fun i : K => x (.inl i)))
    obtain ⟨u, v, hu, hv, huv⟩ := norm_eq_bilinear_of_nonempty M
    obtain ⟨i, hi⟩ := hnear (u, v) (by simp [s, hu, hv])
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hi
    have h := bilinear_form_approx M (hunit i).1 hv hi.1.le hi.2.le
    rw [huv] at h
    have hAx : ∑ k, A i k * x k = ⟪M i.1.1, i.1.2⟫ := by
      rw [real_inner_eq_dot (ι := Fin n) (M i.1.1) i.1.2]
      simp only [A, J, K, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
        sum_const_zero, add_zero, Fintype.sum_prod_type]
      change (∑ a, ∑ b, i.1.2.ofLp a * i.1.1.ofLp b * x (.inl (a, b))) =
        ∑ a, (∑ b, x (.inl (a, b)) * i.1.1.ofLp b) * i.1.2.ofLp a
      simp_rw [sum_mul]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    refine ⟨i, ?_⟩
    rw [hAx]
    change ‖M‖ - 2 * ε * ‖M‖ ≤ _
    linarith
  have hhi (x : J → ℝ) (i : t) : ∑ k, B i k * x k ≤ U x := by
    have hv := real_inner_le_norm i.1.2 (WithLp.toLp 2 fun k => x (.inr (.inl k)))
    have hu := real_inner_le_norm i.1.1 (WithLp.toLp 2 fun k => x (.inr (.inr k)))
    rw [(hunit i).2, one_mul, real_inner_eq_dot (ι := Fin n)] at hv
    rw [(hunit i).1, one_mul, real_inner_eq_dot (ι := Fin d)] at hu
    simpa [B, J, U, Fintype.sum_sum_type] using add_le_add hv hu
  have hcomparison := integral_le_of_finite_comparison A B
    (fun i j k => by cases k <;> simp [A, B]) hcmp hL hU hlo hhi
  have hLsplit : (∫ x, L x ∂gaussianPi J) =
      (∫ x, σ x ∂gaussianPi K) - 2 * ε * ∫ x, σ x ∂gaussianPi K := by
    dsimp only [L]
    rw [integral_sub hσJ (hσJ.const_mul _), integral_const_mul,
      integral_comp_preserving hmK hσ]
  rw [hLsplit] at hcomparison
  change a - 2 * ε * a ≤ _ at hcomparison
  change a ≤ _
  linarith [hcomparison.trans hUb]

/-! ### Concentration of the operator norm -/

private lemma subGaussian_operatorNorm (n d : ℕ) :
    HasSubgaussianMGF
      (fun x : (Fin n × Fin d) → ℝ =>
        operatorNorm (WithLp.toLp 2 x) -
          ∫ y, operatorNorm y ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))
      1 (gaussianPi (Fin n × Fin d)) := by
  let K := Fin n × Fin d
  let E := EuclideanSpace ℝ K
  let V := EuclideanSpace ℝ (Fin (Fintype.card K))
  let e : V ≃ₗᵢ[ℝ] E :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin K).symm
  have hp : MeasurePreserving e (stdGaussian V) (stdGaussian E) :=
    ⟨e.continuous.measurable, stdGaussian_map e⟩
  have hf : LipschitzWith 1 (operatorNorm ∘ e) := by
    simpa using lipschitzWith_operatorNorm.comp e.isometry.lipschitzWith
  open HighDimensionalStatisticsWanted in
  have hc := (lipschitz_concentration_stdGaussian hf).1
  have hI : (∫ y, (operatorNorm ∘ e) y ∂stdGaussian V) =
      ∫ y, operatorNorm y ∂stdGaussian E :=
    hp.integral_comp e.toHomeomorph.measurableEmbedding _
  rw [hI, one_pow] at hc
  have hE : HasSubgaussianMGF
      (fun x : E => operatorNorm x - ∫ y, operatorNorm y ∂stdGaussian E) 1 (stdGaussian E) := by
    have hp' : MeasurePreserving e.symm (stdGaussian E) (stdGaussian V) :=
      ⟨e.symm.continuous.measurable, stdGaussian_map e.symm⟩
    rw [← hp'.map_eq] at hc
    have hh := hc.of_map hp'.measurable.aemeasurable
    convert hh using 1
    ext x
    change _ = operatorNorm (e (e.symm x)) - _
    rw [e.apply_symm_apply]
  have hm : (gaussianPi K).map (WithLp.toLp 2) = stdGaussian E := map_pi_eq_stdGaussian
  have hE' : HasSubgaussianMGF
      (fun x : E => operatorNorm x - ∫ y, operatorNorm y ∂stdGaussian E)
      1 ((gaussianPi K).map (WithLp.toLp 2)) := by rwa [hm]
  exact hE'.of_map (Y := WithLp.toLp 2) (by fun_prop)

end

/-- **Largest singular value of a standard Gaussian matrix** (Wainwright, *High-Dimensional
Statistics*, 2019, §6.2, with `Σ = I`; Vershynin, arXiv:1011.3027, Theorem 5.32 and
Proposition 5.34): if `X` is an `n × d` matrix with independent
`N(0, 1)` entries and `δ ≥ 0`, then
`P(σ_max(X) ≥ √n (1 + δ) + √d) ≤ exp (-n δ² / 2)`. -/
public theorem measureReal_sigmaMax_ge_le (n d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : Fin n × Fin d => gaussianReal 0 1).real
        {x | ∃ u : Fin d → ℝ, u ≠ 0 ∧
          (Real.sqrt n * (1 + δ) + Real.sqrt d) ^ 2 * ∑ j, u j ^ 2 ≤
            ∑ i, (Matrix.of (fun i j => x (i, j)) *ᵥ u) i ^ 2} ≤
      Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hd : d = 0
  · subst d
    calc
      _ = 0 := by simp
      _ ≤ _ := (Real.exp_pos _).le
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let c := ∫ y, operatorNorm y ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))
  have hc : c ≤ Real.sqrt n + Real.sqrt d := integral_operatorNorm_le n d
  let t := Real.sqrt n * δ
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : Real.exp (-t ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) =
      Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by
    congr 1
    simp [t, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), neg_mul]
  refine le_trans (measureReal_mono (s₂ := {x | t ≤ operatorNorm (WithLp.toLp 2 x) - c}) ?_) ?_
  · rintro x ⟨u, hu, h⟩
    let T := matrixMap (matrixOf (WithLp.toLp 2 x))
    let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 u
    have hv : 0 < ‖v‖ := norm_pos_iff.mpr (by simpa [v] using hu)
    have h₁ : (Real.sqrt n * (1 + δ) + Real.sqrt d) ^ 2 * ‖v‖ ^ 2 ≤ ‖T v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v, EuclideanSpace.real_norm_sq_eq (T v)]
      exact h
    have h₂ : (Real.sqrt n * (1 + δ) + Real.sqrt d) * ‖v‖ ≤ ‖T v‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      rwa [mul_pow]
    have h₃ := le_of_mul_le_mul_right (h₂.trans (T.le_opNorm v)) hv
    change t ≤ ‖T‖ - c
    dsimp only [t]
    linarith
  · rw [← ht']
    exact (subGaussian_operatorNorm n d).measure_ge_le ht

end MathlibExt.Probability.GaussianRandomMatrixWanted
