/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FunctionalInequalities.LogSobolevTalagrand
import MathlibExt.MeasureTheory.OptimalTransport.Existence
import MathlibExt.InformationTheory.DonskerVaradhan
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Otto–Villani theorem

`satisfiesTalagrand_of_satisfiesLogSobolev` derives the quadratic transport inequality with
constant `2 / α` from the logarithmic Sobolev inequality with constant `α > 0`.

For the bounded cost `c(x,y) = min(R, d(x,y))² / 2`, let
`Vₜ(x) = inf_y (t g(y) + c(x,y))`. Near-minimizers of this expression bound the local slope
of `Vₜ` in terms of the time secant from `t` to `u > t`. Applying log-Sobolev to the normalized
density proportional to `exp(α Vₜ)` then gives a right-hand estimate showing that
`log (∫ exp(α Vₜ) dm) / t` is nonincreasing. Together with the entropy variational bound, this
bounds every pair of test functions feasible for the bounded cost.

Finite cubes of capped distances to a dense sequence recover the original distance from below.
Compact Kantorovich duality bounds the cost on each cube, and the gluing lemma lifts the
projected couplings. Compactness of the set of couplings yields one coupling satisfying all the
bounds, so monotone convergence recovers the squared distance.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

open MathlibExt.Probability.LogSobolevTalagrand
open MathlibExt.InformationTheory.DonskerVaradhan (integrable_of_bounded toReal_klDiv_tilted)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
  (wasserstein transportCost_le_of_isCoupling exists_gluing)
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
  (IsCoupling primalValues kantorovich_duality_compact)

namespace MathlibExt.Probability.OttoVillaniWanted

section

variable {X : Type*} [MetricSpace X]

/-! ## Infimum convolution and local slopes -/

private def cappedDist (R : ℝ) (x y : X) : ℝ := min R (dist x y)

private noncomputable def cost (R : ℝ) (x y : X) : ℝ := cappedDist R x y ^ 2 / 2

private noncomputable def envelope (R : ℝ) (g : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  ⨅ y : X, t * g y + cost R x y

private lemma cappedDist_nonneg {R : ℝ} (hR : 0 ≤ R) (x y : X) :
    0 ≤ cappedDist R x y := le_min hR dist_nonneg

private lemma cappedDist_le (R : ℝ) (x y : X) : cappedDist R x y ≤ R := min_le_left ..

private lemma abs_cappedDist_sub_le (R : ℝ) (x y z : X) :
    |cappedDist R x z - cappedDist R y z| ≤ dist x y := by
  refine (abs_min_sub_min_le_max ..).trans (max_le ?_ (abs_dist_sub_le x y z))
  simp

private lemma abs_cost_sub_le {R : ℝ} (hR : 0 ≤ R) (x y z : X) :
    |cost R x z - cost R y z| ≤ dist x y * ((cappedDist R x z + cappedDist R y z) / 2) := by
  rw [show cost R x z - cost R y z =
    (cappedDist R x z - cappedDist R y z) * ((cappedDist R x z + cappedDist R y z) / 2) by
      unfold cost
      ring, abs_mul, abs_of_nonneg (div_nonneg
        (add_nonneg (cappedDist_nonneg hR x z) (cappedDist_nonneg hR y z)) two_pos.le)]
  exact mul_le_mul_of_nonneg_right (abs_cappedDist_sub_le R x y z) (div_nonneg
    (add_nonneg (cappedDist_nonneg hR x z) (cappedDist_nonneg hR y z)) two_pos.le)

private lemma abs_cost_sub_le_mul {R : ℝ} (hR : 0 ≤ R) (x y z : X) :
    |cost R x z - cost R y z| ≤ R * dist x y := by
  rw [mul_comm]
  refine (abs_cost_sub_le hR x y z).trans ?_
  gcongr
  linarith [cappedDist_le R x z, cappedDist_le R y z]

private lemma envelope_bddBelow (R : ℝ) {g : X → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M)
    (t : ℝ) (x : X) : BddBelow (range (fun y => t * g y + cost R x y)) := by
  refine ⟨-(|t| * M), ?_⟩
  rintro _ ⟨y, rfl⟩
  have h : -(|t| * M) ≤ t * g y := by
    rw [← neg_le_neg_iff, neg_neg]
    calc -(t * g y) ≤ |t * g y| := neg_le_abs _
      _ ≤ |t| * M := by rw [abs_mul]; gcongr; exact hg y
  exact h.trans (le_add_of_nonneg_right (by unfold cost; positivity))

private lemma envelope_le (R : ℝ) {g : X → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M)
    (t : ℝ) (x y : X) : envelope R g t x ≤ t * g y + cost R x y :=
  ciInf_le (envelope_bddBelow R hg t x) y

private lemma envelope_compare {ι : Type*}
    [Nonempty ι] {a b : ι → ℝ} (ha : BddBelow (range a))
    {C : ℝ} (h : ∀ x, a x ≤ b x + C) : (⨅ x, a x) ≤ (⨅ x, b x) + C := by
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  exact sub_le_iff_le_add.mpr ((ciInf_le ha x).trans (h x))

private lemma lipschitzWith_envelope {R : ℝ} (hR : 0 ≤ R) {g : X → ℝ} {M : ℝ}
    (hg : ∀ x, |g x| ≤ M) (t : ℝ) :
    LipschitzWith ⟨R, hR⟩ (envelope R g t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let : Nonempty X := ⟨x⟩
  change |envelope R g t x - envelope R g t y| ≤ R * dist x y
  rw [abs_sub_le_iff]
  have h (a b : X) :
      envelope R g t a - envelope R g t b ≤ R * dist a b := by
    rw [sub_le_iff_le_add']
    apply envelope_compare (envelope_bddBelow R hg t a)
    intro z
    have hz := (le_abs_self _).trans (abs_cost_sub_le_mul hR a b z)
    linarith
  refine ⟨h x y, ?_⟩
  simpa only [dist_comm y x] using h y x

private lemma lipschitzWith_envelope_time (R : ℝ) {g : X → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ x, |g x| ≤ M) (x : X) :
    LipschitzWith ⟨M, hM⟩ (fun t => envelope R g t x) := by
  let : Nonempty X := ⟨x⟩
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |envelope R g s x - envelope R g t x| ≤ M * |s - t|
  rw [abs_sub_le_iff]
  have h (a b : ℝ) :
      envelope R g a x - envelope R g b x ≤ M * |a - b| := by
    rw [sub_le_iff_le_add']
    apply envelope_compare (envelope_bddBelow R hg a x)
    intro z
    have hz : (a - b) * g z ≤ M * |a - b| := calc
      _ ≤ |(a - b) * g z| := le_abs_self _
      _ ≤ _ := by rw [abs_mul, mul_comm M]; gcongr; exact hg z
    linarith
  refine ⟨h s t, ?_⟩
  simpa only [abs_sub_comm t s] using h t s

private lemma envelope_zero {R : ℝ} (hR : 0 ≤ R) {g : X → ℝ} {M : ℝ}
    (hg : ∀ x, |g x| ≤ M) (x : X) : envelope R g 0 x = 0 := by
  let : Nonempty X := ⟨x⟩
  refine le_antisymm ((envelope_le R hg 0 x x).trans_eq ?_) (le_ciInf fun y => ?_)
  · simp [cost, cappedDist, min_eq_right hR]
  · simp only [zero_mul, zero_add, cost]
    positivity

private lemma envelope_abs_le {R : ℝ} (hR : 0 ≤ R) {g : X → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ x, |g x| ≤ M) (t : ℝ) (x : X) :
    |envelope R g t x| ≤ M * |t| := by
  have h := (lipschitzWith_envelope_time R hM hg x).dist_le_mul t 0
  rwa [Real.dist_eq, envelope_zero hR hg, sub_zero, Real.dist_eq, sub_zero] at h

private lemma exists_envelope_lt (R : ℝ) (g : X → ℝ) (t : ℝ) (x : X) {ε : ℝ}
    (hε : 0 < ε) : ∃ y, t * g y + cost R x y < envelope R g t x + ε :=
  let : Nonempty X := ⟨x⟩
  exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hε)

private noncomputable def envelopeSubMulSecant (R : ℝ) (g : X → ℝ) (t u : ℝ) (x : X) : ℝ :=
  envelope R g t x - t * ((envelope R g u x - envelope R g t x) / (u - t))

private lemma cost_le_envelopeSubMulSecant {R : ℝ} {g : X → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M)
    {t u : ℝ} (ht : 0 ≤ t) (htu : t < u) (x z : X) {δ : ℝ}
    (hz : t * g z + cost R x z ≤ envelope R g t x + δ) :
    cost R x z ≤ envelopeSubMulSecant R g t u x + (u / (u - t)) * δ := by
  have h := envelope_le R hg u x z
  have hd : 0 < u - t := sub_pos.mpr htu
  apply le_of_mul_le_mul_right _ hd
  have heq : (envelopeSubMulSecant R g t u x + u / (u - t) * δ) * (u - t) =
      u * envelope R g t x - t * envelope R g u x + u * δ := by
    unfold envelopeSubMulSecant
    field_simp
    ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left h ht, mul_le_mul_of_nonneg_left hz (ht.trans htu.le)]

private lemma envelopeSubMulSecant_nonneg {R : ℝ} {g : X → ℝ} {M : ℝ}
    (hg : ∀ x, |g x| ≤ M) {t u : ℝ}
    (ht : 0 ≤ t) (htu : t < u) (x : X) :
    0 ≤ envelopeSubMulSecant R g t u x := by
  have hcoef : 0 < u / (u - t) := div_pos (ht.trans_lt htu) (sub_pos.mpr htu)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨z, hz⟩ := exists_envelope_lt R g t x (div_pos hε hcoef)
  have h := cost_le_envelopeSubMulSecant hg ht htu x z hz.le
  rw [mul_div_cancel₀ _ hcoef.ne'] at h
  exact (show 0 ≤ cost R x z by unfold cost; positivity).trans h

private lemma envelope_abs_sub_le {R : ℝ} (hR : 0 ≤ R)
    {g : X → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) {t u : ℝ}
    (ht : 0 ≤ t) (htu : t < u) (x y : X) :
    |envelope R g t y - envelope R g t x| ≤
      dist y x * (sqrt (2 * (envelopeSubMulSecant R g t u x +
        u / (u - t) * (2 * R * dist y x + dist y x ^ 2))) + 3 * dist y x / 2) := by
  by_cases hy : y = x
  · subst y
    simp
  let d := dist y x
  let B := envelopeSubMulSecant R g t u x + u / (u - t) * (2 * R * d + d ^ 2)
  have hd : 0 ≤ d := dist_nonneg
  have hR' : 0 ≤ 2 * R * d := by positivity
  -- A near-minimizer at either point is also a near-minimizer at `x`.
  have hlim (z : X)
      (hz : t * g z + cost R x z ≤ envelope R g t x + (2 * R * d + d ^ 2)) :
      |cost R y z - cost R x z| ≤ d * (sqrt (2 * B) + d / 2) := by
    have hcost : cost R x z ≤ B := cost_le_envelopeSubMulSecant hg ht htu x z hz
    have hdist : cappedDist R x z ≤ sqrt (2 * B) := by
      apply Real.le_sqrt_of_sq_le
      unfold cost at hcost
      linarith
    have hdist' : cappedDist R y z ≤ cappedDist R x z + d := by
      have := (le_abs_self _).trans (abs_cappedDist_sub_le R y x z)
      linarith
    refine (abs_cost_sub_le hR y x z).trans (mul_le_mul_of_nonneg_left ?_ hd)
    linarith
  have hlip : |envelope R g t y - envelope R g t x| ≤ R * d :=
    (lipschitzWith_envelope hR hg t).dist_le_mul y x
  have hd2 : 0 < d ^ 2 := pow_pos (dist_pos.mpr hy) 2
  obtain ⟨z, hz⟩ := exists_envelope_lt R g t x hd2
  obtain ⟨w, hw⟩ := exists_envelope_lt R g t y hd2
  have hz' := hlim z (by linarith [hz])
  have hw' := hlim w (by
    have h1 := (neg_le_abs _).trans (abs_cost_sub_le_mul hR y x w)
    have h2 := (le_abs_self _).trans hlip
    linarith [hw])
  change _ ≤ d * (sqrt (2 * B) + 3 * d / 2)
  rw [abs_sub_le_iff]
  constructor
  · have h := envelope_le R hg t y z
    linarith [le_abs_self (cost R y z - cost R x z)]
  · have h := envelope_le R hg t x w
    linarith [neg_le_abs (cost R y w - cost R x w)]

private lemma localLipschitzConstant_le_of_tendsto {f B : X → ℝ} {x : X} {b : ℝ}
    (hB : Tendsto B (𝓝[≠] x) (𝓝 b)) (h : ∀ᶠ y in 𝓝[≠] x, |f y - f x| / dist y x ≤ B y) :
    localLipschitzConstant f x ≤ ENNReal.ofReal b := by
  unfold localLipschitzConstant
  by_cases hex : NeBot (𝓝[≠] x)
  · let := hex
    rw [← (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hB).limsup_eq]
    exact limsup_le_limsup (h.mono fun _ hy => ENNReal.ofReal_le_ofReal hy)
      (by isBoundedDefault) (by isBoundedDefault)
  · rw [not_neBot] at hex
    rw [hex, limsup_bot]
    exact bot_le

private lemma lipschitzOnWith_exp (C : ℝ) :
    LipschitzOnWith ⟨exp C, (exp_pos C).le⟩ exp (Iic C) := by
  apply (convex_Iic C).lipschitzOnWith_of_nnNorm_deriv_le
  · exact fun x _ => (hasDerivAt_exp x).differentiableAt
  · intro x hx
    rw [(hasDerivAt_exp x).deriv]
    apply NNReal.coe_le_coe.mp
    change ‖exp x‖ ≤ exp C
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos x)]
    exact exp_le_exp.mpr hx

private lemma exp_slope_bound {v G : X → ℝ} {K : ℝ≥0} (hv : LipschitzWith K v)
    {x : X} {b α Z : ℝ} (hα : 0 < α) (hZ : 0 < Z)
    (hG : Tendsto G (𝓝[≠] x) (𝓝 b))
    (hvG : ∀ y, |v y - v x| ≤ dist y x * G y) :
    localLipschitzConstant (fun y => exp (α * v y) / Z) x ≤
      ENNReal.ofReal (exp (α * v x) / Z * α * b) := by
  let C : X → ℝ := fun y => exp (max (α * v y) (α * v x)) / Z
  have hC : Tendsto C (𝓝[≠] x) (𝓝 (exp (α * v x) / Z)) := by
    have h : Continuous C := by
      dsimp [C]
      exact (continuous_exp.comp ((continuous_const.mul hv.continuous).max
        continuous_const)).div_const Z
    simpa only [C, max_self] using (h.continuousWithinAt (s := {x}ᶜ) (x := x)).tendsto
  apply localLipschitzConstant_le_of_tendsto (B := fun y => C y * α * G y)
    ((hC.mul tendsto_const_nhds).mul hG)
  filter_upwards [eventually_mem_nhdsWithin] with y (hy : y ≠ x)
  have h := (lipschitzOnWith_exp (max (α * v y) (α * v x))).dist_le_mul
    (x := α * v y) (y := α * v x) (mem_Iic.mpr (le_max_left _ _)) (mem_Iic.mpr (le_max_right _ _))
  simp only [Real.dist_eq] at h
  rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ (dist_pos.mpr hy), div_le_iff₀ hZ]
  rw [← mul_sub, abs_mul, abs_of_pos hα] at h
  calc
    _ ≤ exp (max (α * v y) (α * v x)) * (α * |v y - v x|) := h
    _ ≤ exp (max (α * v y) (α * v x)) * (α * (dist y x * G y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hvG y) hα.le) (exp_pos _).le
    _ = _ := by dsimp [C]; field_simp

private lemma envelope_exp_slope {R : ℝ} (hR : 0 ≤ R)
    {g : X → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) {t u α Z : ℝ}
    (ht : 0 ≤ t) (htu : t < u) (hα : 0 < α) (hZ : 0 < Z) (x : X) :
    localLipschitzConstant (fun y => exp (α * envelope R g t y) / Z) x ≤
      ENNReal.ofReal (exp (α * envelope R g t x) / Z * α *
        sqrt (2 * envelopeSubMulSecant R g t u x)) := by
  let G : ℝ → ℝ := fun d =>
    sqrt (2 * (envelopeSubMulSecant R g t u x + u / (u - t) * (2 * R * d + d ^ 2))) + 3 * d / 2
  refine exp_slope_bound (lipschitzWith_envelope hR hg t) hα hZ (G := fun y => G (dist y x)) ?_
    (envelope_abs_sub_le hR hg ht htu x)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hd : Tendsto (fun y => dist y x) (𝓝[≠] x) (𝓝 0) := by
    have hdist : Continuous (fun y : X => dist y x) := continuous_id.dist continuous_const
    simpa only [dist_self] using (hdist.continuousWithinAt
      (s := ({x}ᶜ : Set X)) (x := x)).tendsto
  simpa [G, Function.comp_def] using (hG.continuousAt (x := 0)).tendsto.comp hd

/-! ## The exponential integral estimate -/

section LogSobolev

variable [MeasurableSpace X] [BorelSpace X]
  {R : ℝ} (hR : 0 ≤ R) {g : X → ℝ} {M : ℝ} (hM : 0 ≤ M)
  (hg : ∀ x, |g x| ≤ M) (hgc : Continuous g)
  (m : Measure X) [IsProbabilityMeasure m] {α : ℝ} (hα : 0 < α)
  (hm : SatisfiesLogSobolev m α)

private noncomputable def logMoment (m : Measure X) (α R : ℝ) (g : X → ℝ) (t : ℝ) : ℝ :=
  log (∫ x, exp (α * envelope R g t x) ∂m)

omit [MeasurableSpace X] [BorelSpace X] in
include hR hM hg hα in
private lemma envelope_scaled_bound (t : ℝ) (x : X) :
    |α * envelope R g t x| ≤ α * (M * |t|) := by
  rw [abs_mul, abs_of_pos hα]
  exact mul_le_mul_of_nonneg_left (envelope_abs_le hR hM hg t x) hα.le

include hR hM hg hα hm in
private lemma secant_integral_le {t u : ℝ} (ht : 0 < t) (htu : t < u) :
    α * t * (∫ x, (envelope R g u x - envelope R g t x) / (u - t)
      ∂(m.tilted fun x => α * envelope R g t x)) ≤ logMoment m α R g t := by
  let v := envelope R g t
  let w := envelope R g u
  let p : X → ℝ := fun x => α * v x
  let Z := ∫ x, exp (p x) ∂m
  let f : X → ℝ := fun x => exp (p x) / Z
  let ν := m.tilted p
  let s : X → ℝ := fun x => (w x - v x) / (u - t)
  let C := envelopeSubMulSecant R g t u
  have hv := (lipschitzWith_envelope hR hg t).continuous
  have hw := (lipschitzWith_envelope hR hg u).continuous
  have hp : Continuous p := continuous_const.mul hv
  have hpb : ∀ x, |p x| ≤ α * (M * |t|) := envelope_scaled_bound hR hM hg hα t
  have hexp := (integrable_of_bounded (μ := m) hp.measurable hpb).2
  have hZ : 0 < Z := integral_exp_pos hexp
  have hfpos (x : X) : 0 < f x := div_pos (exp_pos _) hZ
  have hfint : (∫ x, f x ∂m) = 1 := by
    dsimp [f]
    rw [integral_div, div_self hZ.ne']
  have hfL : ∃ L, LipschitzWith L f := by
    let B := α * (M * |t|)
    refine ⟨⟨exp B * α * R / Z, by positivity⟩, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have h := (lipschitzOnWith_exp B).dist_le_mul
      (x := p x) (y := p y)
      (mem_Iic.mpr ((le_abs_self _).trans (hpb x)))
      (mem_Iic.mpr ((le_abs_self _).trans (hpb y)))
    change |exp (p x) - exp (p y)| ≤ exp B * |p x - p y| at h
    change |exp (p x) / Z - exp (p y) / Z| ≤ exp B * α * R / Z * dist x y
    rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    dsimp [p] at h
    rw [← mul_sub, abs_mul, abs_of_pos hα] at h
    have hl : |v x - v y| ≤ R * dist x y := (lipschitzWith_envelope hR hg t).dist_le_mul x y
    calc
      _ ≤ exp B * (α * |v x - v y|) := h
      _ ≤ exp B * (α * (R * dist x y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hα.le) (exp_pos B).le
      _ = _ := by field_simp
  have hLS := hm f hfL (fun x => (hfpos x).le) hfint
  have hC (x : X) : 0 ≤ C x := envelopeSubMulSecant_nonneg hg ht.le htu x
  have hpt (x : X) : localLipschitzConstant f x ^ 2 / ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (2 * α ^ 2 * C x * f x) := by
    calc
      _ ≤ (ENNReal.ofReal (f x * α * sqrt (2 * C x))) ^ 2 / ENNReal.ofReal (f x) := by
        gcongr
        exact envelope_exp_slope hR hg ht.le htu hα hZ x
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity [hfpos x]), ← ENNReal.ofReal_div_of_pos (hfpos x)]
        congr 1
        have h : (sqrt (2 * C x)) ^ 2 = 2 * C x := sq_sqrt (by positivity [hC x])
        field_simp
        rw [h]
        ring
  have hcontC : Continuous C := hv.sub (continuous_const.mul ((hw.sub hv).div_const _))
  have hsb (x : X) : |s x| ≤ M := by
    have h : |w x - v x| ≤ M * |u - t| :=
      (lipschitzWith_envelope_time R hM hg x).dist_le_mul u t
    dsimp [s]
    rw [abs_div, div_le_iff₀ (abs_pos.mpr (sub_pos.mpr htu).ne')]
    exact h
  have hCb (x : X) : |C x| ≤ M * |t| + t * M := by
    change |v x - t * s x| ≤ _
    calc
      _ ≤ |v x| + |t * s x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have hts : |t| * |s x| ≤ t * M := by
          rw [abs_of_pos ht]
          exact mul_le_mul_of_nonneg_left (hsb x) ht.le
        exact add_le_add (envelope_abs_le hR hM hg t x)
          hts
  have hfb (x : X) : |f x| ≤ exp (α * (M * |t|)) / Z := by
    change |exp (p x) / Z| ≤ _
    rw [abs_of_pos (hfpos x)]
    exact div_le_div_of_nonneg_right (exp_le_exp.mpr ((le_abs_self _).trans (hpb x))) hZ.le
  have hcf : Integrable (fun x => 2 * α ^ 2 * C x * f x) m :=
    (integrable_of_bounded ((continuous_const.mul hcontC).mul
      ((continuous_exp.comp hp).div_const Z)).measurable
        (fun x => by
          change |2 * α ^ 2 * C x * f x| ≤
            2 * α ^ 2 * (M * |t| + t * M) * (exp (α * (M * |t|)) / Z)
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * α ^ 2)]
          gcongr
          · exact hCb x
          · exact hfb x)).1
  have hscaled : ENNReal.ofReal (2 * α) * klDiv ν m ≤
      ENNReal.ofReal (∫ x, 2 * α ^ 2 * C x * f x ∂m) := by
    change ENNReal.ofReal (2 * α) * klDiv (m.withDensity fun x => ENNReal.ofReal (f x)) m ≤ _
    rw [ofReal_integral_eq_lintegral_ofReal hcf
      (ae_of_all _ fun x => by positivity [hfpos x, hC x])]
    exact hLS.trans ((lintegral_mono hpt).trans (lintegral_mono' Measure.restrict_le_self le_rfl))
  have hG := toReal_klDiv_tilted (ν := m) hp.measurable hpb
  have hreal := ENNReal.toReal_mono (by simp) hscaled
  have hnonneg : 0 ≤ ∫ x, 2 * α ^ 2 * C x * f x ∂m :=
    integral_nonneg (fun x => by positivity [hfpos x, hC x])
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hG.2,
    ENNReal.toReal_ofReal hnonneg] at hreal
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hexp
  have hvν : Integrable v ν := (integrable_of_bounded hv.measurable
    (envelope_abs_le hR hM hg t)).1
  have hsν : Integrable s ν := (integrable_of_bounded
    ((hw.sub hv).div_const _).measurable hsb).1
  have hcalc : (∫ x, 2 * α ^ 2 * C x * f x ∂m) = 2 * α ^ 2 * ∫ x, C x ∂ν := by
    change _ = _ * ∫ x, C x ∂(m.tilted p)
    rw [integral_tilted, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by change _ = _ * (f x * C x); ring
  have hsplit : (∫ x, C x ∂ν) = (∫ x, v x ∂ν) - t * ∫ x, s x ∂ν := by
    change (∫ x, v x - t * s x ∂ν) = _
    rw [integral_sub hvν (hsν.const_mul _), integral_const_mul]
  rw [hcalc, hsplit] at hreal
  change (2 * α) * ((∫ x, α * v x ∂ν) - log Z) ≤ _ at hreal
  rw [integral_const_mul] at hreal
  change α * t * (∫ x, s x ∂ν) ≤ log Z
  apply le_of_mul_le_mul_left _ (show 0 < 2 * α by positivity)
  linarith

include hR hM hg hα in
private lemma integral_exp_envelope_pos (t : ℝ) :
    0 < ∫ x, exp (α * envelope R g t x) ∂m := by
  have hp : Continuous (fun x => α * envelope R g t x) :=
    continuous_const.mul (lipschitzWith_envelope hR hg t).continuous
  exact integral_exp_pos
    (integrable_of_bounded hp.measurable (envelope_scaled_bound hR hM hg hα t)).2

include hR hM hg hα in
private lemma continuous_logMoment : Continuous (logMoment m α R g) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  refine (continuousAt_log (integral_exp_envelope_pos hR hM hg m hα t).ne').comp
    (f := fun s => ∫ x, exp (α * envelope R g s x) ∂m) ?_
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => exp (α * (M * (|t| + 1))))
  · exact Eventually.of_forall fun s => (continuous_exp.comp
      (continuous_const.mul (lipschitzWith_envelope hR hg s).continuous)).aestronglyMeasurable
  · have h : ∀ᶠ s in 𝓝 t, |s| < |t| + 1 :=
      continuous_abs.continuousAt.tendsto.eventually_lt_const (lt_add_one _)
    filter_upwards [h] with s hs
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      exact ((le_abs_self _).trans (envelope_scaled_bound hR hM hg hα s x)).trans
        (by gcongr)
  · exact integrable_const _
  · exact ae_of_all _ (fun x => (continuous_exp.comp
      (continuous_const.mul (lipschitzWith_envelope_time R hM hg x).continuous)).continuousAt)

include hR hM hg hα hm in
private lemma logMoment_div_le {t u : ℝ} (ht : 0 < t) (htu : t < u)
    (hs : α * M * (u - t) ≤ 1) :
    logMoment m α R g u / u ≤ logMoment m α R g t / t + (α * M * (u - t)) ^ 2 / u := by
  let p (s : ℝ) (x : X) := α * envelope R g s x
  let Δ : X → ℝ := fun x => p u x - p t x
  let ν := m.tilted (p t)
  let A := α * M * (u - t)
  have hp (s : ℝ) : Continuous (p s) :=
    continuous_const.mul (lipschitzWith_envelope hR hg s).continuous
  have hΔ : Continuous Δ := (hp u).sub (hp t)
  have hΔabs (x : X) : |Δ x| ≤ A := by
    have h : |envelope R g u x - envelope R g t x| ≤ M * |u - t| :=
      (lipschitzWith_envelope_time R hM hg x).dist_le_mul u t
    rw [abs_of_pos (sub_pos.mpr htu)] at h
    dsimp [Δ, p, A]
    rw [← mul_sub, abs_mul, abs_of_pos hα, mul_assoc]
    gcongr
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted
    (integrable_of_bounded (hp t).measurable (envelope_scaled_bound hR hM hg hα t)).2
  have hi := integrable_of_bounded (μ := ν) hΔ.measurable hΔabs
  have hexp :
      (∫ x, exp (Δ x) ∂ν) ≤ 1 + (∫ x, Δ x ∂ν) + A ^ 2 := by
    calc
      _ ≤ ∫ x, 1 + Δ x + A ^ 2 ∂ν := by
        apply integral_mono hi.2 (((integrable_const _).add hi.1).add (integrable_const _))
        intro x
        have h := (le_abs_self _).trans (abs_exp_sub_one_sub_id_le ((hΔabs x).trans hs))
        have hsq : (Δ x) ^ 2 ≤ A ^ 2 := by
          rw [← sq_abs (Δ x)]
          gcongr
          exact hΔabs x
        change exp (Δ x) ≤ 1 + Δ x + A ^ 2
        linarith
      _ = _ := by
        rw [integral_add (f := fun x => 1 + Δ x) (g := fun _ => A ^ 2)
          ((integrable_const _).add hi.1) (integrable_const _),
          integral_add (f := fun _ => 1) (integrable_const _) hi.1]
        simp
  have hratio :
      (∫ x, exp (Δ x) ∂ν) = (∫ x, exp (p u x) ∂m) / (∫ x, exp (p t x) ∂m) := by
    rw [integral_exp_tilted]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [Δ, add_sub_cancel]
  have hlog := (log_le_sub_one_of_pos (integral_exp_pos hi.2)).trans
    (sub_le_sub_right hexp 1)
  rw [hratio, log_div (integral_exp_envelope_pos hR hM hg m hα u).ne'
    (integral_exp_envelope_pos hR hM hg m hα t).ne'] at hlog
  change logMoment m α R g u - logMoment m α R g t ≤ _ at hlog
  have hδ (x : X) : Δ x =
      α * (u - t) * ((envelope R g u x - envelope R g t x) / (u - t)) := by
    dsimp [Δ, p]
    field_simp [(sub_pos.mpr htu).ne']
  simp_rw [hδ, integral_const_mul] at hlog
  have hsecant := secant_integral_le hR hM hg m hα hm ht htu
  have htu' : 0 < u := ht.trans htu
  apply (div_le_iff₀ htu').mpr
  have heq : (logMoment m α R g t / t + A ^ 2 / u) * u =
      logMoment m α R g t +
        (u - t) / t * logMoment m α R g t + A ^ 2 := by
    field_simp
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hsecant (div_nonneg (sub_pos.mpr htu).le ht.le)
  have hh' : (u - t) / t * (α * t) = α * (u - t) := by field_simp
  rw [← mul_assoc, hh'] at hh
  exact by linarith


private lemma antitoneOn_of_eventually_le {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0))
    (h : ∀ t > 0, ∀ ε > 0, ∀ᶠ u in 𝓝[>] t, F u ≤ F t + ε * (u - t)) :
    AntitoneOn F (Ioi 0) := by
  intro a ha b hb hab
  by_contra! hlt
  have hab' : a < b := hab.lt_of_ne (by rintro rfl; exact (lt_irrefl _ hlt))
  let ε := (F b - F a) / (2 * (b - a))
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (by positivity [sub_pos.mpr hab'])
  let G : ℝ → ℝ := fun t => F t - ε * t
  have hGab : G a < G b := by
    have hEq : ε * (b - a) = (F b - F a) / 2 := by
      dsimp [ε]
      field_simp [(sub_pos.mpr hab').ne']
    dsimp [G]
    linarith
  have hsub : Icc a b ⊆ Ioi 0 := fun _ hx => mem_Ioi.mpr ((mem_Ioi.mp ha).trans_le hx.1)
  obtain ⟨t, ht, htmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    ((hF.mono hsub).sub (continuousOn_const.mul continuousOn_id) :
      ContinuousOn G (Icc a b))
  have htb : t < b := ht.2.lt_of_ne (fun heq =>
    hGab.not_ge (heq ▸ (isMinOn_iff.mp htmin) a (left_mem_Icc.mpr hab)))
  have htu : ∀ᶠ u in 𝓝[>] t, u < b :=
    nhdsWithin_le_nhds (Iio_mem_nhds htb)
  have he : ∀ᶠ u in 𝓝[>] t, u ∈ Ioi t ∧ u < b ∧ F u ≤ F t + (ε / 2) * (u - t) :=
    (eventually_mem_nhdsWithin : ∀ᶠ u in 𝓝[>] t, u ∈ Ioi t).and
      (htu.and (h t (ha.trans_le ht.1) (ε / 2) (by positivity)))
  obtain ⟨u, hu, hbu, huu⟩ := he.exists
  have htu' : t < u := hu
  have hmin := (isMinOn_iff.mp htmin) u ⟨ht.1.trans htu'.le, hbu.le⟩
  change F t - ε * t ≤ F u - ε * u at hmin
  linarith [mul_pos hε (sub_pos.mpr htu')]

include hR hM hg hα hm in
private lemma antitoneOn_logMoment_div :
    AntitoneOn (fun t => logMoment m α R g t / t) (Ioi 0) := by
  apply antitoneOn_of_eventually_le
  · exact (continuous_logMoment hR hM hg m hα).continuousOn.div continuousOn_id
      (fun t ht => (mem_Ioi.mp ht).ne')
  · intro t ht ε hε
    have hsmall : ∀ᶠ u in 𝓝[>] t, α * M * (u - t) < 1 := by
      apply nhdsWithin_le_nhds
      have hcont : Continuous (fun u => α * M * (u - t)) := by fun_prop
      exact hcont.continuousAt.tendsto.eventually_lt_const (by simp)
    have herr : ∀ᶠ u in 𝓝[>] t, (α * M) ^ 2 * (u - t) / u < ε := by
      apply nhdsWithin_le_nhds
      have hcont : ContinuousAt (fun u => (α * M) ^ 2 * (u - t) / u) t :=
        (by fun_prop : ContinuousAt (fun u => (α * M) ^ 2 * (u - t)) t).div
          continuousAt_id ht.ne'
      exact hcont.tendsto.eventually_lt_const (by simpa using hε)
    filter_upwards [eventually_mem_nhdsWithin, hsmall, herr] with u (htu : t < u) hs he
    refine (logMoment_div_le hR hM hg m hα hm ht htu hs.le).trans ?_
    have hh := mul_le_mul_of_nonneg_right he.le (sub_pos.mpr htu).le
    rw [← mul_div_right_comm] at hh
    have heq : (α * M) ^ 2 * (u - t) * (u - t) = (α * M * (u - t)) ^ 2 := by ring
    rw [heq] at hh
    exact add_le_add_right hh _

open ProbabilityTheory in
include hR hM hg hgc hα hm in
private lemma logMoment_one_le :
    logMoment m α R g 1 ≤ α * ∫ x, g x ∂m := by
  let p : X → ℝ := fun x => α * g x
  have hp_int : ∀ t : ℝ, Integrable (fun x => exp (t * p x)) m := by
    intro t
    refine (integrable_of_bounded (μ := m) (continuous_const.mul
      (continuous_const.mul hgc)).measurable (C := |t| * (α * M)) ?_).2
    intro x
    change |t * (α * g x)| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos hα]
    gcongr
    exact hg x
  have h0 : 0 ∈ interior (integrableExpSet p m) := by
    have heq : integrableExpSet p m = univ := Set.eq_univ_of_forall hp_int
    simp [heq]
  have hderiv : HasDerivAt (cgf p m) (∫ x, p x ∂m) 0 := by
    have h := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    simpa [deriv_cgf_zero h0] using h
  change logMoment m α R g 1 ≤ α * ∫ x, g x ∂m
  rw [← integral_const_mul]
  refine ge_of_tendsto hderiv.tendsto_slope_zero_right ?_
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [eventually_mem_nhdsWithin, hne] with t (ht : 0 < t) h1
  have hanti := antitoneOn_logMoment_div hR hM hg m hα hm
    (mem_Ioi.mpr ht) (mem_Ioi.mpr zero_lt_one) h1.le
  change logMoment m α R g 1 / 1 ≤ logMoment m α R g t / t at hanti
  rw [div_one] at hanti
  change logMoment m α R g 1 ≤ t⁻¹ * (cgf p m (0 + t) - cgf p m 0)
  rw [zero_add, cgf_zero, sub_zero, ← div_eq_inv_mul]
  refine hanti.trans ((div_le_div_iff_of_pos_right ht).mpr ?_)
  unfold logMoment cgf mgf
  apply log_le_log (integral_exp_envelope_pos hR hM hg m hα t)
  refine integral_mono (integrable_of_bounded (μ := m) ?_ (envelope_scaled_bound hR hM hg hα t)).2
    (hp_int t) ?_
  · exact (continuous_const.mul (lipschitzWith_envelope hR hg t).continuous).measurable
  · intro x
    have h := envelope_le R hg t x x
    have hcx : cost R x x = 0 := by simp [cost, cappedDist, min_eq_right hR]
    rw [hcx, add_zero] at h
    apply exp_le_exp.mpr
    change α * envelope R g t x ≤ t * (α * g x)
    linarith [mul_le_mul_of_nonneg_left h hα.le]

end LogSobolev

/-! ## Transport bounds on compact projections -/

section Projection

variable [MeasurableSpace X] [BorelSpace X]
  {m μ : ProbabilityMeasure X} {α : ℝ}

private lemma dual_bound {R : ℝ} (hR : 0 ≤ R) (hα : 0 < α)
    (hm : SatisfiesLogSobolev (m : Measure X) α)
    (hKL : klDiv (μ : Measure X) (m : Measure X) ≠ ⊤)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    {A B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B)
    (hfg : ∀ x y, f x - g y ≤ cost R x y) :
    (∫ x, f x ∂(μ : Measure X)) - (∫ y, g y ∂(m : Measure X)) ≤
      (klDiv (μ : Measure X) (m : Measure X)).toReal / α := by
  let p : X → ℝ := fun x => α * f x
  have hp : Measurable p := (continuous_const.mul hf).measurable
  have hpB (x : X) : |p x| ≤ α * A := by
    dsimp [p]
    rw [abs_mul, abs_of_pos hα]
    exact mul_le_mul_of_nonneg_left (hfB x) hα.le
  have hpint := (integrable_of_bounded (μ := (m : Measure X)) hp hpB).2
  have hvar :=
    MathlibExt.InformationTheory.DonskerVaradhan.integral_sub_log_integral_exp_le_toReal_klDiv
      hKL hp hpB
  have hle : log (∫ x, exp (p x) ∂(m : Measure X)) ≤
      logMoment (m : Measure X) α R g 1 := by
    apply log_le_log (integral_exp_pos hpint)
    apply integral_mono hpint
      (integrable_of_bounded ((continuous_const.mul
        (lipschitzWith_envelope hR hgB 1).continuous).measurable)
          (envelope_scaled_bound hR hB hgB hα 1)).2
    intro x
    apply exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hα.le)
    let : Nonempty X := ⟨x⟩
    apply le_ciInf
    intro y
    simpa only [one_mul] using sub_le_iff_le_add'.mp (hfg x y)
  have hmoment := logMoment_one_le hR hB hgB hg (m : Measure X) hα hm
  change (∫ x, α * f x ∂(μ : Measure X)) -
    log (∫ x, exp (p x) ∂(m : Measure X)) ≤ _ at hvar
  rw [integral_const_mul] at hvar
  apply (le_div_iff₀ hα).mpr
  linarith


open MathlibExt.MeasureTheory.OptimalTransport.Existence
  (exists_isCoupling_forall_lintegral_le)

private lemma exists_compact_projection_coupling {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {F : X → Y} (hF : LipschitzWith 1 F)
    {R : ℝ} (hR : 0 ≤ R) (hdiam : ∀ x y : Y, dist x y ≤ R)
    (hα : 0 < α) (hm : SatisfiesLogSobolev (m : Measure X) α)
    (hKL : klDiv (μ : Measure X) (m : Measure X) ≠ ⊤) :
    ∃ γ : ProbabilityMeasure (Y × Y), IsCoupling (μ.map F) (m.map F) γ ∧
      (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2) ∂(γ : Measure (Y × Y))) ≤
        ENNReal.ofReal ((klDiv (μ : Measure X) (m : Measure X)).toReal / α) := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure (m : Measure X)
  have : Nonempty Y := Nonempty.map F ‹Nonempty X›
  let c : Y × Y → ℝ := fun z => dist z.1 z.2 ^ 2 / 2
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hcn (z : Y × Y) : 0 ≤ c z := by dsimp [c]; positivity
  have hreal (γ : ProbabilityMeasure (Y × Y)) :
      ENNReal.ofReal (∫ z, c z ∂(γ : Measure (Y × Y))) =
        ∫⁻ z, ENNReal.ofReal (c z) ∂(γ : Measure (Y × Y)) :=
    ofReal_integral_eq_lintegral_ofReal
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (ae_of_all _ hcn)
  obtain ⟨γ, hγ, hmin⟩ :=
    exists_isCoupling_forall_lintegral_le (μ.map F) (m.map F)
      (ENNReal.continuous_ofReal.comp hc)
  refine ⟨γ, hγ, ?_⟩
  change (∫⁻ z, ENNReal.ofReal (c z) ∂(γ : Measure (Y × Y))) ≤ _
  rw [← hreal]
  apply ENNReal.ofReal_le_ofReal
  have hle : (∫ z, c z ∂(γ : Measure (Y × Y))) ≤ sInf (primalValues (μ.map F) (m.map F) c) := by
    have hP : (primalValues (μ.map F) (m.map F) c).Nonempty := ⟨_, γ, hγ, rfl⟩
    apply le_csInf hP
    rintro _ ⟨γ', hγ', rfl⟩
    have h : (∫⁻ z, ENNReal.ofReal (c z) ∂(γ : Measure (Y × Y))) ≤
        ∫⁻ z, ENNReal.ofReal (c z) ∂(γ' : Measure (Y × Y)) := hmin γ' hγ'
    rw [← hreal, ← hreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hcn)).mp h
  refine hle.trans ?_
  rw [kantorovich_duality_compact (μ.map F) (m.map F) c hc]
  apply csSup_le
  · refine ⟨0, fun _ => 0, fun _ => 0, ⟨continuous_const, continuous_const, ?_⟩, by simp⟩
    exact fun x y => by simpa using hcn (x, y)
  rintro _ ⟨f, g, ⟨hfc, hgc, hfg⟩, rfl⟩
  let f₀ : Y →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hfc⟩
  let g₀ : Y →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨g, hgc⟩
  have hff (x : X) : |f (F x)| ≤ ‖f₀‖ := f₀.norm_coe_le_norm (F x)
  have hgg (x : X) : |-(g (F x))| ≤ ‖g₀‖ := by
    rw [abs_neg]
    exact g₀.norm_coe_le_norm (F x)
  have hfg' (x y : X) : f (F x) - -(g (F y)) ≤ cost R x y := by
    rw [sub_neg_eq_add]
    refine (hfg (F x) (F y)).trans ?_
    change dist (F x) (F y) ^ 2 / 2 ≤ min R (dist x y) ^ 2 / 2
    have hl : dist (F x) (F y) ≤ dist x y := by simpa using hF.dist_le_mul x y
    have hd : dist (F x) (F y) ≤ min R (dist x y) := le_min (hdiam _ _) hl
    gcongr
  have h := dual_bound hR hα hm hKL (hfc.comp hF.continuous)
    (hgc.comp hF.continuous).neg (norm_nonneg g₀) hff hgg hfg'
  change (∫ x, f (F x) ∂(μ : Measure X)) - (∫ x, -g (F x) ∂(m : Measure X)) ≤ _ at h
  rw [integral_neg, sub_neg_eq_add] at h
  simpa only [ProbabilityMeasure.toMeasure_map, integral_map hF.continuous.measurable.aemeasurable
    hfc.aestronglyMeasurable, integral_map hF.continuous.measurable.aemeasurable
    hgc.aestronglyMeasurable, Function.comp_apply] using h

end Projection

omit [MetricSpace X] in
private lemma exists_lift_coupling [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y]
    {F : X → Y} (hF : Measurable F) {μ m : ProbabilityMeasure X}
    {γ : ProbabilityMeasure (Y × Y)} (hγ : IsCoupling (μ.map F) (m.map F) γ) :
    ∃ η : ProbabilityMeasure (X × X), IsCoupling μ m η ∧
      (η : Measure (X × X)).map (fun z => (F z.1, F z.2)) = (γ : Measure (Y × Y)) := by
  let f : X → X × Y := fun x => (x, F x)
  let g : X → Y × X := fun x => (F x, x)
  have hf : Measurable f := measurable_id.prodMk hF
  have hg : Measurable g := hF.prodMk measurable_id
  -- Glue the coupling on the image to the graph of each marginal map.
  let ρ := (μ : Measure X).map f
  let σ := (m : Measure X).map g
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsProbabilityMeasure σ := inferInstance
  have hρ : ρ.map Prod.fst = μ := by
    dsimp [ρ]
    rw [Measure.map_map measurable_fst hf]
    exact Measure.map_id
  have hσ : σ.map Prod.snd = m := by
    dsimp [σ]
    rw [Measure.map_map measurable_snd hg]
    exact Measure.map_id
  have hmid : ρ.map Prod.snd = (γ : Measure (Y × Y)).map Prod.fst := by
    rw [← hγ.1]
    dsimp [ρ]
    rw [Measure.map_map measurable_snd hf]
    rfl
  obtain ⟨τ, hτ, hτ₁, hτ₂⟩ := exists_gluing ρ (γ : Measure (Y × Y)) hmid
  let := hτ
  have hmid' : τ.map Prod.snd = σ.map Prod.fst := by
    have hp : Measurable (fun z : (X × Y) × Y => (z.1.2, z.2)) := by fun_prop
    have heq := congrArg (fun ν : Measure (Y × Y) => ν.map Prod.snd) hτ₂
    rw [Measure.map_map measurable_snd hp, ← hγ.2] at heq
    rw [show τ.map Prod.snd = (γ : Measure (Y × Y)).map Prod.snd by
      rw [← hγ.2]; exact heq]
    rw [← hγ.2]
    dsimp [σ]
    rw [Measure.map_map measurable_fst hg]
    rfl
  obtain ⟨ω, hω, hω₁, hω₂⟩ := exists_gluing τ σ hmid'
  let := hω
  let i : ((X × Y) × Y) × X → X × X := fun w => (w.1.1.1, w.2)
  let j : ((X × Y) × Y) × X → Y × Y := fun w => (w.1.1.2, w.1.2)
  let k : ((X × Y) × Y) × X → Y × X := fun w => (w.1.2, w.2)
  change ω.map k = σ at hω₂
  have hi : Measurable i := by dsimp [i]; fun_prop
  have hj : Measurable j := by dsimp [j]; fun_prop
  have hk : Measurable k := by dsimp [k]; fun_prop
  let η : ProbabilityMeasure (X × X) := ⟨ω.map i, inferInstance⟩
  refine ⟨η, ⟨?_, ?_⟩, ?_⟩
  · change (μ : Measure X) = (ω.map i).map Prod.fst
    rw [← hρ, ← hτ₁, ← hω₁, Measure.map_map measurable_fst measurable_fst,
      Measure.map_map (measurable_fst.comp measurable_fst) measurable_fst,
      Measure.map_map measurable_fst hi]
    rfl
  · change (m : Measure X) = (ω.map i).map Prod.snd
    rw [← hσ, ← hω₂, Measure.map_map measurable_snd hk, Measure.map_map measurable_snd hi]
    rfl
  have hleftGraph : ∀ᵐ w ∂ρ, F w.1 = w.2 := by
    change ∀ᵐ w ∂(μ : Measure X).map f, F w.1 = w.2
    refine (ae_map_iff hf.aemeasurable
      (show MeasurableSet {w : X × Y | F w.1 = w.2} from
        measurableSet_eq_fun (hF.comp measurable_fst) measurable_snd)).mpr ?_
    exact ae_of_all _ fun _ => rfl
  have hrightGraph : ∀ᵐ w ∂σ, F w.2 = w.1 := by
    change ∀ᵐ w ∂(m : Measure X).map g, F w.2 = w.1
    refine (ae_map_iff hg.aemeasurable
      (show MeasurableSet {w : Y × X | F w.2 = w.1} from
        measurableSet_eq_fun (hF.comp measurable_snd) measurable_fst)).mpr ?_
    exact ae_of_all _ fun _ => rfl
  have hl : ∀ᵐ w ∂ω, F w.1.1.1 = w.1.1.2 := by
    rw [← hτ₁] at hleftGraph
    have ht := ae_of_ae_map measurable_fst.aemeasurable hleftGraph
    rw [← hω₁] at ht
    exact ae_of_ae_map measurable_fst.aemeasurable ht
  have hr : ∀ᵐ w ∂ω, F w.2 = w.1.2 :=
    ae_of_ae_map hk.aemeasurable (hω₂.symm ▸ hrightGraph)
  change (ω.map i).map (fun z => (F z.1, F z.2)) = _
  have hmap : Measurable (fun z : X × X => (F z.1, F z.2)) :=
    (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
  rw [Measure.map_map hmap hi]
  calc
    _ = ω.map j := Measure.map_congr (by
      filter_upwards [hl, hr] with w hw hw'
      exact Prod.ext hw hw')
    _ = _ := by
      rw [← hτ₂, ← hω₁, Measure.map_map (by fun_prop) measurable_fst]
      rfl

/-! ## Approximation by finite coordinate cubes -/

section CoordinateCubes

private abbrev CoordinateCube (n : ℕ) := Fin (n + 1) → Icc (0 : ℝ) ((n : ℝ) + 1)

private noncomputable def project (a : ℕ → X) (n : ℕ) (x : X) : CoordinateCube n :=
  fun i => ⟨cappedDist ((n : ℝ) + 1) x (a i),
    cappedDist_nonneg (by positivity) _ _, cappedDist_le _ _ _⟩

private lemma lipschitzWith_project (a : ℕ → X) (n : ℕ) :
    LipschitzWith 1 (project a n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  change |cappedDist _ x (a i) - cappedDist _ y (a i)| ≤ dist x y
  exact abs_cappedDist_sub_le _ _ _ _

private lemma dist_le_of_mem_cube {n : ℕ} (x y : CoordinateCube n) :
    dist x y ≤ (n : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  change |(x i : ℝ) - (y i : ℝ)| ≤ (n : ℝ) + 1
  rw [abs_sub_le_iff]
  exact ⟨sub_le_self _ (y i).2.1 |>.trans (x i).2.2,
    sub_le_self _ (x i).2.1 |>.trans (y i).2.2⟩

private lemma abs_min_sub_min_mono {r s : ℝ} (hrs : r ≤ s) (b c : ℝ) :
    |min r b - min r c| ≤ |min s b - min s c| := by
  wlog hbc : b ≤ c generalizing b c
  · rw [abs_sub_comm (min r b), abs_sub_comm (min s b)]
    exact this c b (le_of_not_ge hbc)
  rw [abs_sub_comm (min r b), abs_sub_comm (min s b),
    abs_of_nonneg (sub_nonneg.mpr (min_le_min_left _ hbc)),
    abs_of_nonneg (sub_nonneg.mpr (min_le_min_left _ hbc))]
  by_cases h : r ≤ b
  · rw [min_eq_left h, min_eq_left (h.trans hbc), sub_self]
    exact sub_nonneg.mpr (min_le_min_left _ hbc)
  · rw [min_eq_right (le_of_not_ge h), min_eq_right ((le_of_not_ge h).trans hrs)]
    exact sub_le_sub_right (min_le_min_right _ hrs) _

private lemma monotone_dist_project (a : ℕ → X) (x y : X) :
    Monotone (fun n => dist (project a n x) (project a n y)) := by
  intro n k hnk
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  let j : Fin (k + 1) := Fin.castLE (Nat.succ_le_succ hnk) i
  refine le_trans ?_ (dist_le_pi_dist (project a k x) (project a k y) j)
  change |min ((n : ℝ) + 1) (dist x (a i)) - min ((n : ℝ) + 1) (dist y (a i))| ≤
    |min ((k : ℝ) + 1) (dist x (a i)) - min ((k : ℝ) + 1) (dist y (a i))|
  apply abs_min_sub_min_mono
  exact add_le_add_left (Nat.cast_le.mpr hnk) 1

private lemma tendsto_dist_project {a : ℕ → X} (ha : DenseRange a) (x y : X) :
    Tendsto (fun n => dist (project a n x) (project a n y)) atTop (𝓝 (dist x y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp ha x (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (dist x (a i)) (dist y (a i)))
  refine ⟨max i N, fun n hn => ?_⟩
  have hin : i ≤ n := (le_max_left _ _).trans hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right i N).trans hn
  have hcap (d : ℝ) (hd : d ≤ max (dist x (a i)) (dist y (a i))) : d ≤ (n : ℝ) + 1 :=
    ((hd.trans hN.le).trans hNn).trans (le_add_of_nonneg_right zero_le_one)
  let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hin⟩
  have hcoord := dist_le_pi_dist (project a n x) (project a n y) j
  change |min ((n : ℝ) + 1) (dist x (a i)) - min ((n : ℝ) + 1) (dist y (a i))| ≤ _ at hcoord
  rw [min_eq_right (hcap _ (le_max_left _ _)), min_eq_right (hcap _ (le_max_right _ _))] at hcoord
  have hupper : dist (project a n x) (project a n y) ≤ dist x y := by
    simpa using (lipschitzWith_project a n).dist_le_mul x y
  have htriangle := dist_triangle_right x y (a i)
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith [neg_le_abs (dist x (a i) - dist y (a i))]

private noncomputable def projectedCost (a : ℕ → X) (n : ℕ) (z : X × X) : ℝ≥0∞ :=
  ENNReal.ofReal (dist (project a n z.1) (project a n z.2) ^ 2 / 2)

private lemma continuous_projectedCost (a : ℕ → X) (n : ℕ) : Continuous (projectedCost a n) := by
  apply ENNReal.continuous_ofReal.comp
  have h := (lipschitzWith_project a n).continuous
  exact ((h.comp continuous_fst).dist (h.comp continuous_snd)).pow 2 |>.div_const 2

private lemma monotone_projectedCost (a : ℕ → X) (z : X × X) :
    Monotone (fun n => projectedCost a n z) := by
  intro n k hnk
  apply ENNReal.ofReal_le_ofReal
  change dist (project a n z.1) (project a n z.2) ^ 2 / 2 ≤
    dist (project a k z.1) (project a k z.2) ^ 2 / 2
  gcongr
  exact monotone_dist_project a z.1 z.2 hnk

private lemma iSup_projectedCost {a : ℕ → X} (ha : DenseRange a) (z : X × X) :
    (⨆ n, projectedCost a n z) = ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2) :=
  tendsto_nhds_unique (tendsto_atTop_iSup (monotone_projectedCost a z))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((tendsto_dist_project ha z.1 z.2).pow 2).div_const 2))

end CoordinateCubes

open MathlibExt.MeasureTheory.OptimalTransport.Existence
  (isClosed_setOf_isCoupling isTightMeasureSet_setOf_isCoupling lowerSemicontinuous_lintegral)

private lemma exists_coupling_of_finite_entropy [CompleteSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ m : ProbabilityMeasure X} {α : ℝ} (hα : 0 < α)
    (hm : SatisfiesLogSobolev (m : Measure X) α)
    (hKL : klDiv (μ : Measure X) (m : Measure X) ≠ ⊤) :
    ∃ γ : ProbabilityMeasure (X × X), IsCoupling μ m γ ∧
      (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2) ∂(γ : Measure (X × X))) ≤
        ENNReal.ofReal ((klDiv (μ : Measure X) (m : Measure X)).toReal / α) := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure (m : Measure X)
  let a := TopologicalSpace.denseSeq X
  let C := ENNReal.ofReal ((klDiv (μ : Measure X) (m : Measure X)).toReal / α)
  let S := {γ : ProbabilityMeasure (X × X) | IsCoupling μ m γ}
  let T (n : ℕ) := S ∩ {γ : ProbabilityMeasure (X × X) |
    (∫⁻ z, projectedCost a n z ∂(γ : Measure (X × X))) ≤ C}
  have hScl : IsClosed S := isClosed_setOf_isCoupling μ m
  have hS : IsCompact S := by
    have h := isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_setOf_isCoupling μ m)
    rwa [hScl.closure_eq] at h
  have hTcl (n : ℕ) : IsClosed (T n) := hScl.inter
    ((lowerSemicontinuous_lintegral (continuous_projectedCost a n)).isClosed_preimage C)
  have hTn (n : ℕ) : (T n).Nonempty := by
    let F := project a n
    have hF := lipschitzWith_project a n
    obtain ⟨γ, hγ, hcost⟩ :=
      exists_compact_projection_coupling hF (by positivity) dist_le_of_mem_cube hα hm hKL
    obtain ⟨η, hη, hmap⟩ := exists_lift_coupling hF.continuous.measurable hγ
    refine ⟨η, hη, ?_⟩
    have hprod : Measurable (fun z : X × X => (F z.1, F z.2)) :=
      (hF.continuous.measurable.comp measurable_fst).prodMk
        (hF.continuous.measurable.comp measurable_snd)
    have hcost_m : Measurable (fun z : CoordinateCube n × CoordinateCube n =>
        ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2)) := by fun_prop
    change (∫⁻ z, ENNReal.ofReal (dist (F z.1) (F z.2) ^ 2 / 2) ∂(η : Measure (X × X))) ≤ C
    rwa [← lintegral_map hcost_m hprod, hmap]
  have hTmono (n : ℕ) : T (n + 1) ⊆ T n := by
    rintro γ ⟨hγ, hc⟩
    exact ⟨hγ, (lintegral_mono (fun z => monotone_projectedCost a z (Nat.le_succ n))).trans hc⟩
  -- Pick a single coupling satisfying every projected cost bound.
  have hT0 : IsCompact (T 0) := hS.of_isClosed_subset (hTcl 0) inter_subset_left
  obtain ⟨γ, hγ⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hTmono hTn hT0 hTcl
  have hγn (n : ℕ) : γ ∈ T n := mem_iInter.mp hγ n
  refine ⟨γ, (hγn 0).1, ?_⟩
  simp_rw [← iSup_projectedCost (TopologicalSpace.denseRange_denseSeq X)]
  rw [lintegral_iSup (fun n => (continuous_projectedCost a n).measurable)
    (fun i j hij z => monotone_projectedCost a z hij)]
  exact iSup_le (fun n => (hγn n).2)

end

/-- **Otto–Villani theorem.** Let `(X, d, m)` be a complete separable metric space with a Borel
probability measure `m` satisfying the logarithmic Sobolev inequality with constant `α > 0`
(formulation (i) of Proposition 5.1 of Gigli and Ledoux). Then `m` satisfies Talagrand's
inequality with constant `2/α`: `W₂(μ, m)² ≤ (2/α) KL(μ ‖ m)` for every probability measure `μ`
(N. Gigli and M. Ledoux, *From log Sobolev to Talagrand: a quick proof*, Discrete Contin. Dyn.
Syst. Ser. A (2013), Theorem 5.3; originally F. Otto and C. Villani, J. Funct. Anal. 173 (2000),
on Riemannian manifolds). -/
public theorem satisfiesTalagrand_of_satisfiesLogSobolev {X : Type*} [MetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (m : ProbabilityMeasure X) {α : ℝ} (hα : 0 < α)
    (hm : SatisfiesLogSobolev (m : Measure X) α) :
    SatisfiesTalagrand m (2 / α) := by
  intro μ
  by_cases hKL : klDiv (μ : Measure X) (m : Measure X) = ⊤
  · rw [hKL, ENNReal.mul_top (by positivity : ENNReal.ofReal (2 / α) ≠ 0)]
    exact le_top
  obtain ⟨γ, hγ, hcost⟩ := exists_coupling_of_finite_entropy hα hm hKL
  rw [wasserstein, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  refine (transportCost_le_of_isCoupling hγ).trans ?_
  have hcost_eq (z : X × X) :
      edist z.1 z.2 ^ (2 : ℝ) = 2 * ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2) := by
    rw [ENNReal.rpow_two, edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  calc
    _ = 2 * ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ 2 / 2) ∂(γ : Measure (X × X)) := by
      simp_rw [hcost_eq]
      exact lintegral_const_mul _ (by fun_prop)
    _ ≤ 2 * ENNReal.ofReal ((klDiv (μ : Measure X) (m : Measure X)).toReal / α) := by gcongr
    _ = _ := by
      conv_rhs => rw [← ENNReal.ofReal_toReal hKL]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end MathlibExt.Probability.OttoVillaniWanted
