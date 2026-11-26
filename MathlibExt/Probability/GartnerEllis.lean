/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LegendreTransform
public import MathlibExt.Probability.LargeDeviationPrinciple
import MathlibExt.Probability.CramerLDPLowerBound
import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The differentiable Gärtner–Ellis theorem

`satisfiesLDP_of_tendsto_scaledCGF` gives the large deviation bounds and a good rate
function when the scaled log moment generating functions have a finite differentiable limit.
We use the same tilted half-space estimate for the upper bound and for concentration
at a gradient point. Quadratic regularization then gives the lower bound on every open set.
-/

open MeasureTheory Filter Topology Set Metric
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.LegendreTransform
open MathlibExt.Probability.CramerLDPUpperBound (inner_single_one isCompact_box)
open MathlibExt.Probability.CramerLDPLowerBound (exists_pos_sub_lt_of_hasDerivAt)
open MathlibExt.Probability.VaradhanIntegralLemma (coe_le_inv_mul_log_iff inv_mul_log_le_coe_iff)

namespace MathlibExt.Probability.GartnerEllisWanted

private abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {ν : ℕ → Measure (Space d)} [∀ n, IsProbabilityMeasure (ν n)]
  {Λ : Space d → ℝ}

private noncomputable def scaledCGF (ν : ℕ → Measure (Space d)) (n : ℕ) (t : Space d) : ℝ :=
  (n : ℝ)⁻¹ * Real.log (∫ x, Real.exp (n * ⟪t, x⟫_ℝ) ∂(ν n))

private noncomputable abbrev rate (Λ : Space d → ℝ) (x : Space d) :=
  (legendreTransform (fun t => (Λ t : EReal)) x).toENNReal

private theorem rate_eq_iSup (Λ : Space d → ℝ) (x : Space d) :
    rate Λ x = ⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - Λ t) := by
  apply le_antisymm
  · have h : legendreTransform (fun t => (Λ t : EReal)) x ≤
        ((⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - Λ t) : ℝ≥0∞) : EReal) := by
      rw [legendreTransform_eq_iSup]
      refine iSup_le fun t => ?_
      rw [← EReal.coe_sub]
      refine le_trans ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (le_iSup (fun t => ENNReal.ofReal (⟪t, x⟫_ℝ - Λ t)) t))
      rw [EReal.coe_ennreal_ofReal]
      exact_mod_cast le_max_left (⟪t, x⟫_ℝ - Λ t) 0
    simpa [rate] using EReal.toENNReal_le_toENNReal h
  · refine iSup_le fun t => ?_
    simpa only [← EReal.coe_sub, EReal.real_coe_toENNReal, rate] using
      EReal.toENNReal_le_toENNReal (le_legendreTransform (Λ := fun t => (Λ t : EReal))
        (l := t) (x := x))

private noncomputable def direction (p : Fin d × Bool) : Space d :=
  if p.2 then EuclideanSpace.single p.1 (1 : ℝ) else -EuclideanSpace.single p.1 (1 : ℝ)

private theorem exists_direction {B : ℝ} {x : Space d} (hx : ¬∀ i, |x i| ≤ B) :
    ∃ p : Fin d × Bool, B < ⟪direction p, x⟫_ℝ := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  rcases lt_abs.mp (lt_of_not_ge hi) with h | h
  · exact ⟨(i, true), by simpa [direction, inner_single_one] using h⟩
  · exact ⟨(i, false), by simp [direction, inner_single_one]; linarith⟩

private theorem goodRate (Λ : Space d → ℝ) : IsGoodRateFunction (rate Λ) := by
  have hlsc : LowerSemicontinuous (rate Λ) := by
    simp_rw [funext (rate_eq_iSup Λ)]
    exact lowerSemicontinuous_iSup fun t =>
      (ENNReal.continuous_ofReal.comp (by fun_prop :
        Continuous fun x : Space d => ⟪t, x⟫_ℝ - Λ t)).lowerSemicontinuous
  refine ⟨⟨hlsc⟩, fun a => ?_⟩
  let B := max a 0 + ∑ p : Fin d × Bool, |Λ (direction p)|
  refine (isCompact_box B).of_isClosed_subset (hlsc.isClosed_preimage _) fun x hx => ?_
  by_contra h
  obtain ⟨p, hp⟩ := exists_direction h
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun p => |Λ (direction p)|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ p)
  have hx' : rate Λ x ≤ ENNReal.ofReal a := hx
  rw [rate_eq_iSup] at hx'
  have hterm := ENNReal.ofReal_le_ofReal_iff'.mp (iSup_le_iff.mp hx' (direction p))
  dsimp [B] at hp
  rcases hterm with h | h <;> linarith [le_abs_self (Λ (direction p)), le_max_left a 0,
    le_max_right a 0]

private noncomputable def tilt (ν : ℕ → Measure (Space d)) (θ : Space d) (n : ℕ) :=
  (ν n).tilted (fun x => n * ⟪θ, x⟫_ℝ)

private theorem exp_scaled (hexp : ∀ (n : ℕ) t, Integrable (fun x => Real.exp (n * ⟪t, x⟫_ℝ)) (ν n))
    {n : ℕ} (hn : 0 < n) (t : Space d) :
    Real.exp (n * scaledCGF ν n t) = ∫ x, Real.exp (n * ⟪t, x⟫_ℝ) ∂(ν n) := by
  rw [scaledCGF, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul,
    Real.exp_log (integral_exp_pos (hexp n t))]

-- On a half-space, transfer the tilt from θ to θ + t and integrate over the whole space.
private theorem tilted_halfspace (hexp : ∀ (n : ℕ) t, Integrable (fun x => Real.exp (n * ⟪t, x⟫_ℝ))
    (ν n)) (θ t : Space d) (c : ℝ) {n : ℕ} (hn : 0 < n) :
    (tilt ν θ n).real {x | c < ⟪t, x⟫_ℝ} ≤
      Real.exp (n * (scaledCGF ν n (θ + t) - scaledCGF ν n θ - c)) := by
  let H := {x : Space d | c < ⟪t, x⟫_ℝ}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (by fun_prop)
  let k := Real.exp (-(n * (scaledCGF ν n θ + c)))
  have hInt := (hexp n (θ + t)).mul_const k
  apply ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
  rw [tilt, tilted_apply]
  calc
    _ ≤ ∫⁻ x in H, ENNReal.ofReal (Real.exp (n * ⟪θ + t, x⟫_ℝ) * k) ∂(ν n) := by
      refine setLIntegral_mono' hH fun x hx => ENNReal.ofReal_le_ofReal ?_
      rw [← exp_scaled hexp hn θ, ← Real.exp_sub, ← Real.exp_add, inner_add_left]
      apply Real.exp_le_exp.mpr
      have hc : c ≤ ⟪t, x⟫_ℝ := le_of_lt hx
      nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) n)]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun _ => by positivity),
        integral_mul_const, ← exp_scaled hexp hn, ← Real.exp_add]
      congr 2
      ring

private theorem exp_tendsto_zero {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a))
    (ha : a < 0) : Tendsto (fun n : ℕ => Real.exp (n * u n)) atTop (𝓝 0) := by
  refine squeeze_zero' (.of_forall fun _ => (Real.exp_pos _).le) ?_
    (Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg
      (show a / 2 < 0 by linarith)))
  filter_upwards [hu.eventually_lt_const (show a < a / 2 by linarith)] with n hn
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn.le (Nat.cast_nonneg _))

section Bounds

variable (hexp : ∀ (n : ℕ) t, Integrable (fun x => Real.exp (n * ⟪t, x⟫_ℝ)) (ν n))
  (hlim : ∀ t, Tendsto (fun n => scaledCGF ν n t) atTop (𝓝 (Λ t)))

include hexp hlim in
/-- Cover the closed set by half-spaces with negative tilted exponential growth.
The coordinate half-spaces cover the complement of a compact box, so finitely many suffice. -/
private theorem closed_tilt_decay (θ : Space d) (q : ℝ) {F : Set (Space d)} (hF : IsClosed F)
    (hsep : ∀ x ∈ F, ∃ t, q + (Λ (θ + t) - Λ θ) < ⟪t, x⟫_ℝ) :
    Tendsto (fun n : ℕ => Real.exp (n * q) * (tilt ν θ n).real F) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (tilt ν θ n) := isProbabilityMeasure_tilted (hexp n θ)
  let P (s : Set (Space d)) := Tendsto
    (fun n : ℕ => Real.exp (n * q) * (tilt ν θ n).real s) atTop (𝓝 0)
  have mono {s t} (hst : s ⊆ t) (ht : P t) : P s := by
    apply squeeze_zero (fun _ => mul_nonneg (Real.exp_pos _).le measureReal_nonneg) _ ht
    exact fun _ => mul_le_mul_of_nonneg_left (measureReal_mono hst) (Real.exp_pos _).le
  have union {s t} (hs : P s) (ht : P t) : P (s ∪ t) := by
    refine squeeze_zero (fun _ => mul_nonneg (Real.exp_pos _).le measureReal_nonneg) ?_
      (by simpa only [add_zero] using hs.add ht)
    intro n
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (measureReal_union_le _ _) (Real.exp_pos _).le
  have halfspace (t : Space d) (c : ℝ) (hc : q + (Λ (θ + t) - Λ θ) < c) :
      P {y | c < ⟪t, y⟫_ℝ} := by
    have ht := exp_tendsto_zero ((tendsto_const_nhds.add ((hlim (θ + t)).sub (hlim θ))).sub
      (tendsto_const_nhds (x := c))) (sub_neg.mpr hc)
    apply squeeze_zero' (.of_forall fun _ => mul_nonneg (Real.exp_pos _).le measureReal_nonneg) _ ht
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply (mul_le_mul_of_nonneg_left (tilted_halfspace hexp θ t c hn) (Real.exp_pos _).le).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    exact le_of_eq (by ring)
  let B := q + (∑ p : Fin d × Bool, |Λ (θ + direction p) - Λ θ|) + 1
  let K := {x : Space d | ∀ i, |x i| ≤ B}
  let H := fun p : Fin d × Bool => {x : Space d | B < ⟪direction p, x⟫_ℝ}
  have hH (p) : P (H p) := by
    apply halfspace
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun p => |Λ (θ + direction p) - Λ θ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)
    dsimp [B]
    linarith [le_abs_self (Λ (θ + direction p) - Λ θ)]
  have hK : P Kᶜ := by
    apply mono (t := ⋃ p, H p) fun x hx => mem_iUnion.mpr (exists_direction hx)
    refine squeeze_zero (fun _ => mul_nonneg (Real.exp_pos _).le measureReal_nonneg) ?_
      (by simpa using tendsto_finsetSum Finset.univ fun p _ => hH p)
    intro n
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le H) (Real.exp_pos _).le
  have hFK : P (F ∩ K) := by
    apply ((isCompact_box B).inter_left hF).induction_on (p := P)
    · simp [P]
    · exact fun _ _ h => mono h
    · exact fun _ _ => union
    · intro x hx
      obtain ⟨t, ht⟩ := hsep x hx.1
      obtain ⟨c, hc, hcx⟩ := exists_between ht
      exact ⟨{y | c < ⟪t, y⟫_ℝ}, mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hcx), halfspace t c hc⟩
  apply mono (t := (F ∩ K) ∪ Kᶜ) _ (union hFK hK)
  intro x hx
  by_cases h : x ∈ K
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

include hexp hlim in
private theorem upper_bound (hzero : Λ 0 = 0) {F : Set (Space d)} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n F)) atTop ≤
      -(⨅ x ∈ F, (rate Λ x : EReal)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  rw [EReal.neg_lt_comm] at hb
  obtain ⟨q, hbq, hq⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hsmall := closed_tilt_decay hexp hlim 0 q hF fun x hx => by
    have h := hq.trans_le (iInf₂_le (f := fun x (_ : x ∈ F) => (rate Λ x : EReal)) x hx)
    have hnn : 0 ≤ legendreTransform (fun t => (Λ t : EReal)) x := by
      simpa [hzero] using le_legendreTransform (Λ := fun t => (Λ t : EReal)) (l := 0) (x := x)
    rw [rate, EReal.coe_toENNReal hnn, legendreTransform_eq_iSup, lt_iSup_iff] at h
    obtain ⟨t, ht⟩ := h
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff] at ht
    exact ⟨t, by rw [zero_add, hzero]; linarith⟩
  have hz (n : ℕ) : tilt ν 0 n = ν n := by simp [tilt]
  simp only [hz] at hsmall
  have hqb : ((-q : ℝ) : EReal) ≤ b := by
    rw [EReal.coe_neg]
    exact (EReal.neg_lt_comm.mp hbq).le
  refine le_trans (limsup_le_of_le (by isBoundedDefault) ?_) hqb
  filter_upwards [hsmall.eventually_lt_const zero_lt_one, eventually_gt_atTop 0] with n h hn
  rw [inv_mul_log_le_coe_iff hn, mul_neg, Real.exp_neg, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [← one_div, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact h.le

include hexp hlim in
private theorem ball_lower {θ x : Space d} (hg : HasFDerivAt Λ (innerSL ℝ x) θ)
    {δ : ℝ} (hδ : 0 < δ) :
    ((-(⟪θ, x⟫_ℝ - Λ θ) - ‖θ‖ * δ : ℝ) : EReal) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n (ball x δ))) atTop := by
  have (n : ℕ) : IsProbabilityMeasure (tilt ν θ n) := isProbabilityMeasure_tilted (hexp n θ)
  -- The derivative strictly separates every other point from x after tilting.
  have hsmall := closed_tilt_decay hexp hlim θ 0 isOpen_ball.isClosed_compl
    (F := (ball x δ)ᶜ) fun y hy => by
      have hyx : y ≠ x := fun h => hy (h ▸ mem_ball_self hδ)
      let e := y - x
      have he : 0 < ‖e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))
      have hline : HasDerivAt (fun s : ℝ => θ + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add θ
      have hg' : HasFDerivAt Λ (innerSL ℝ x) (θ + (0 : ℝ) • e) := by simpa using hg
      obtain ⟨s, hs, h⟩ := exists_pos_sub_lt_of_hasDerivAt (hg'.comp_hasDerivAt 0 hline) he
      refine ⟨s • e, ?_⟩
      simp only [Function.comp_apply, zero_smul, add_zero, innerSL_apply_apply] at h
      have hid : ⟪e, y⟫_ℝ = ⟪x, e⟫_ℝ + ‖e‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← inner_add_left, add_sub_cancel x y, real_inner_comm]
      simpa only [zero_add, real_inner_smul_left, hid] using h
  simp only [mul_zero, Real.exp_zero, one_mul] at hsmall
  let A := ⟪θ, x⟫_ℝ + ‖θ‖ * δ
  have hweight (n : ℕ) (hn : 0 < n) : (tilt ν θ n).real (ball x δ) ≤
      Real.exp (n * (A - scaledCGF ν n θ)) * (ν n).real (ball x δ) := by
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
    rw [tilt, tilted_apply, ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal,
      ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ENNReal.ofReal_le_ofReal ?_
    rw [← exp_scaled hexp hn θ, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have h1 := real_inner_le_norm θ (y - x)
    rw [inner_sub_right] at h1
    have h2 : ‖y - x‖ ≤ δ := by rw [← dist_eq_norm]; exact le_of_lt hy
    have h3 : ⟪θ, y⟫_ℝ ≤ A := by dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg θ)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) n)]
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  obtain ⟨r, hbr, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  rw [EReal.coe_lt_coe_iff] at hr
  have hdec := exp_tendsto_zero
    ((tendsto_const_nhds (x := r + A)).sub (hlim θ)) (by dsimp [A]; linarith)
  refine hbr.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [hsmall.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    hdec.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num), eventually_gt_atTop 0]
    with n hcomp hdec hn
  have hmass := measureReal_add_measureReal_compl (μ := tilt ν θ n) (s := ball x δ)
    measurableSet_ball
  rw [probReal_univ] at hmass
  rw [coe_le_inv_mul_log_iff hn, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_mul_le_mul_left (a := Real.exp (n * (A - scaledCGF ν n θ))) _ (Real.exp_pos _)
  refine le_trans ?_ (hweight n hn)
  rw [← Real.exp_add]
  have hrew : (n : ℝ) * (A - scaledCGF ν n θ) + n * r = n * (r + A - scaledCGF ν n θ) := by ring
  rw [hrew]
  linarith

-- Quadratic regularization approximates a point of finite rate by a gradient point
-- while controlling its supporting affine functional.
private theorem exists_gradient_near (hdiff : Differentiable ℝ Λ) (hzero : Λ 0 = 0)
    (x : Space d) {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hFY : ∀ t, ⟪t, x⟫_ℝ - Λ t ≤ c) :
    ∃ θ y : Space d, HasFDerivAt Λ (innerSL ℝ y) θ ∧
      dist y x < ρ ∧ ⟪θ, y⟫_ℝ - Λ θ ≤ c := by
  let ε := ρ ^ 2 / (2 * (c + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hερ : ε * (2 * (c + 1)) = ρ ^ 2 := div_mul_cancel₀ _ (by positivity)
  let f (t : Space d) := ⟪x, t⟫_ℝ - Λ t - ε / 2 * ‖t‖ ^ 2
  have hcont : Continuous f := by
    have := hdiff.continuous
    dsimp [f]
    fun_prop
  have hf0 : f 0 = 0 := by simp [f, hzero]
  obtain ⟨θ, hθ⟩ := hcont.exists_forall_ge' 0 (by
    let R := 2 * (c + 1) / ε + 1
    filter_upwards [(isCompact_closedBall (0 : Space d) R).compl_mem_cocompact] with t ht
    have htR : R < ‖t‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using ht
    have hR : 1 ≤ R := by dsimp [R]; linarith [div_nonneg (by positivity : 0 ≤ 2 * (c + 1)) hε.le]
    have hs : ‖t‖ ≤ ‖t‖ ^ 2 := by nlinarith
    have hRε : 2 * (c + 1) ≤ ε * R := by
      dsimp [R]
      rw [mul_add ε, mul_div_cancel₀ _ hε.ne']
      linarith
    rw [hf0]
    dsimp [f]
    rw [real_inner_comm]
    nlinarith [hFY t])
  let y := x - ε • θ
  have hθ0 := hθ 0
  rw [hf0] at hθ0
  change 0 ≤ ⟪x, θ⟫_ℝ - Λ θ - ε / 2 * ‖θ‖ ^ 2 at hθ0
  rw [real_inner_comm] at hθ0
  have hpen : ε / 2 * ‖θ‖ ^ 2 ≤ c := by linarith [hFY θ]
  refine ⟨θ, y, ?_, ?_, ?_⟩
  · have hL := (hdiff θ).hasFDerivAt
    have hderiv : HasFDerivAt f (innerSL ℝ x - fderiv ℝ Λ θ - (ε / 2) • (2 • innerSL ℝ θ)) θ :=
      (((innerSL ℝ x).hasFDerivAt).sub hL).sub
        ((hasStrictFDerivAt_norm_sq θ).hasFDerivAt.const_smul (ε / 2))
    have hstat := IsLocalMax.hasFDerivAt_eq_zero (Eventually.of_forall hθ) hderiv
    convert hL using 1
    ext v
    have := congrArg (fun T : Space d →L[ℝ] ℝ => T v) hstat
    simp [innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul] at this
    simp only [innerSL_apply_apply, y, inner_sub_left, real_inner_smul_left]
    linarith
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    apply lt_of_pow_lt_pow_left₀ 2 hρ.le
    nlinarith [mul_le_mul_of_nonneg_left hpen hε.le]
  · dsimp [y]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [hFY θ, mul_nonneg hε.le (sq_nonneg ‖θ‖)]

include hexp hlim in
private theorem lower_bound (hzero : Λ 0 = 0) (hdiff : Differentiable ℝ Λ)
    {U : Set (Space d)} (hU : IsOpen U) :
    -(⨅ x ∈ U, (rate Λ x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n U)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  rw [EReal.lt_neg_comm, iInf_lt_iff] at hb
  obtain ⟨x, hx⟩ := hb
  obtain ⟨hxU, hx⟩ := iInf_lt_iff.mp hx
  have hfin : rate Λ x ≠ ⊤ := fun heq => by
    rw [heq, EReal.coe_ennreal_top] at hx
    exact not_top_lt hx
  let c := (rate Λ x).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hcx : (rate Λ x : EReal) = (c : EReal) := (EReal.coe_ennreal_toReal hfin).symm
  rw [hcx, EReal.lt_neg_comm, ← EReal.coe_neg] at hx
  obtain ⟨r, hbr, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hx
  rw [EReal.coe_lt_coe_iff] at hr
  have hFY (t) : ⟪t, x⟫_ℝ - Λ t ≤ c := by
    have h : ENNReal.ofReal (⟪t, x⟫_ℝ - Λ t) ≤ rate Λ x := by
      rw [rate_eq_iSup]
      exact le_iSup (fun t => ENNReal.ofReal (⟪t, x⟫_ℝ - Λ t)) t
    rwa [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff hc] at h
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨θ, y, hg, hdist, hcost⟩ :=
    exists_gradient_near hdiff hzero x hc (half_pos hρ) hFY
  let δ := min (ρ / 2) ((-c - r) / (‖θ‖ + 1))
  have hδ : 0 < δ := lt_min (half_pos hρ) (div_pos (by linarith) (by positivity))
  have hball : ball y δ ⊆ U := fun z hz => hρU (by
    have hz' := mem_ball.mp hz
    have := min_le_left (ρ / 2) ((-c - r) / (‖θ‖ + 1))
    change dist z x < ρ
    dsimp [δ] at hz'
    linarith [dist_triangle z y x])
  have hδcost : ‖θ‖ * δ ≤ -c - r := by
    have h := (le_div_iff₀ (by positivity : 0 < ‖θ‖ + 1)).mp (min_le_right (ρ / 2)
      ((-c - r) / (‖θ‖ + 1)))
    change δ * (‖θ‖ + 1) ≤ -c - r at h
    nlinarith
  refine hbr.le.trans (le_trans ?_ ((ball_lower hexp hlim hg hδ).trans ?_))
  · exact_mod_cast (show r ≤ -(⟪θ, y⟫_ℝ - Λ θ) - ‖θ‖ * δ by linarith)
  · apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
    exact .of_forall fun n => mul_le_mul_of_nonneg_left (ENNReal.log_monotone (measure_mono hball))
      (EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n))

end Bounds

/-- **Gärtner–Ellis theorem, differentiable case.** Let `νₙ` be probability measures on
`ℝᵈ` (the laws of random vectors `Zₙ`) such that `x ↦ exp (n ⟪t, x⟫)` is `νₙ`-integrable for
all `n` and `t`, and suppose the scaled cumulant generating functions converge,
`(1/n) log ∫ exp (n ⟪t, x⟫) dνₙ(x) → Λ(t)` for every `t`, to a function `Λ : ℝᵈ → ℝ` that is
differentiable everywhere. Then `νₙ` satisfies the large deviation principle with the good
rate function `Λ*(x) = sup_t (⟪t, x⟫ - Λ(t))`.
Source: A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
Section 2.3 (the case of a finite, everywhere differentiable limit, which is essentially
smooth). -/
public theorem satisfiesLDP_of_tendsto_scaledCGF {d : ℕ}
    {ν : ℕ → Measure (EuclideanSpace ℝ (Fin d))} [∀ n, IsProbabilityMeasure (ν n)]
    (hexp : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin d)),
      Integrable (fun x => Real.exp (n * ⟪t, x⟫_ℝ)) (ν n))
    {Λ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hlim : ∀ t, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log (∫ x, Real.exp (n * ⟪t, x⟫_ℝ) ∂(ν n))) atTop (𝓝 (Λ t)))
    (hdiff : Differentiable ℝ Λ) :
    SatisfiesLDP ν (fun x => (legendreTransform (fun t => (Λ t : EReal)) x).toENNReal) ∧
      IsGoodRateFunction (fun x => (legendreTransform (fun t => (Λ t : EReal)) x).toENNReal) := by
  have hzero : Λ 0 = 0 := tendsto_nhds_unique (hlim 0) (by simp)
  have hgood := goodRate Λ
  exact ⟨⟨hgood.toIsRateFunction, fun _ => lower_bound hexp hlim hzero hdiff,
    fun _ => upper_bound hexp hlim hzero⟩, hgood⟩

end MathlibExt.Probability.GartnerEllisWanted
