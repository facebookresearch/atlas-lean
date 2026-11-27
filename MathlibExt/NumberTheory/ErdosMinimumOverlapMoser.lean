/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! # Moser's lower bound for minimum overlap

The second moment and a Fourier coefficient of the overlap show that every admissible pair's
score is at least `713 / 2000`. This implies `lowerBound_M1959_holds`, the lower bound
`√(4 - √15) ≤ C₁ᵦ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

-- This proposition precedes Moser's to preserve their shared numeral proof for 4.
/-- **Statement of the Motzkin–Ralston–Selfridge upper bound $0.4$ for the minimum-overlap
constant.** The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$
satisfies $C_{1b} \le 0.4$.

Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_pointFour : Prop := C₁ᵦ ≤ (4 : ℝ) / 10

/-- **The proposition $\sqrt{4 - \sqrt{15}} \le C_{1b}$.** This is the proposition that the
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $\sqrt{4 - \sqrt{15}} \le C_{1b}$.

Source: Moser 1959; Optimization Problems, Constant 1b. -/
def lowerBound_M1959 : Prop := Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ

namespace Moser

private theorem integrable_mul_continuous_on_support {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [T2Space α] [BorelSpace α] {μ : Measure α}
    {u w : α → ℝ} {s : Set α} (hu : Integrable u μ) (hs : IsCompact s)
    (hz : ∀ x ∉ s, u x = 0) (hw : Continuous w) :
    Integrable (fun x ↦ u x * w x) μ := by
  obtain ⟨b, hb⟩ := (hs.image hw.norm).bddAbove
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := s) ?_
    (fun x hx ↦ by simp [hz x hx])
  apply hu.integrableOn.mul_bdd (c := b) hw.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := μ) hs.isClosed.measurableSet] with x hx
  exact hb ⟨x, hx, rfl⟩

variable {f g : ℝ → ℝ} (h : ContinuousAdmissible f g)

include h

private theorem overlap_eq_integral (x : ℝ) :
    continuousOverlap f g x = ∫ t, f t * g (x + t) :=
  setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht ↦ by simp [continuousOverlapIntegrand, h.zero_outside_f t ht])

private theorem overlap_zero (x : ℝ) (hx : x ∉ continuousTranslationInterval) :
    continuousOverlap f g x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have hout : x + t ∉ continuousSupportInterval := by
    intro hxt
    exact hx ⟨by linarith [hxt.1, ht.2], by linarith [hxt.2, ht.1]⟩
  simp [continuousOverlapIntegrand, h.zero_outside_g _ hout]

-- The map (x, t) ↦ (t, x + t) turns translation x into the difference of two coordinates.
private theorem overlap_weight {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable (fun x ↦ continuousOverlap f g x * w x) ∧
      (∫ x, continuousOverlap f g x * w x) =
        ∫ p : ℝ × ℝ, f p.1 * g p.2 * w (p.2 - p.1) ∂volume.prod volume := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.shearAddRight ℝ)
  have he : MeasurePreserving e (volume.prod volume) (volume.prod volume) := by
    convert measurePreserving_prod_add_swap_right (volume : Measure ℝ) volume using 1
    funext p
    change (p.2, p.2 + p.1) = (p.2, p.1 + p.2)
    rw [add_comm]
  let k (p : ℝ × ℝ) := f p.1 * g p.2 * w (p.2 - p.1)
  have hk : Integrable k (volume.prod volume) := by
    apply integrable_mul_continuous_on_support (h.integrable_f.mul_prod h.integrable_g)
      (s := continuousSupportInterval ×ˢ continuousSupportInterval)
      (isCompact_Icc.prod isCompact_Icc) ?_ (hw.comp (continuous_snd.sub continuous_fst))
    rintro ⟨x, y⟩ hxy
    by_cases hx : x ∈ continuousSupportInterval
    · have hy : y ∉ continuousSupportInterval := fun hy ↦ hxy ⟨hx, hy⟩
      simp [h.zero_outside_g y hy]
    · simp [h.zero_outside_f x hx]
  have hke : Integrable (k ∘ e) (volume.prod volume) :=
    (he.integrable_comp hk.aestronglyMeasurable).2 hk
  have hinner (x : ℝ) :
      (∫ t, (k ∘ e) (x, t)) = continuousOverlap f g x * w x := by
    rw [overlap_eq_integral h, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t
    change f t * g (t + x) * w (t + x - t) = f t * g (x + t) * w x
    rw [add_comm t x, add_sub_cancel_right]
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hke.integral_prod_left
  · simp_rw [← hinner]
    exact (integral_prod (k ∘ e) hke).symm.trans (he.integral_comp' k)

private theorem integrable_overlap : Integrable (continuousOverlap f g) := by
  simpa using (overlap_weight h (continuous_const (y := (1 : ℝ)))).1

-- Complementarity identifies the sum of the weighted masses with an interval integral.
private theorem integral_weight_sum {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x, f x * w x) + (∫ x, g x * w x) = ∫ x in (-1 : ℝ)..1, w x := by
  have hf := integrable_mul_continuous_on_support h.integrable_f isCompact_Icc
    h.zero_outside_f hw
  have hg := integrable_mul_continuous_on_support h.integrable_g isCompact_Icc
    h.zero_outside_g hw
  rw [← integral_add hf hg, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := continuousSupportInterval)]
  · apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [← add_mul, h.complementary x hx, one_mul]
  · intro x hx
    simp [h.zero_outside_f x hx, h.zero_outside_g x hx]

private theorem integral_g : (∫ x, g x) = 1 := by
  have hsum := integral_weight_sum h (continuous_const (y := (1 : ℝ)))
  norm_num [h.integral_f, intervalIntegral.integral_const] at hsum
  linarith

private theorem integral_overlap : (∫ x, continuousOverlap f g x) = 1 := by
  simpa [integral_prod_mul, h.integral_f, integral_g h] using
    (overlap_weight h (continuous_const (y := (1 : ℝ)))).2

-- If the mean difference is m, the second moment about c is 2/3 + m²/2 - 2cm + c².
private theorem overlap_quadratic (c : ℝ) :
    (∫ x, continuousOverlap f g x * (x - c) ^ 2) =
      2 / 3 + ((∫ x, g x * x) - (∫ x, f x * x)) ^ 2 / 2
        - 2 * c * ((∫ x, g x * x) - (∫ x, f x * x)) + c ^ 2 := by
  have hf {w : ℝ → ℝ} (hw : Continuous w) : Integrable (fun x ↦ f x * w x) :=
    integrable_mul_continuous_on_support h.integrable_f isCompact_Icc h.zero_outside_f hw
  have hg {w : ℝ → ℝ} (hw : Continuous w) : Integrable (fun x ↦ g x * w x) :=
    integrable_mul_continuous_on_support h.integrable_g isCompact_Icc h.zero_outside_g hw
  have hf₁ := hf (w := fun x ↦ x) continuous_id
  have hg₁' := hg (w := fun x ↦ x) continuous_id
  have hf₂ := hf (w := fun x ↦ x ^ 2) (by fun_prop)
  have hg₂' := hg (w := fun x ↦ x ^ 2) (by fun_prop)
  have hg₁c := hg (w := fun x ↦ x - c) (by fun_prop)
  have hg₂c := hg (w := fun x ↦ (x - c) ^ 2) (by fun_prop)
  have hm₁ : (∫ x, f x * x) + (∫ x, g x * x) = 0 := by
    simpa [integral_id] using integral_weight_sum h continuous_id
  have hm₂ : (∫ x, f x * x ^ 2) + (∫ x, g x * x ^ 2) = 2 / 3 := by
    have he := integral_weight_sum h (w := fun x ↦ x ^ 2) (by fun_prop)
    rw [integral_pow] at he
    norm_num at he
    exact he
  have hg₁ : (∫ x, g x * (x - c)) = (∫ x, g x * x) - c := by
    simp_rw [mul_sub]
    rw [integral_sub hg₁' (h.integrable_g.mul_const c),
      integral_mul_const, integral_g h, one_mul]
  have hg₂ : (∫ x, g x * (x - c) ^ 2) =
      (∫ x, g x * x ^ 2) - 2 * c * (∫ x, g x * x) + c ^ 2 := by
    have hexpand : (fun x ↦ g x * (x - c) ^ 2) =
        fun x ↦ g x * x ^ 2 - (2 * c) * (g x * x) + g x * c ^ 2 := by
      funext x
      ring
    rw [hexpand]
    change (∫ x, ((fun t ↦ g t * t ^ 2) - (fun t ↦ 2 * c * (g t * t))) x +
      g x * c ^ 2) = _
    rw [integral_add (hg₂'.sub (hg₁'.const_mul (2 * c))) (h.integrable_g.mul_const (c ^ 2)),
      integral_sub' hg₂' (hg₁'.const_mul (2 * c)),
      integral_const_mul, integral_mul_const, integral_g h, one_mul]
  rw [(overlap_weight h (w := fun x ↦ (x - c) ^ 2) (by fun_prop)).2]
  have hexpand : (fun p : ℝ × ℝ ↦ f p.1 * g p.2 * (p.2 - p.1 - c) ^ 2) =
      fun p ↦ (f p.1 * p.1 ^ 2) * g p.2 + f p.1 * (g p.2 * (p.2 - c) ^ 2)
        - 2 * ((f p.1 * p.1) * (g p.2 * (p.2 - c))) := by
    funext p
    ring
  rw [hexpand]
  change (∫ p : ℝ × ℝ, ((fun p : ℝ × ℝ ↦ (f p.1 * p.1 ^ 2) * g p.2) +
    (fun p : ℝ × ℝ ↦ f p.1 * (g p.2 * (p.2 - c) ^ 2))) p -
    2 * ((f p.1 * p.1) * (g p.2 * (p.2 - c))) ∂volume.prod volume) = _
  rw [integral_sub ((hf₂.mul_prod h.integrable_g).add (h.integrable_f.mul_prod hg₂c))
      ((hf₁.mul_prod hg₁c).const_mul 2),
    integral_add' (hf₂.mul_prod h.integrable_g) (h.integrable_f.mul_prod hg₂c),
    integral_const_mul, integral_prod_mul (fun x ↦ f x * x ^ 2) g,
    integral_prod_mul f (fun x ↦ g x * (x - c) ^ 2),
    integral_prod_mul (fun x ↦ f x * x) (fun x ↦ g x * (x - c)),
    h.integral_f, integral_g h, hg₁, hg₂]
  nlinarith [sq_nonneg ((∫ x, f x * x) + (∫ x, g x * x))]

private noncomputable def cosine (x : ℝ) : ℝ := Real.cos (2 * π * x)
private noncomputable def sine (x : ℝ) : ℝ := Real.sin (2 * π * x)

omit h in
private theorem integral_cosine (a b : ℝ) :
    (∫ x in a..b, cosine x) = (sine b - sine a) / (2 * π) := by
  apply (eq_div_iff (by positivity : (2 * π : ℝ) ≠ 0)).2
  rw [mul_comm]
  exact (intervalIntegral.mul_integral_comp_mul_left (f := Real.cos) (2 * π)).trans integral_cos

omit h in
private theorem integral_sine (a b : ℝ) :
    (∫ x in a..b, sine x) = (cosine a - cosine b) / (2 * π) := by
  apply (eq_div_iff (by positivity : (2 * π : ℝ) ≠ 0)).2
  rw [mul_comm]
  exact (intervalIntegral.mul_integral_comp_mul_left (f := Real.sin) (2 * π)).trans integral_sin

-- The sine and cosine integrals of f + g vanish at this frequency.
private theorem overlap_cosine_nonpos : (∫ x, continuousOverlap f g x * cosine x) ≤ 0 := by
  have hc : Continuous cosine := by unfold cosine; fun_prop
  have hs : Continuous sine := by unfold sine; fun_prop
  have hcos : (∫ x, f x * cosine x) + (∫ x, g x * cosine x) = 0 := by
    rw [integral_weight_sum h hc, integral_cosine]
    simp [sine, mul_neg]
  have hsin : (∫ x, f x * sine x) + (∫ x, g x * sine x) = 0 := by
    rw [integral_weight_sum h hs, integral_sine]
    simp [cosine, mul_neg]
  have hf {w : ℝ → ℝ} (hw : Continuous w) : Integrable (fun x ↦ f x * w x) :=
    integrable_mul_continuous_on_support h.integrable_f isCompact_Icc h.zero_outside_f hw
  have hg {w : ℝ → ℝ} (hw : Continuous w) : Integrable (fun x ↦ g x * w x) :=
    integrable_mul_continuous_on_support h.integrable_g isCompact_Icc h.zero_outside_g hw
  rw [(overlap_weight h hc).2]
  have htrig : (fun p : ℝ × ℝ ↦ f p.1 * g p.2 * cosine (p.2 - p.1)) =
      fun p ↦ (f p.1 * cosine p.1) * (g p.2 * cosine p.2) +
        (f p.1 * sine p.1) * (g p.2 * sine p.2) := by
    funext p
    simp only [cosine, sine, mul_sub, Real.cos_sub]
    ring
  rw [htrig, integral_add ((hf hc).mul_prod (hg hc)) ((hf hs).mul_prod (hg hs)),
    integral_prod_mul (fun x ↦ f x * cosine x) (fun x ↦ g x * cosine x),
    integral_prod_mul (fun x ↦ f x * sine x) (fun x ↦ g x * sine x)]
  rw [eq_neg_of_add_eq_zero_right hcos, eq_neg_of_add_eq_zero_right hsin]
  nlinarith [sq_nonneg (∫ x, f x * cosine x), sq_nonneg (∫ x, f x * sine x)]

-- Bound the weighted integral from below by filling the sublevel interval at height q.
private theorem overlap_weight_lower {w : ℝ → ℝ} (hw : Continuous w) {q a b c : ℝ}
    (hq : ∀ x, continuousOverlap f g x ≤ q) (hab : a ≤ b)
    (hin : ∀ x ∈ Icc a b, w x ≤ c) (hout : ∀ x ∉ Icc a b, c ≤ w x) :
    (1 - q * (b - a)) * c + q * (∫ x in a..b, w x) ≤
      ∫ x, continuousOverlap f g x * w x := by
  have hi : Integrable ((Icc a b).indicator (fun x ↦ q * (c - w x))) :=
    ((show Continuous (fun x ↦ q * (c - w x)) by fun_prop).integrableOn_Icc
      (μ := volume)).integrable_indicator measurableSet_Icc
  have hc := (integrable_overlap h).mul_const c
  have hweight := (overlap_weight h hw).1
  have hle := integral_mono (hc.sub hweight) hi ?_
  · rw [integral_sub' hc hweight, integral_mul_const, integral_overlap h, one_mul,
      integral_indicator measurableSet_Icc, integral_const_mul,
      integral_sub (integrableOn_const measure_Icc_lt_top.ne) hw.integrableOn_Icc,
      setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (sub_nonneg.mpr hab),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hle
    linarith only [hle]
  · intro x
    change continuousOverlap f g x * c - continuousOverlap f g x * w x ≤ _
    rw [← mul_sub]
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (hq x) (sub_nonneg.mpr (hin x hx))
    · rw [indicator_of_notMem hx]
      exact mul_nonpos_of_nonneg_of_nonpos (continuousOverlap_nonneg h x)
        (sub_nonpos.mpr (hout x hx))

private noncomputable def cosineWeight (x : ℝ) : ℝ := x ^ 2 + (3 / 8) * cosine x

omit h in
private theorem cosineWeight_le_of_le {x y : ℝ} (hxy : x ≤ y) (hsum : 12 / 5 ≤ x + y) :
    cosineWeight x ≤ cosineWeight y := by
  have hcos := (le_abs_self _).trans (Real.abs_cos_sub_cos_le (2 * π * x) (2 * π * y))
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π),
    abs_of_nonpos (sub_nonpos.mpr hxy)] at hcos
  have hslope : (3 / 8 : ℝ) * (2 * π) - (x + y) ≤ 0 := by
    linarith [Real.pi_lt_d2]
  have hquad := mul_nonpos_of_nonpos_of_nonneg hslope (sub_nonneg.mpr hxy)
  unfold cosineWeight cosine
  nlinarith only [hquad, hcos]

omit h in
private theorem cosineWeight_abs (x : ℝ) : cosineWeight |x| = cosineWeight x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx]
    simp [cosineWeight, cosine, mul_neg]

omit h in
private theorem cosineWeight_cutoff :
    (∀ x ∈ Icc (-(7 / 5) : ℝ) (7 / 5), cosineWeight x ≤ cosineWeight (7 / 5)) ∧
    (∀ x ∉ Icc (-(7 / 5) : ℝ) (7 / 5), cosineWeight (7 / 5) ≤ cosineWeight x) := by
  constructor
  · intro x hx
    rw [← cosineWeight_abs x]
    have ha : |x| ≤ 7 / 5 := abs_le.mpr hx
    by_cases hx₁ : 1 ≤ |x|
    · exact cosineWeight_le_of_le ha (by linarith)
    · have hs : x ^ 2 ≤ 1 := by
        rw [← sq_abs x]
        simpa using pow_le_pow_left₀ (abs_nonneg x) (le_of_not_ge hx₁) 2
      norm_num [cosineWeight, cosine]
      linarith [Real.cos_le_one (2 * π * |x|), Real.neg_one_le_cos (2 * π * (7 / 5))]
  · intro x hx
    have ha : (7 / 5 : ℝ) ≤ |x| := by
      by_contra! hlt
      exact hx (abs_le.mp hlt.le)
    rw [← cosineWeight_abs x]
    exact cosineWeight_le_of_le ha (by linarith)

omit h in
private theorem integral_cosineWeight_lower :
    (947 / 500 : ℝ) ≤ ∫ x in (-(7 / 5) : ℝ)..(7 / 5), cosineWeight x := by
  have hsin : sine (7 / 5) = Real.sin (π / 5) := by
    unfold sine
    rw [show 2 * π * (7 / 5) = (π - π / 5) + 2 * π by ring,
      Real.sin_add_two_pi, Real.sin_pi_sub]
  have hneg : sine (-(7 / 5)) = -sine (7 / 5) := by simp [sine, mul_neg]
  have hcube : (π / 5) ^ 3 ≤ (63 / 100 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d2]) 3
  have hlo : (11 / 20 : ℝ) ≤ Real.sin (π / 5) := by
    linarith only [Real.pi_gt_three, hcube, Real.sin_ge_sub_cube (show 0 ≤ π / 5 by positivity)]
  have hratio : (11 / 63 : ℝ) ≤ Real.sin (π / 5) / π := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_d2]
  have hquad : Continuous (fun x : ℝ ↦ x ^ 2) := by fun_prop
  have hcos : Continuous (fun x ↦ (3 / 8) * cosine x) := by unfold cosine; fun_prop
  unfold cosineWeight
  rw [intervalIntegral.integral_add (hquad.intervalIntegrable _ _) (hcos.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cosine, hneg, hsin, integral_pow]
  rw [show (Real.sin (π / 5) - -Real.sin (π / 5)) / (2 * π) =
      Real.sin (π / 5) / π by ring]
  linarith only [hratio]

private theorem pairScore_lower : (713 / 2000 : ℝ) ≤ continuousPairScore f g := by
  by_contra! hlt
  have hq (x : ℝ) : continuousOverlap f g x ≤ (713 / 2000 : ℝ) := by
    by_cases hx : x ∈ continuousTranslationInterval
    · exact (le_csSup h.overlapValues_bddAbove ⟨x, hx, rfl⟩).trans hlt.le
    · rw [overlap_zero h x hx]
      norm_num
  let m := (∫ x, g x * x) - (∫ x, f x * x)
  by_cases hm : |m| ≤ 3 / 20
  · -- Add the nonpositive Fourier coefficient when the mean difference is small.
    have hm₂ : m ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := by
      rw [← sq_abs m]
      exact pow_le_pow_left₀ (abs_nonneg m) hm 2
    have hcut : (317 / 200 : ℝ) ≤ cosineWeight (7 / 5) := by
      unfold cosineWeight cosine
      linarith [Real.neg_one_le_cos (2 * π * (7 / 5))]
    have hlow := overlap_weight_lower h (w := cosineWeight)
      (by unfold cosineWeight cosine; fun_prop) hq (by norm_num : -(7 / 5 : ℝ) ≤ 7 / 5)
      cosineWeight_cutoff.1 cosineWeight_cutoff.2
    have hcos : Continuous cosine := by unfold cosine; fun_prop
    have hquad : Continuous (fun x : ℝ ↦ x ^ 2) := by fun_prop
    have hw : (∫ x, continuousOverlap f g x * cosineWeight x) =
        2 / 3 + m ^ 2 / 2 + (3 / 8) * (∫ x, continuousOverlap f g x * cosine x) := by
      have he := overlap_quadratic h 0
      change (∫ x, continuousOverlap f g x * (x - 0) ^ 2) =
        2 / 3 + m ^ 2 / 2 - 2 * 0 * m + 0 ^ 2 at he
      norm_num at he
      simp_rw [cosineWeight, mul_add, mul_left_comm (continuousOverlap f g _)]
      rw [integral_add (overlap_weight h hquad).1
        ((overlap_weight h hcos).1.const_mul (3 / 8)), integral_const_mul, he]
    rw [hw] at hlow
    linarith only [hlow, hcut, integral_cosineWeight_lower, hm₂, overlap_cosine_nonpos h]
  · -- With a large mean difference, the second moment about the mean suffices.
    have hm₂ : (3 / 20 : ℝ) ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs m]
      exact pow_le_pow_left₀ (by norm_num) (le_of_not_ge hm) 2
    have hab : m - 7 / 5 ≤ m + 7 / 5 := by linarith
    have hin (x : ℝ) (hx : x ∈ Icc (m - 7 / 5) (m + 7 / 5)) :
        (x - m) ^ 2 ≤ (7 / 5 : ℝ) ^ 2 := by
      rw [← sq_abs (x - m)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) 2
    have hout (x : ℝ) (hx : x ∉ Icc (m - 7 / 5) (m + 7 / 5)) :
        (7 / 5 : ℝ) ^ 2 ≤ (x - m) ^ 2 := by
      rw [← sq_abs (x - m)]
      apply pow_le_pow_left₀ (by norm_num) ?_ 2
      by_contra! hlt'
      obtain ⟨h₁, h₂⟩ := abs_le.mp hlt'.le
      exact hx ⟨by linarith, by linarith⟩
    have hlow := overlap_weight_lower h (w := fun x ↦ (x - m) ^ 2) (by fun_prop) hq hab hin hout
    have hint : (∫ x in (m - 7 / 5)..(m + 7 / 5), (x - m) ^ 2) = (686 / 375 : ℝ) := by
      simp only [sub_eq_add_neg]
      rw [intervalIntegral.integral_comp_add_right (fun x : ℝ ↦ x ^ 2) (-m),
        show m + -(7 / 5) + -m = -(7 / 5) by ring, show m + 7 / 5 + -m = 7 / 5 by ring,
        integral_pow]
      norm_num
    have hquad := overlap_quadratic h m
    change (∫ x, continuousOverlap f g x * (x - m) ^ 2) =
      2 / 3 + m ^ 2 / 2 - 2 * m * m + m ^ 2 at hquad
    rw [hint, hquad, show (m + 7 / 5) - (m - 7 / 5) = 14 / 5 by ring] at hlow
    linarith only [hlow, hm₂]

end Moser

/-- **Moser's lower bound $C_{1b} \ge \sqrt{4 - \sqrt{15}}$.** The continuous Erdős minimum-overlap
constant $C_{1b}$ satisfies $\sqrt{4 - \sqrt{15}} \le C_{1b}$.

Source: Moser 1959 and Optimization Problems 1b. -/
theorem lowerBound_M1959_holds : lowerBound_M1959 := by
  apply continuousMinimumOverlapConstant_isGreatest.2
  intro f g h
  refine le_trans ?_ (Moser.pairScore_lower h)
  apply (Real.sqrt_le_iff).2
  refine ⟨by norm_num, ?_⟩
  have hroot : (4 - (713 / 2000) ^ 2 : ℝ) ≤ Real.sqrt 15 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  linarith

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
