/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import MathlibExt.GameTheory.MechanismDesign.SingleParameter

/-! # The Myerson–Satterthwaite theorem

`myerson_satterthwaite` proves that efficient bilateral trade on overlapping value intervals
is incompatible with Bayesian incentive compatibility and interim individual rationality.
The single-parameter envelope formula bounds each trader's utility from below. Integrating
these bounds over both types gives a sum strictly larger than the available gains from trade.
-/

namespace MathlibExt.GameTheory.MyersonSatterthwaiteWanted

open Set MeasureTheory MathlibExt.GameTheory.MechanismDesign.SingleParameter

/- Two utilities with the same supporting slopes have the same increments. -/
private theorem rent_bound {a b e t : ℝ} {Q U G : ℝ → ℝ}
    (hU : ∀ s ∈ Icc a b, ∀ v ∈ Icc a b, U s + (v - s) * Q s ≤ U v)
    (hG : ∀ s ∈ Icc a b, ∀ v ∈ Icc a b, G s + (v - s) * Q s ≤ G v)
    (he : e ∈ Icc a b) (ht : t ∈ Icc a b) (hir : 0 ≤ U e) :
    G t - G e ≤ U t := by
  have envelope (V : ℝ → ℝ)
      (hV : ∀ s ∈ Icc a b, ∀ v ∈ Icc a b, V s + (v - s) * Q s ≤ V v)
      (v : ℝ) (hv : v ∈ Icc a b) : V v = V a + ∫ y in a..v, Q y := by
    let P s := s * Q s - V s
    have h : IsIncentiveCompatibleOn Q P a b := by
      rw [isIncentiveCompatibleOn_iff_utility]
      simpa [P, truthfulUtility] using hV
    simpa [P, truthfulUtility] using h.envelope_formula hv
  linarith [envelope U hU e he, envelope U hU t ht, envelope G hG e he, envelope G hG t ht]

/- Here u, q and g already include the other trader's density. The benchmark g has the
same supporting allocation q as the truthful utility u. Anchor their difference at e. -/
private theorem interim_bound {a b c d e : ℝ} {u q g : ℝ → ℝ → ℝ} (hcd : c ≤ d)
    (hu : ∀ s ∈ Icc a b, IntervalIntegrable (u s) volume c d)
    (hq : ∀ s ∈ Icc a b, IntervalIntegrable (q s) volume c d)
    (hg : ∀ s ∈ Icc a b, IntervalIntegrable (g s) volume c d)
    (hic : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (∫ y in c..d, u s y + (t - s) * q s y) ≤ ∫ y in c..d, u t y)
    (hsupport : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ y ∈ Icc c d,
      g s y + (t - s) * q s y ≤ g t y)
    (he : e ∈ Icc a b) (hir : 0 ≤ ∫ y in c..d, u e y) (t : ℝ) (ht : t ∈ Icc a b) :
    0 ≤ ∫ y in c..d, u t y - g t y + g e y := by
  rw [intervalIntegral.integral_add ((hu t ht).sub (hg t ht)) (hg e he),
    intervalIntegral.integral_sub (hu t ht) (hg t ht)]
  have bound := rent_bound (Q := fun s => ∫ y in c..d, q s y)
    (U := fun s => ∫ y in c..d, u s y) (G := fun s => ∫ y in c..d, g s y)
    (a := a) (b := b) (e := e) (t := t) (by
      intro s hs v hv
      simpa only [intervalIntegral.integral_add (hu s hs) ((hq s hs).const_mul _),
        intervalIntegral.integral_const_mul] using hic s hs v hv) (by
      intro s hs v hv
      have h := intervalIntegral.integral_mono_on hcd
        ((hg s hs).add ((hq s hs).const_mul (v - s))) (hg v hv) (hsupport s hs v hv)
      simpa only [intervalIntegral.integral_add (hg s hs) ((hq s hs).const_mul _),
        intervalIntegral.integral_const_mul] using h) he ht hir
  linarith

private def gain (s b : ℝ) : ℝ := max (b - s) 0

private theorem trade_le_gain {s b q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (b - s) * q ≤ gain s b := by
  rcases le_total s b with h | h
  · simpa [gain, max_eq_left (sub_nonneg.mpr h)] using
      mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr h)
  · simpa [gain, max_eq_right (sub_nonpos.mpr h)] using
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hq.1

private theorem efficient_gain {s b q : ℝ}
    (h : (s < b → q = 1) ∧ (b < s → q = 0)) : gain s b = (b - s) * q := by
  rcases lt_trichotomy s b with hlt | rfl | hgt
  · simp [gain, h.1 hlt, max_eq_left (sub_nonneg.mpr hlt.le)]
  · simp [gain]
  · simp [gain, h.2 hgt, max_eq_right (sub_nonpos.mpr hgt.le)]

private theorem integrableOn_prob {α : Type*} [MeasureSpace α]
    {K : Set α} {p : α → ℝ} (hK : MeasurableSet K) (hfin : volume K < ⊤)
    (hm : Measurable p) (hp : ∀ z ∈ K, p z ∈ Icc (0 : ℝ) 1) : IntegrableOn p K := by
  apply IntegrableOn.of_bound hfin hm.aestronglyMeasurable 1
  rw [ae_restrict_iff' hK]
  exact Filter.Eventually.of_forall fun z hz => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hp z hz).1] using (hp z hz).2

/- Fubini lifts an interim lower bound to a lower bound on the joint integral. -/
private theorem joint_nonneg {a b c d : ℝ} {F : ℝ × ℝ → ℝ}
    (hcd : c ≤ d) (hF : IntegrableOn F (Icc a b ×ˢ Icc c d))
    (h : ∀ s ∈ Icc a b, 0 ≤ ∫ y in c..d, F (s, y)) :
    0 ≤ ∫ z in Icc a b ×ˢ Icc c d, F z := by
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [setIntegral_prod F hF]
  apply setIntegral_nonneg measurableSet_Icc
  intro s hs
  simpa only [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc] using h s hs

/- Weighted difference between the actual utility and the benchmark rent g(t,y) - g(e,y).
Both signs of the allocation and cash flow are allowed, so this applies to either trader. -/
private def excess (m q g : ℝ → ℝ → ℝ) (e : ℝ) (f h : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (m z.1 z.2 + z.1 * q z.1 z.2 - g z.1 z.2 + g e z.2) * h z.2 * f z.1

private theorem joint_rent {a b c d e : ℝ} {m q g : ℝ → ℝ → ℝ} {f h : ℝ → ℝ}
    (hcd : c ≤ d) (he : e ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hh : ContinuousOn h (Icc c d))
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t) (hhpos : ∀ y ∈ Icc c d, 0 ≤ h y)
    (hg : Continuous g.uncurry)
    (hm : IntegrableOn m.uncurry (Icc a b ×ˢ Icc c d))
    (hq : IntegrableOn q.uncurry (Icc a b ×ˢ Icc c d))
    (hms : ∀ t ∈ Icc a b, IntervalIntegrable (m t) volume c d)
    (hqs : ∀ t ∈ Icc a b, IntervalIntegrable (q t) volume c d)
    (hic : ∀ t ∈ Icc a b, ∀ s ∈ Icc a b,
      (∫ y in c..d, (m s y + t * q s y) * h y) ≤ ∫ y in c..d, (m t y + t * q t y) * h y)
    (hsupport : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ y ∈ Icc c d,
      g s y + (t - s) * q s y ≤ g t y)
    (hir : 0 ≤ ∫ y in c..d, (m e y + e * q e y) * h y) :
    IntegrableOn (excess m q g e f h) (Icc a b ×ˢ Icc c d) ∧
      0 ≤ ∫ z in Icc a b ×ˢ Icc c d, excess m q g e f h z := by
  have hK := (isCompact_Icc (α := ℝ) (a := a) (b := b)).prod
    (isCompact_Icc (α := ℝ) (a := c) (b := d))
  have hge : Continuous (fun z : ℝ × ℝ => g e z.2) :=
    hg.comp (continuous_const.prodMk continuous_snd)
  have hint : IntegrableOn (excess m q g e f h) (Icc a b ×ˢ Icc c d) := by
    apply IntegrableOn.mul_continuousOn _ (hf.comp continuous_fst.continuousOn mapsTo_fst_prod) hK
    apply IntegrableOn.mul_continuousOn _ (hh.comp continuous_snd.continuousOn mapsTo_snd_prod) hK
    exact ((hm.add (hq.continuousOn_mul continuous_fst.continuousOn hK)).sub
      (hg.continuousOn.integrableOn_compact hK)).add (hge.continuousOn.integrableOn_compact hK)
  refine ⟨hint, joint_nonneg hcd hint ?_⟩
  intro t ht
  have hh' : ContinuousOn h (uIcc c d) := by rwa [uIcc_of_le hcd]
  let U s y := (m s y + s * q s y) * h y
  let Q s y := q s y * h y
  let G s y := g s y * h y
  have hbound := interim_bound (u := U) (q := Q) (g := G) hcd
    (fun s hs => ((hms s hs).add ((hqs s hs).const_mul s)).mul_continuousOn hh')
    (fun s hs => (hqs s hs).mul_continuousOn hh')
    (fun s _ => ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      (μ := volume)).mul_continuousOn hh') (by
      intro s hs v hv
      convert hic v hv s hs using 1
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [U, Q]
      ring) (by
      intro s hs v hv y hy
      simpa only [G, Q, add_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (hsupport s hs v hv y hy) (hhpos y hy)) he hir t ht
  calc
    0 ≤ (∫ y in c..d, U t y - G t y + G e y) * f t := mul_nonneg hbound (hfpos t ht)
    _ = ∫ y in c..d, excess m q g e f h (t, y) := by
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [U, G, excess]
      ring

private theorem section_prob {a b : ℝ} {p : ℝ → ℝ} (hab : a ≤ b) (hm : Measurable p)
    (hp : ∀ y ∈ Icc a b, p y ∈ Icc (0 : ℝ) 1) : IntervalIntegrable p volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (integrableOn_prob measurableSet_Icc isCompact_Icc.measure_lt_top hm hp)

/- After the endpoint rents have been subtracted, the residual gain is the length of the
part of [s,b] lying between the lowest buyer type and the highest seller type. -/
private def residual (hi lo : ℝ) (f h : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (gain z.1 z.2 - gain hi z.2 - gain z.1 lo) * h z.2 * f z.1

private theorem integral_residual_pos {a b c d : ℝ} {f h : ℝ → ℝ}
    (hab : a < b) (hcd : c < d) (hcb : c < b) (had : a < d)
    (hf : ContinuousOn f (Icc a b)) (hh : ContinuousOn h (Icc c d))
    (hfpos : ∀ s ∈ Icc a b, 0 < f s) (hhpos : ∀ v ∈ Icc c d, 0 < h v) :
    0 < ∫ z in Icc a b ×ˢ Icc c d, residual b c f h z := by
  have hint : IntegrableOn (residual b c f h) (Icc a b ×ˢ Icc c d) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply ContinuousOn.mul _ (hf.comp continuous_fst.continuousOn mapsTo_fst_prod)
    apply ContinuousOn.mul _ (hh.comp continuous_snd.continuousOn mapsTo_snd_prod)
    unfold gain
    fun_prop
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ hint).2
  · obtain ⟨t, hlt, htu⟩ := exists_between
      (max_lt (lt_min hab had) (lt_min hcb hcd))
    let B := Ioo (max a c) t ×ˢ Ioo t (min b d)
    have hB : 0 < volume B := (isOpen_Ioo.prod isOpen_Ioo).measure_pos _
      ((nonempty_Ioo.2 hlt).prod (nonempty_Ioo.2 htu))
    refine hB.trans_le (measure_mono ?_)
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hsv : s < v := hs.2.trans hv.1
    obtain ⟨has, hcs⟩ := max_lt_iff.mp hs.1
    obtain ⟨hvb, hvd⟩ := lt_min_iff.mp hv.2
    have hs' : s ∈ Icc a b := ⟨has.le, (hsv.trans hvb).le⟩
    have hv' : v ∈ Icc c d := ⟨(hcs.trans hsv).le, hvd.le⟩
    refine ⟨Function.mem_support.mpr (ne_of_gt ?_), hs', hv'⟩
    simp only [residual, gain, max_eq_left (sub_nonneg.mpr hsv.le),
      max_eq_right (sub_nonpos.mpr hvb.le), max_eq_right (sub_nonpos.mpr hcs.le), sub_zero]
    exact mul_pos (mul_pos (sub_pos.mpr hsv) (hhpos v hv')) (hfpos s hs')
  · rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
    filter_upwards with z hz
    apply mul_nonneg (mul_nonneg _ (hhpos _ hz.2).le) (hfpos _ hz.1).le
    have hs := hz.1.2
    have hv := hz.2.1
    simp only [gain, max_def]
    split_ifs <;> linarith

-- Positive rescaling of either density preserves the inequalities used in the proof.
set_option linter.unusedVariables false in
/-- **Myerson–Satterthwaite theorem.** Let the seller's value have a continuous positive
probability density `f₁` on `[a₁, b₁]` and the buyer's value a continuous positive probability
density `f₂` on `[a₂, b₂]`, with `a₂ < b₁` and `a₁ < b₂` (the interiors intersect). Then there is
no trading mechanism `(p, x)`, with `p` a measurable transfer probability and interim payments
defined, that is Bayesian incentive compatible (`hIC₁`, `hIC₂`), interim individually rational
(`hIR₁`, `hIR₂`) and ex post efficient (`heff`) (Myerson and Satterthwaite 1983,
Corollary 1). -/
public theorem myerson_satterthwaite
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hov₁ : a₂ < b₁) (hov₂ : a₁ < b₂)
    {f₁ f₂ : ℝ → ℝ} (hf₁ : ContinuousOn f₁ (Icc a₁ b₁)) (hf₂ : ContinuousOn f₂ (Icc a₂ b₂))
    (hf₁pos : ∀ v ∈ Icc a₁ b₁, 0 < f₁ v) (hf₂pos : ∀ v ∈ Icc a₂ b₂, 0 < f₂ v)
    (hf₁one : ∫ v in a₁..b₁, f₁ v = 1) (hf₂one : ∫ v in a₂..b₂, f₂ v = 1)
    (p x : ℝ → ℝ → ℝ) (hpm : Measurable (Function.uncurry p))
    (hp : ∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂, p v₁ v₂ ∈ Icc (0 : ℝ) 1)
    (hx : IntegrableOn (Function.uncurry x) (Icc a₁ b₁ ×ˢ Icc a₂ b₂))
    (hx₁ : ∀ v₁ ∈ Icc a₁ b₁, IntervalIntegrable (x v₁) volume a₂ b₂)
    (hx₂ : ∀ v₂ ∈ Icc a₂ b₂, IntervalIntegrable (fun v₁ => x v₁ v₂) volume a₁ b₁)
    (hIC₁ : ∀ v₁ ∈ Icc a₁ b₁, ∀ w₁ ∈ Icc a₁ b₁,
      ∫ v₂ in a₂..b₂, (x w₁ v₂ - v₁ * p w₁ v₂) * f₂ v₂ ≤
        ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂)
    (hIC₂ : ∀ v₂ ∈ Icc a₂ b₂, ∀ w₂ ∈ Icc a₂ b₂,
      ∫ v₁ in a₁..b₁, (v₂ * p v₁ w₂ - x v₁ w₂) * f₁ v₁ ≤
        ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁)
    (hIR₁ : ∀ v₁ ∈ Icc a₁ b₁, 0 ≤ ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂)
    (hIR₂ : ∀ v₂ ∈ Icc a₂ b₂, 0 ≤ ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁)
    (heff : ∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂,
      (v₁ < v₂ → p v₁ v₂ = 1) ∧ (v₂ < v₁ → p v₁ v₂ = 0)) :
    False := by
  have hK := (isCompact_Icc (α := ℝ) (a := a₁) (b := b₁)).prod
    (isCompact_Icc (α := ℝ) (a := a₂) (b := b₂))
  have hpint := integrableOn_prob hK.measurableSet hK.measure_lt_top hpm
    (fun z hz => hp z.1 hz.1 z.2 hz.2)
  have hs : b₁ ∈ Icc a₁ b₁ := ⟨h₁.le, le_rfl⟩
  have hb : a₂ ∈ Icc a₂ b₂ := ⟨le_rfl, h₂.le⟩
  -- For the seller the allocation enters utility with a minus sign.
  let S := excess x (fun s v => -p s v) gain b₁ f₁ f₂
  obtain ⟨hSint, hS⟩ : IntegrableOn S (Icc a₁ b₁ ×ˢ Icc a₂ b₂) ∧
      0 ≤ ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, S z := by
    apply joint_rent (m := x) (q := fun s v => -p s v) (g := gain) h₂.le hs hf₁ hf₂
      (fun t ht => (hf₁pos t ht).le) (fun y hy => (hf₂pos y hy).le)
      (by unfold gain Function.uncurry; fun_prop)
      hx hpint.neg hx₁
    · intro s hs'
      exact (section_prob h₂.le (hpm.comp (measurable_const.prodMk measurable_id))
        (hp s hs')).neg
    · simpa only [mul_neg, ← sub_eq_add_neg] using hIC₁
    · intro s hs' t _ v hv
      rw [efficient_gain (heff s hs' v hv)]
      nlinarith only [trade_le_gain (s := t) (b := v) (hp s hs' v hv)]
    · simpa only [mul_neg, ← sub_eq_add_neg] using hIR₁ b₁ hs
  -- For the buyer the allocation is positive and the same transfer is an expense.
  let B := excess (fun v s => -x s v) (fun v s => p s v) (fun v s => gain s v) a₂ f₂ f₁
  obtain ⟨hBint, hB⟩ : IntegrableOn B (Icc a₂ b₂ ×ˢ Icc a₁ b₁) ∧
      0 ≤ ∫ z in Icc a₂ b₂ ×ˢ Icc a₁ b₁, B z := by
    apply joint_rent (m := fun v s => -x s v) (q := fun v s => p s v)
      (g := fun v s => gain s v) h₁.le hb hf₂ hf₁ (fun t ht => (hf₂pos t ht).le)
      (fun y hy => (hf₁pos y hy).le) (by unfold gain Function.uncurry; fun_prop)
      hx.swap.neg hpint.swap (fun v hv => (hx₂ v hv).neg)
    · intro v hv
      exact section_prob h₁.le (hpm.comp (measurable_id.prodMk measurable_const))
        (fun s hs' => hp s hs' v hv)
    · simpa only [sub_eq_add_neg, add_comm] using hIC₂
    · intro v hv w _ s hs'
      rw [efficient_gain (heff s hs' v hv)]
      nlinarith only [trade_le_gain (s := s) (b := w) (hp s hs' v hv)]
    · simpa only [sub_eq_add_neg, add_comm] using hIR₂ a₂ hb
  have hswap : (∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, B z.swap) =
      ∫ z in Icc a₂ b₂ ×ˢ Icc a₁ b₁, B z :=
    setIntegral_prod_swap _ _ _
  have hsum : (∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, S z + B z.swap) =
      -(∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, residual b₁ a₂ f₁ f₂ z) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    dsimp [S, B, excess, residual]
    rw [efficient_gain (heff z.1 hz.1 z.2 hz.2)]
    ring
  have hBswap : IntegrableOn (fun z : ℝ × ℝ => B z.swap) (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := hBint.swap
  rw [integral_add hSint hBswap, hswap] at hsum
  linarith [integral_residual_pos h₁ h₂ hov₁ hov₂ hf₁ hf₂ hf₁pos hf₂pos]

end MathlibExt.GameTheory.MyersonSatterthwaiteWanted
