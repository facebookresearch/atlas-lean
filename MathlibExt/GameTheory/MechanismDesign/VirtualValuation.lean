/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.SingleParameter
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Expected revenue as expected virtual surplus

A bidder's value `t` is distributed on `[a, b]` with a continuous positive density `f` and
distribution function `F t = ∫_a^t f`. Myerson's *virtual valuation* is
`φ(t) = t - (1 - F t) / f t` (Myerson 1981, (5.1), without revision effects). For every
mechanism that is incentive compatible on `[a, b]`, in the interim form of
`SingleParameter`, the expected payment equals the expected virtual surplus minus the utility
of the lowest type:

`∫_a^b P(t) f(t) dt = ∫_a^b φ(t) Q(t) f(t) dt - U(a)`

(Myerson 1981, (4.10), for one bidder). Summed over bidders this is the identity (4.12) that
reduces optimal auction design to the pointwise maximization of virtual surplus. Consequently
no individually rational incentive-compatible mechanism with allocation probabilities in
`[0, 1]` earns more than `∫_a^b max(φ f, 0)` from the bidder (Myerson 1981, Lemma 3 and §5, with
a single bidder and seller value `t₀ = 0`).

The proof integrates by parts: with `G t = ∫_a^t Q`, the function `G (F - 1)` has derivative
`Q (F - 1) + G f` off the countable set of discontinuities of the monotone function `Q`, so
`∫_a^b G f = ∫_a^b Q (1 - F)`; this replaces the exchange of integrals in Myerson's (4.10).

## Main results

* `integral_payment_mul_density`: the revenue identity (4.10).
* `integral_payment_mul_density_le`: the revenue bound `∫ P f ≤ ∫ max(φ f, 0)`.

## References

* R. B. Myerson, "Optimal auction design", *Math. Oper. Res.* 6(1) (1981), 58–73, (4.10),
  Lemma 3, (5.1) and §5.
-/

namespace MathlibExt.GameTheory.MechanismDesign.SingleParameter

open Set MeasureTheory Filter Topology

variable {Q P f : ℝ → ℝ} {a b t : ℝ}

/-- **Virtual valuation.** For the density `f` of values on `[a, b]`, the virtual valuation
`φ(t) = t - (1 - F t) / f t` with `F t = ∫_a^t f` (Myerson 1981, (5.1) with zero revision
effects). -/
noncomputable def virtualValue (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  t - (1 - ∫ s in a..t, f s) / f t

/-- **Virtual surplus density.** Where `f t ≠ 0`, `φ(t) f(t) = t f(t) - (1 - F t)`. -/
theorem virtualValue_mul_density (hft : f t ≠ 0) :
    virtualValue f a t * f t = t * f t - (1 - ∫ s in a..t, f s) := by
  unfold virtualValue
  field_simp

/- Interval integrability transferred along equality on `[a, b]`. -/
private theorem intervalIntegrable_of_eqOn {g h : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (heq : EqOn g h (Icc a b)) :
    IntervalIntegrable h volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hg ⊢
  exact hg.congr_fun heq measurableSet_Icc

/-- **Myerson's revenue identity (4.10).** Let the bidder's value have a continuous positive
density `f` on `[a, b]` with `∫_a^b f = 1`, and let `(Q, P)` be incentive compatible on
`[a, b]`. Then the expected payment is the expected virtual surplus minus the utility of the
lowest type: `∫_a^b P f = ∫_a^b φ Q f - U a` (Myerson 1981, (4.10), for one bidder without
revision effects). -/
theorem integral_payment_mul_density (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfpos : ∀ t ∈ Icc a b, 0 < f t) (hf1 : ∫ t in a..b, f t = 1)
    (h : IsIncentiveCompatibleOn Q P a b) :
    ∫ t in a..b, P t * f t =
      (∫ t in a..b, virtualValue f a t * Q t * f t) - truthfulUtility Q P a := by
  have hle := hab.le
  have hQm := h.allocation_monotoneOn
  -- a monotone extension of `Q` to the whole line
  set Qt : ℝ → ℝ := fun x => Q (projIcc a b hle x) with hQt
  have hQtmono : Monotone Qt := fun x y hxy =>
    hQm (projIcc a b hle x).2 (projIcc a b hle y).2 (monotone_projIcc hle hxy)
  have hQeq : EqOn Q Qt (Icc a b) := fun x hx => by simp [hQt, projIcc_of_mem hle hx]
  have hQtint : ∀ u v, IntervalIntegrable Qt volume u v := fun u v => hQtmono.intervalIntegrable
  set G : ℝ → ℝ := fun x => ∫ s in a..x, Qt s with hG
  set F : ℝ → ℝ := fun x => ∫ s in a..x, f s with hF
  have hfint : IntegrableOn f (uIcc a b) := by
    rw [uIcc_of_le hle]; exact hfc.integrableOn_Icc
  have hFc : ContinuousOn F (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval hfint
    rwa [uIcc_of_le hle] at this
  have hGc : Continuous G := intervalIntegral.continuous_primitive hQtint a
  have hfii : ∀ x ∈ Icc a b, IntervalIntegrable f volume a x := fun x hx =>
    (hfc.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  -- integration by parts: `∫ (Qt (F - 1) + G f) = 0`
  have hparts : ∫ t in a..b, (Qt t * (F t - 1) + G t * f t) = 0 := by
    have hcount : {x | ¬ContinuousAt Qt x}.Countable := hQtmono.countable_not_continuousAt
    have hderiv : ∀ x ∈ Ioo a b \ {x | ¬ContinuousAt Qt x},
        HasDerivAt (fun t => G t * (F t - 1)) (Qt x * (F x - 1) + G x * f x) x := by
      rintro x ⟨hx, hxc'⟩
      have hxc : ContinuousAt Qt x := not_not.mp hxc'
      have hGd : HasDerivAt G (Qt x) x :=
        intervalIntegral.integral_hasDerivAt_right (hQtint a x)
          (hQtmono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hxc
      have hFd : HasDerivAt F (f x) x :=
        intervalIntegral.integral_hasDerivAt_right (hfii x (Ioo_subset_Icc_self hx))
          (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hfc.mono Ioo_subset_Icc_self) x hx)
          (hfc.continuousAt (Icc_mem_nhds hx.1 hx.2))
      exact HasDerivAt.mul hGd (hFd.sub_const 1)
    have hint : IntervalIntegrable (fun t => Qt t * (F t - 1) + G t * f t) volume a b := by
      refine IntervalIntegrable.add ?_ ?_
      · exact (hQtint a b).mul_continuousOn
          (by rw [uIcc_of_le hle]; exact hFc.sub continuousOn_const)
      · refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hle]; exact hGc.continuousOn.mul hfc
    rw [integral_eq_of_hasDerivAt_off_countable_of_le _ _ hle hcount
      ((hGc.continuousOn.mul (hFc.sub continuousOn_const))) hderiv hint]
    simp [hG, hF, hf1]
  -- the pieces are integrable
  have hiQF : IntervalIntegrable (fun t => Qt t * (F t - 1)) volume a b :=
    (hQtint a b).mul_continuousOn (by rw [uIcc_of_le hle]; exact hFc.sub continuousOn_const)
  have hiGf : IntervalIntegrable (fun t => G t * f t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]; exact hGc.continuousOn.mul hfc
  have hitQf : IntervalIntegrable (fun t => Qt t * (t * f t)) volume a b :=
    (hQtint a b).mul_continuousOn (by
      rw [uIcc_of_le hle]; exact continuousOn_id.mul hfc)
  have hif : IntervalIntegrable f volume a b := hfii b ⟨hle, le_rfl⟩
  have hsplit := intervalIntegral.integral_add hiQF hiGf
  rw [hparts] at hsplit
  -- the left side
  have hL : ∫ t in a..b, P t * f t =
      (∫ t in a..b, Qt t * (t * f t)) - (∫ t in a..b, G t * f t) -
        truthfulUtility Q P a * ∫ t in a..b, f t := by
    have hcongr : EqOn (fun t => P t * f t)
        (fun t => Qt t * (t * f t) - G t * f t - truthfulUtility Q P a * f t) (uIcc a b) := by
      intro t ht
      rw [uIcc_of_le hle] at ht
      have hGt : ∫ x in a..t, Q x = G t := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le ht.1] at hx
        exact hQeq ⟨hx.1, hx.2.trans ht.2⟩
      simp only
      rw [h.payment_formula ht, hGt, ← hQeq ht]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub (hitQf.sub hiGf)
      (hif.const_mul _), intervalIntegral.integral_sub hitQf hiGf,
      intervalIntegral.integral_const_mul]
  -- the right side
  have hR : ∫ t in a..b, virtualValue f a t * Q t * f t =
      (∫ t in a..b, Qt t * (t * f t)) + ∫ t in a..b, Qt t * (F t - 1) := by
    have hcongr : EqOn (fun t => virtualValue f a t * Q t * f t)
        (fun t => Qt t * (t * f t) + Qt t * (F t - 1)) (uIcc a b) := by
      intro t ht
      rw [uIcc_of_le hle] at ht
      have hv := virtualValue_mul_density (a := a) (hfpos t ht).ne'
      simp only [hF]
      rw [← hQeq ht, mul_right_comm, hv]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add hitQf hiQF]
  rw [hL, hR, hf1]
  linarith

/-- **Revenue bound from a single bidder.** Under the hypotheses of
`integral_payment_mul_density`, if moreover `0 ≤ Q ≤ 1` on `[a, b]` (a probability of sale) and
the lowest type gets `U a ≥ 0`, the expected payment is at most `∫_a^b max(φ f, 0)` (Myerson
1981, Lemma 3 and §5 for one bidder and seller value `t₀ = 0`: selling exactly to the types with
nonnegative virtual valuation maximizes the expected virtual surplus). -/
theorem integral_payment_mul_density_le (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfpos : ∀ t ∈ Icc a b, 0 < f t) (hf1 : ∫ t in a..b, f t = 1)
    (h : IsIncentiveCompatibleOn Q P a b) (hQ : ∀ t ∈ Icc a b, Q t ∈ Icc (0 : ℝ) 1)
    (hU : 0 ≤ truthfulUtility Q P a) :
    ∫ t in a..b, P t * f t ≤ ∫ t in a..b, max (virtualValue f a t * f t) 0 := by
  have hle := hab.le
  rw [integral_payment_mul_density hab hfc hfpos hf1 h]
  -- `φ f` agrees on `[a, b]` with a continuous function
  have hFc : ContinuousOn (fun t => ∫ s in a..t, f s) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn f (uIcc a b) by rw [uIcc_of_le hle]; exact hfc.integrableOn_Icc)
    rwa [uIcc_of_le hle] at this
  have hc : ContinuousOn (fun t => t * f t - (1 - ∫ s in a..t, f s)) (Icc a b) :=
    (continuousOn_id.mul hfc).sub (continuousOn_const.sub hFc)
  have heq : EqOn (fun t => t * f t - (1 - ∫ s in a..t, f s)) (fun t => virtualValue f a t * f t)
      (Icc a b) := fun t ht => (virtualValue_mul_density (hfpos t ht).ne').symm
  have hmax : IntervalIntegrable (fun t => max (virtualValue f a t * f t) 0) volume a b :=
    intervalIntegrable_of_eqOn hle
      ((hc.sup (continuousOn_const (c := (0 : ℝ)))).intervalIntegrable_of_Icc hle)
      (fun t ht => congrArg (fun x => max x (0 : ℝ)) (heq ht))
  have hQi : IntervalIntegrable Q volume a b :=
    MonotoneOn.intervalIntegrable (by rw [uIcc_of_le hle]; exact h.allocation_monotoneOn)
  have hφQf : IntervalIntegrable (fun t => virtualValue f a t * Q t * f t) volume a b := by
    have := hQi.mul_continuousOn (g := fun t => t * f t - (1 - ∫ s in a..t, f s))
      (by rw [uIcc_of_le hle]; exact hc)
    refine intervalIntegrable_of_eqOn hle this fun t ht => ?_
    have e : t * f t - (1 - ∫ s in a..t, f s) = virtualValue f a t * f t := heq ht
    change Q t * (t * f t - (1 - ∫ s in a..t, f s)) = virtualValue f a t * Q t * f t
    rw [e]; ring
  have hmono : ∫ t in a..b, virtualValue f a t * Q t * f t ≤
      ∫ t in a..b, max (virtualValue f a t * f t) 0 := by
    refine intervalIntegral.integral_mono_on hle hφQf hmax fun t ht => ?_
    obtain ⟨hq0, hq1⟩ := hQ t ht
    have e : virtualValue f a t * Q t * f t = (virtualValue f a t * f t) * Q t := by ring
    rw [e]
    rcases le_total 0 (virtualValue f a t * f t) with hx | hx
    · exact (mul_le_of_le_one_right hx hq1).trans (le_max_left _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg hx hq0).trans (le_max_right _ _)
  linarith

/-! ### Posted prices and the optimal mechanism for one bidder -/

/-- **Posted-price allocation.** The bidder gets the object exactly when its value exceeds the
price `r`. -/
noncomputable def postedPriceAlloc (r t : ℝ) : ℝ := if r < t then 1 else 0

/-- **Posted-price payment.** The bidder pays the price `r` exactly when it gets the object. -/
noncomputable def postedPricePayment (r t : ℝ) : ℝ := if r < t then r else 0

/-- **Posted-price allocations are monotone.** -/
theorem monotone_postedPriceAlloc (r : ℝ) : Monotone (postedPriceAlloc r) := by
  intro s t hst
  unfold postedPriceAlloc
  by_cases h1 : r < s
  · have h2 : r < t := h1.trans_le hst
    simp [h1, h2]
  · by_cases h2 : r < t <;> simp [h1, h2]

/-- **Posted prices are incentive compatible.** A posted price `r` is incentive compatible on
every interval of values. -/
theorem isIncentiveCompatibleOn_postedPrice (r a b : ℝ) :
    IsIncentiveCompatibleOn (postedPriceAlloc r) (postedPricePayment r) a b := by
  intro s _ t _
  unfold truthfulUtility postedPriceAlloc postedPricePayment
  split_ifs with h1 h2 h2 <;> simp only [mul_one, mul_zero] <;> linarith

/-- **Posted-price payments.** The payment is the price times the allocation. -/
theorem postedPricePayment_mul (r t x : ℝ) :
    postedPricePayment r t * x = r * (postedPriceAlloc r t * x) := by
  unfold postedPricePayment postedPriceAlloc
  split_ifs <;> ring

/-- **Revenue of a posted price.** If the value has a continuous density `f` on `[a, b]` with
`∫_a^b f = 1` and `r ∈ [a, b]`, the posted price `r` earns `r (1 - F r)` in expectation. -/
theorem integral_postedPricePayment_mul_density {r : ℝ} (hr : r ∈ Icc a b)
    (hfc : ContinuousOn f (Icc a b)) (hf1 : ∫ t in a..b, f t = 1) :
    ∫ t in a..b, postedPricePayment r t * f t = r * (1 - ∫ t in a..r, f t) := by
  have hab : a ≤ b := hr.1.trans hr.2
  simp_rw [postedPricePayment_mul]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hfi : ∀ c d, a ≤ c → c ≤ d → d ≤ b → IntervalIntegrable f volume c d :=
    fun c d hac hcd hdb => (hfc.mono (Icc_subset_Icc hac hdb)).intervalIntegrable_of_Icc hcd
  have hQfi : ∀ c d, a ≤ c → c ≤ d → d ≤ b →
      IntervalIntegrable (fun t => postedPriceAlloc r t * f t) volume c d :=
    fun c d hac hcd hdb => (monotone_postedPriceAlloc r).intervalIntegrable.mul_continuousOn
      (by rw [uIcc_of_le hcd]; exact hfc.mono (Icc_subset_Icc hac hdb))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hQfi a r le_rfl hr.1 hr.2)
    (hQfi r b hr.1 hr.2 le_rfl)]
  have h1 : ∫ t in a..r, postedPriceAlloc r t * f t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le hr.1] at ht
      simp [postedPriceAlloc, not_lt.2 ht.2]
  have h2 : ∫ t in r..b, postedPriceAlloc r t * f t = ∫ t in r..b, f t := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hr.2] at ht
    simp [postedPriceAlloc, ht.1]
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hfi a r le_rfl hr.1 hr.2)
    (hfi r b hr.1 hr.2 le_rfl)
  rw [hf1] at h3
  rw [h1, h2]
  linarith

/-- **The optimal mechanism for one bidder.** Let the value have a continuous positive density
`f` on `[a, b]` with `∫_a^b f = 1`, and let `r ∈ [a, b]` separate the values of negative and
nonnegative virtual valuation (`φ ≤ 0` below `r` and `φ ≥ 0` above `r`, as when `φ` is
increasing and `r = φ⁻¹(0)`, or `r = a` when `φ ≥ 0` throughout, or `r = b` when `φ ≤ 0`
throughout). Then the posted price `r` earns at least as much as every
incentive-compatible, individually rational mechanism with allocation probabilities in `[0, 1]`
(Myerson 1981, §5, for one bidder and seller value `t₀ = 0`: the optimal auction sells exactly to
the types with nonnegative virtual valuation, at the lowest winning bid `r`). -/
theorem integral_payment_mul_density_le_postedPrice (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfpos : ∀ t ∈ Icc a b, 0 < f t)
    (hf1 : ∫ t in a..b, f t = 1) {r : ℝ} (hr : r ∈ Icc a b)
    (hneg : ∀ t ∈ Icc a b, t < r → virtualValue f a t ≤ 0)
    (hpos : ∀ t ∈ Icc a b, r < t → 0 ≤ virtualValue f a t)
    (h : IsIncentiveCompatibleOn Q P a b) (hQ : ∀ t ∈ Icc a b, Q t ∈ Icc (0 : ℝ) 1)
    (hU : 0 ≤ truthfulUtility Q P a) :
    ∫ t in a..b, P t * f t ≤ ∫ t in a..b, postedPricePayment r t * f t := by
  have hle := hab.le
  refine (integral_payment_mul_density_le hab hfc hfpos hf1 h hQ hU).trans_eq ?_
  rw [integral_postedPricePayment_mul_density hr hfc hf1]
  set F : ℝ → ℝ := fun x => ∫ s in a..x, f s with hF
  have hFc : ContinuousOn F (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn f (uIcc a b) by rw [uIcc_of_le hle]; exact hfc.integrableOn_Icc)
    rwa [uIcc_of_le hle] at this
  have hc : ContinuousOn (fun t => t * f t - (1 - F t)) (Icc a b) :=
    (continuousOn_id.mul hfc).sub (continuousOn_const.sub hFc)
  have heq : EqOn (fun t => max (t * f t - (1 - F t)) 0)
      (fun t => max (virtualValue f a t * f t) 0) (Icc a b) := fun t ht => by
    simp only [hF, virtualValue_mul_density (a := a) (hfpos t ht).ne']
  have hmax : IntervalIntegrable (fun t => max (virtualValue f a t * f t) 0) volume a b :=
    intervalIntegrable_of_eqOn hle
      ((hc.sup (continuousOn_const (c := (0 : ℝ)))).intervalIntegrable_of_Icc hle) heq
  have hsub : ∀ c d, c ∈ Icc a b → d ∈ Icc a b → uIcc c d ⊆ uIcc a b := fun c d hc hd =>
    uIcc_subset_uIcc (mem_uIcc_of_le hc.1 hc.2) (mem_uIcc_of_le hd.1 hd.2)
  have haI : a ∈ Icc a b := ⟨le_rfl, hle⟩
  have hbI : b ∈ Icc a b := ⟨hle, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hmax.mono_set (hsub a r haI hr)) (hmax.mono_set (hsub r b hr hbI))]
  have h1 : ∫ t in a..r, max (virtualValue f a t * f t) 0 = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [Measure.ae_ne volume r] with t htr ht
      rw [uIoc_of_le hr.1] at ht
      have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.trans hr.2⟩
      have := mul_nonpos_of_nonpos_of_nonneg (hneg t htI (lt_of_le_of_ne ht.2 htr))
        (hfpos t htI).le
      simp [this]
  have h2 : ∫ t in r..b, max (virtualValue f a t * f t) 0 =
      ∫ t in r..b, ((F t - 1) + t * f t) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hr.2] at ht
    have htI : t ∈ Icc a b := ⟨hr.1.trans ht.1.le, ht.2⟩
    have hnn := mul_nonneg (hpos t htI ht.1) (hfpos t htI).le
    rw [max_eq_left hnn, virtualValue_mul_density (hfpos t htI).ne']
    simp only [hF]
    ring
  have h3 : ∫ t in r..b, ((F t - 1) + t * f t) = b * (F b - 1) - r * (F r - 1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t => t * (F t - 1))
      hr.2 (continuousOn_id.mul ((hFc.mono (Icc_subset_Icc hr.1 le_rfl)).sub continuousOn_const))
      (fun x hx => ?_) ?_
    · have hxI : x ∈ Ioo a b := ⟨hr.1.trans_lt hx.1, hx.2⟩
      have hFd : HasDerivAt F (f x) x :=
        intervalIntegral.integral_hasDerivAt_right
          ((hfc.mono (Icc_subset_Icc_right hxI.2.le)).intervalIntegrable_of_Icc hxI.1.le)
          (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hfc.mono Ioo_subset_Icc_self) x
            hxI)
          (hfc.continuousAt (Icc_mem_nhds hxI.1 hxI.2))
      have := HasDerivAt.mul (hasDerivAt_id' x) (hFd.sub_const 1)
      convert this using 1
      ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hr.2]
      exact (((hFc.sub continuousOn_const).add (continuousOn_id.mul hfc)).mono
        (Icc_subset_Icc hr.1 le_rfl))
  rw [h1, h2, h3]
  simp only [hF, hf1]
  ring

end MathlibExt.GameTheory.MechanismDesign.SingleParameter
