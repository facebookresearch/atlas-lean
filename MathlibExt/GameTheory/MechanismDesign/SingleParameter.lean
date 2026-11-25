/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Myerson's lemma: incentive compatibility in single-parameter environments

An agent with a one-dimensional private value `t ∈ [a, b]` faces a mechanism that, on the report
`s`, gives it a quantity (an allocation probability) `Q s` and charges it `P s`; with
quasi-linear utility, an agent of value `t` reporting `s` gets `t * Q s - P s`. The mechanism
is *incentive compatible* on `[a, b]` when truthful reporting is optimal for every value.

`Q` and `P` can be read in two ways, and the results below apply to both:

* **Bayesian (interim) form** (Myerson 1981, §§3–4): `Q t` is the probability `Qᵢ(p, t)` that
  bidder `i` of value `t` wins when the others report truthfully, and `P t` its expected
  payment; incentive compatibility is Myerson's (3.5) for bidder `i` without revision effects.
* **Dominant-strategy form** (Nisan 2007, Theorem 9.39; Hartline and Karlin 2007,
  Theorem 13.6): the bids `b₋ᵢ` of the others are fixed and `Q`, `P` are bidder `i`'s allocation
  and payment as functions of its own bid.

## Main results

* `isIncentiveCompatibleOn_iff` (Myerson's lemma): the mechanism is incentive compatible on
  `[a, b]` iff `Q` is monotone on `[a, b]` and the utility `U t = t * Q t - P t` satisfies
  the envelope formula `U t = U a + ∫_a^t Q` (Myerson 1981, Lemma 2, conditions (4.2)–(4.3)).
* `IsIncentiveCompatibleOn.payment_formula`: the payment formula `P t = t * Q t - ∫_a^t Q - U a`.
* `payment_eqOn_of_isIncentiveCompatibleOn`, `setIntegral_payment_eq` (revenue equivalence):
  two incentive-compatible mechanisms with the same allocation rule and the same payment at
  the lowest value have the same payment at every value, hence the same expected payment under
  every distribution of values (the one-bidder form of Myerson 1981, Corollary).
* `isIncentiveCompatibleOn_and_utility_nonneg_iff`: with `Q ≥ 0`, incentive compatibility and
  individual rationality hold iff `Q` is monotone, the envelope formula holds and `U a ≥ 0`
  (Myerson 1981, Lemma 2 for one bidder, without revision effects).

No continuity or differentiability of `Q` is assumed: monotone functions are interval
integrable, and the envelope formula is proved by comparing the two-sided incentive bounds
with Riemann sums over equally spaced partitions, as in Myerson's proof of Lemma 2.

## References

* R. B. Myerson, "Optimal auction design", *Math. Oper. Res.* 6(1) (1981), 58–73, Lemma 2,
  (4.6) and the Corollary (revenue-equivalence theorem).
* N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of
  N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*,
  Cambridge University Press, 2007, Theorem 9.39 and Theorem 9.46.
* J. D. Hartline and A. R. Karlin, "Profit maximization in mechanism design", Chapter 13 of the
  same volume, Theorem 13.6.
-/

namespace MathlibExt.GameTheory.MechanismDesign.SingleParameter

open Set MeasureTheory

variable {Q P : ℝ → ℝ} {a b : ℝ}

/-- **Truthful utility.** The utility `t * Q t - P t` of an agent of value `t` reporting
truthfully to the single-parameter mechanism with allocation `Q` and payment `P`. -/
def truthfulUtility (Q P : ℝ → ℝ) (t : ℝ) : ℝ := t * Q t - P t

/-- **Incentive compatibility on an interval.** The single-parameter mechanism `(Q, P)` is
incentive compatible on `[a, b]`: for all values `s, t ∈ [a, b]`, an agent of value `t` does
not gain by reporting `s`, that is `t * Q s - P s ≤ t * Q t - P t` (Myerson 1981, (3.5) without
revision effects; Hartline and Karlin 2007, Definition 13.5). -/
def IsIncentiveCompatibleOn (Q P : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, t * Q s - P s ≤ truthfulUtility Q P t

/-- **Myerson's inequality (4.6).** Incentive compatibility is equivalent to
`U s + (t - s) * Q s ≤ U t` for all `s, t ∈ [a, b]` (Myerson 1981, (4.6)). -/
theorem isIncentiveCompatibleOn_iff_utility (Q P : ℝ → ℝ) (a b : ℝ) :
    IsIncentiveCompatibleOn Q P a b ↔
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        truthfulUtility Q P s + (t - s) * Q s ≤ truthfulUtility Q P t := by
  have e : ∀ s t, truthfulUtility Q P s + (t - s) * Q s = t * Q s - P s := by
    intro s t; unfold truthfulUtility; ring
  simp only [IsIncentiveCompatibleOn, e]

/-- **Myerson's inequality, applied.** Under incentive compatibility on `[a, b]`,
`U s + (t - s) * Q s ≤ U t` for `s, t ∈ [a, b]`. -/
theorem IsIncentiveCompatibleOn.utility_add_mul_le_utility (h : IsIncentiveCompatibleOn Q P a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    truthfulUtility Q P s + (t - s) * Q s ≤ truthfulUtility Q P t :=
  (isIncentiveCompatibleOn_iff_utility Q P a b).1 h s hs t ht

/-- **Monotonicity of incentive-compatible allocations.** If `(Q, P)` is incentive compatible
on `[a, b]`, then `Q` is monotone on `[a, b]` (Myerson 1981, (4.2); Nisan 2007,
Theorem 9.39 (i)). -/
theorem IsIncentiveCompatibleOn.allocation_monotoneOn (h : IsIncentiveCompatibleOn Q P a b) :
    MonotoneOn Q (Icc a b) := by
  intro s hs t ht hst
  have h1 := h.utility_add_mul_le_utility hs ht
  have h2 := h.utility_add_mul_le_utility ht hs
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  · by_contra hc
    rw [not_le] at hc
    nlinarith

/-- **Two-sided comparison lemma.** If `g` is monotone on `[a, b]` and the increments of `D`
satisfy `|D t - D s| ≤ (g t - g s) * (t - s)` for `a ≤ s ≤ t ≤ b`, then `D b = D a`: summing
over a partition of `[a, b]` into `n` equal pieces bounds `|D b - D a|` by
`(g b - g a) * (b - a) / n`. -/
theorem eq_of_abs_sub_le_mul {D g : ℝ → ℝ} (hab : a ≤ b)
    (hD : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |D t - D s| ≤ (g t - g s) * (t - s)) :
    D b = D a := by
  have key : ∀ n : ℕ, 0 < n → |D b - D a| ≤ (g b - g a) * (b - a) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (b - a) / n with hh
    have h0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hab) hn'.le
    let x : ℕ → ℝ := fun k => a + k * h
    have hx0 : x 0 = a := by simp [x]
    have hxn : x n = b := by
      simp only [x, hh]; field_simp; ring
    have hxmem : ∀ k ≤ n, x k ∈ Icc a b := by
      intro k hk
      have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      refine ⟨by simp only [x]; nlinarith, ?_⟩
      have : (k : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hk' h0
      have hnh : (n : ℝ) * h = b - a := by simp only [hh]; field_simp
      simp only [x]; linarith
    have hstep : ∀ k, x (k + 1) - x k = h := by
      intro k; simp only [x]; push_cast; ring
    have tD : D b - D a = ∑ k ∈ Finset.range n, (D (x (k + 1)) - D (x k)) := by
      rw [Finset.sum_range_sub (fun k => D (x k)) n, hx0, hxn]
    have tg : g b - g a = ∑ k ∈ Finset.range n, (g (x (k + 1)) - g (x k)) := by
      rw [Finset.sum_range_sub (fun k => g (x k)) n, hx0, hxn]
    calc |D b - D a| = |∑ k ∈ Finset.range n, (D (x (k + 1)) - D (x k))| := by rw [tD]
      _ ≤ ∑ k ∈ Finset.range n, |D (x (k + 1)) - D (x k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, (g (x (k + 1)) - g (x k)) * h := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          have := hD (x k) (hxmem k hk'.le) (x (k + 1)) (hxmem (k + 1) hk')
            (by linarith [hstep k])
          rwa [hstep k] at this
      _ = (g b - g a) * (b - a) / n := by
          rw [← Finset.sum_mul, ← tg, hh, mul_div_assoc]
  by_contra hne
  have hpos : 0 < |D b - D a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((g b - g a) * (b - a) / |D b - D a|)
  have hC : 0 ≤ (g b - g a) * (b - a) := by
    have := key 1 one_pos
    simp only [Nat.cast_one, div_one] at this
    exact (abs_nonneg _).trans this
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hC hpos.le) hn
  have hk := key n (by exact_mod_cast hnpos)
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hnpos] at hk
  linarith

private theorem intervalIntegrable_of_monotoneOn (hQ : MonotoneOn Q (Icc a b)) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : IntervalIntegrable Q volume s t := by
  apply MonotoneOn.intervalIntegrable
  refine hQ.mono ?_
  intro x hx
  rcases le_total s t with hst | hst
  · rw [uIcc_of_le hst] at hx; exact ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
  · rw [uIcc_of_ge hst] at hx; exact ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩

/- Integral bounds for a monotone function on `[s, t] ⊆ [a, b]`. -/
private theorem integral_mem_of_monotoneOn (hQ : MonotoneOn Q (Icc a b)) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (t - s) * Q s ≤ ∫ x in s..t, Q x ∧ ∫ x in s..t, Q x ≤ (t - s) * Q t := by
  have hint := intervalIntegrable_of_monotoneOn hQ hs ht
  have hmem : ∀ x ∈ Icc s t, x ∈ Icc a b := fun x hx => ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
  constructor
  · have := intervalIntegral.integral_mono_on hst intervalIntegrable_const hint
      (fun x hx => hQ hs (hmem x hx) hx.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  · have := intervalIntegral.integral_mono_on hst hint intervalIntegrable_const
      (fun x hx => hQ (hmem x hx) ht hx.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this

/-- **Envelope formula.** If `(Q, P)` is incentive compatible on `[a, b]`, then
`U t = U a + ∫_a^t Q` for every `t ∈ [a, b]` (Myerson 1981, (4.3)). -/
theorem IsIncentiveCompatibleOn.envelope_formula (h : IsIncentiveCompatibleOn Q P a b) {t : ℝ}
    (ht : t ∈ Icc a b) : truthfulUtility Q P t = truthfulUtility Q P a + ∫ x in a..t, Q x := by
  have hQ := h.allocation_monotoneOn
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsub : ∀ x ∈ Icc a t, x ∈ Icc a b := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  set D : ℝ → ℝ := fun v => truthfulUtility Q P v - ∫ x in a..v, Q x with hD
  have hDeq : D t = D a := by
    refine eq_of_abs_sub_le_mul (g := Q) ht.1 ?_
    intro u hu v hv huv
    have hu' := hsub u hu
    have hv' := hsub v hv
    have h1 := h.utility_add_mul_le_utility hu' hv'
    have h2 := h.utility_add_mul_le_utility hv' hu'
    obtain ⟨i1, i2⟩ := integral_mem_of_monotoneOn hQ hu' hv' huv
    have hsplit : (∫ x in a..v, Q x) - ∫ x in a..u, Q x = ∫ x in u..v, Q x :=
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_monotoneOn hQ ha hv')
        (intervalIntegrable_of_monotoneOn hQ ha hu')
    simp only [hD]
    rw [abs_le]
    constructor <;> nlinarith
  simp only [hD, intervalIntegral.integral_same, sub_zero] at hDeq
  linarith

/-- **Myerson's lemma.** The single-parameter mechanism `(Q, P)` is incentive compatible on
`[a, b]` if and only if `Q` is monotone on `[a, b]` and `U t = U a + ∫_a^t Q` for every
`t ∈ [a, b]`, where `U t = t * Q t - P t` (Myerson 1981, Lemma 2, conditions (4.2) and (4.3);
Nisan 2007, Theorem 9.39; Hartline and Karlin 2007, Theorem 13.6). No regularity of `Q` beyond
monotonicity is needed. -/
theorem isIncentiveCompatibleOn_iff :
    IsIncentiveCompatibleOn Q P a b ↔
      MonotoneOn Q (Icc a b) ∧
        ∀ t ∈ Icc a b, truthfulUtility Q P t = truthfulUtility Q P a + ∫ x in a..t, Q x := by
  refine ⟨fun h => ⟨h.allocation_monotoneOn, fun t ht => h.envelope_formula ht⟩, ?_⟩
  rintro ⟨hQ, hU⟩
  rw [isIncentiveCompatibleOn_iff_utility]
  intro s hs t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have hsplit : (∫ x in a..t, Q x) - ∫ x in a..s, Q x = ∫ x in s..t, Q x :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_monotoneOn hQ ha ht)
      (intervalIntegrable_of_monotoneOn hQ ha hs)
  rw [hU s hs, hU t ht]
  rcases le_total s t with hst | hts
  · have := (integral_mem_of_monotoneOn hQ hs ht hst).1
    linarith
  · have h2 := (integral_mem_of_monotoneOn hQ ht hs hts).2
    have hsym : ∫ x in s..t, Q x = -∫ x in t..s, Q x := intervalIntegral.integral_symm t s
    nlinarith

/-- **Payment formula.** In an incentive-compatible single-parameter mechanism on `[a, b]`,
the payment is determined by the allocation rule and the utility of the lowest value:
`P t = t * Q t - ∫_a^t Q - U a` (Myerson 1981, (4.8) with `U a = 0`; Hartline and Karlin 2007,
Theorem 13.6 (ii), where `a = 0` and `P 0 = 0`). -/
theorem IsIncentiveCompatibleOn.payment_formula (h : IsIncentiveCompatibleOn Q P a b) {t : ℝ}
    (ht : t ∈ Icc a b) : P t = t * Q t - (∫ x in a..t, Q x) - truthfulUtility Q P a := by
  have := h.envelope_formula ht
  unfold truthfulUtility at this ⊢
  linarith

/-- **Revenue equivalence (pointwise).** Two single-parameter mechanisms with the same
allocation rule `Q` that are incentive compatible on `[a, b]` and charge the same payment at the
lowest value `a` charge the same payment at every value in `[a, b]` (the one-bidder form of
Myerson 1981, Corollary;
Nisan 2007, Theorem 9.46). -/
theorem payment_eqOn_of_isIncentiveCompatibleOn {P₁ P₂ : ℝ → ℝ}
    (h₁ : IsIncentiveCompatibleOn Q P₁ a b) (h₂ : IsIncentiveCompatibleOn Q P₂ a b)
    (ha : P₁ a = P₂ a) : EqOn P₁ P₂ (Icc a b) := by
  intro t ht
  rw [h₁.payment_formula ht, h₂.payment_formula ht]
  simp only [truthfulUtility, ha]

/-- **Revenue equivalence (in expectation).** Under the hypotheses of
`payment_eqOn_of_isIncentiveCompatibleOn`, the expected payments agree for every distribution
`μ` of values: `∫_{[a,b]} P₁ dμ = ∫_{[a,b]} P₂ dμ` (the one-bidder form of Myerson 1981,
Corollary: the seller's
expected revenue is determined by the allocation rule and the utilities of the lowest
types). -/
theorem setIntegral_payment_eq {P₁ P₂ : ℝ → ℝ} (h₁ : IsIncentiveCompatibleOn Q P₁ a b)
    (h₂ : IsIncentiveCompatibleOn Q P₂ a b) (ha : P₁ a = P₂ a) (μ : Measure ℝ) :
    ∫ t in Icc a b, P₁ t ∂μ = ∫ t in Icc a b, P₂ t ∂μ :=
  setIntegral_congr_fun measurableSet_Icc (payment_eqOn_of_isIncentiveCompatibleOn h₁ h₂ ha)

/-- **Individual rationality from the lowest type.** If `(Q, P)` is incentive compatible on
`[a, b]`, `Q ≥ 0` on `[a, b]` and the lowest value gets `U a ≥ 0`, then every value gets a
nonnegative utility (Myerson 1981, proof of Lemma 2: (3.4) follows from (4.3) and (4.4)). -/
theorem IsIncentiveCompatibleOn.utility_nonneg_of_lowest (h : IsIncentiveCompatibleOn Q P a b)
    (hQ : ∀ t ∈ Icc a b, 0 ≤ Q t) (ha : 0 ≤ truthfulUtility Q P a) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ truthfulUtility Q P t := by
  rw [h.envelope_formula ht]
  have : 0 ≤ ∫ x in a..t, Q x :=
    intervalIntegral.integral_nonneg ht.1 fun x hx => hQ x ⟨hx.1, hx.2.trans ht.2⟩
  linarith

/-- **Myerson's Lemma 2 for one bidder.** If `0 ≤ Q` on `[a, b]` and `a ≤ b`, the mechanism
`(Q, P)` is incentive compatible and individually rational (`U t ≥ 0` for all `t ∈ [a, b]`) on
`[a, b]` if and only if `Q` is monotone on `[a, b]`, the envelope formula
`U t = U a + ∫_a^t Q` holds on `[a, b]`, and `U a ≥ 0` (Myerson 1981, Lemma 2, (4.2)–(4.4), for
a single bidder without revision effects; the probability conditions (3.3) are the separate
hypothesis `0 ≤ Q`). -/
theorem isIncentiveCompatibleOn_and_utility_nonneg_iff (hab : a ≤ b)
    (hQ : ∀ t ∈ Icc a b, 0 ≤ Q t) :
    (IsIncentiveCompatibleOn Q P a b ∧ ∀ t ∈ Icc a b, 0 ≤ truthfulUtility Q P t) ↔
      MonotoneOn Q (Icc a b) ∧
        (∀ t ∈ Icc a b, truthfulUtility Q P t = truthfulUtility Q P a + ∫ x in a..t, Q x) ∧
          0 ≤ truthfulUtility Q P a := by
  constructor
  · rintro ⟨h, hir⟩
    exact ⟨h.allocation_monotoneOn, fun t ht => h.envelope_formula ht, hir a ⟨le_rfl, hab⟩⟩
  · rintro ⟨hmono, hU, ha⟩
    have h : IsIncentiveCompatibleOn Q P a b := isIncentiveCompatibleOn_iff.2 ⟨hmono, hU⟩
    exact ⟨h, fun t ht => h.utility_nonneg_of_lowest hQ ha ht⟩

end MathlibExt.GameTheory.MechanismDesign.SingleParameter
