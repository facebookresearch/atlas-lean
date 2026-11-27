/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldInequalities

/-!
# The Wald–Wolfowitz theorem: optimality of the sequential probability ratio test

For mutually absolutely continuous laws `P₀ ≠ P₁` of i.i.d. observations and log-boundaries
`a < 0 < b`, `MeasureTheory.sprt_wald_wolfowitz` states that the SPRT `N` of
`MathlibExt.Probability.Statistics.SequentialAnalysis` minimises both expected sample sizes: if a
test `(T, D)` (a stopping time of the observations with finite expectations under `P₀` and `P₁`
and a rejection region in the stopped `σ`-algebra) has error probabilities `P₀(D)` and `P₁(Dᶜ)`
at most those of the SPRT, then `E₀ N ≤ E₀ T` and `E₁ N ≤ E₁ T`. This is the theorem of Wald and
Wolfowitz (1948). No condition on the error probabilities of the SPRT is needed, and the finite
expected sample sizes of the SPRT are a consequence of the proof.

## Proof outline

The proof is the Bayes argument of Wald and Wolfowitz; the choice of the costs follows Dudley's
lecture notes (Lemma 1.7.10), in which the sampling cost fixes the ratio of the two boundaries
and the prior fixes their position. Write `r = dP₁/dP₀` and `Rₙ = ∏_{i=1}^{n} r(Xᵢ)` for the
likelihood ratio of the first `n` observations (coordinate `i` of `ℕ → X` is `X_{i+1}`).

* **Bayes problem.** Fix a loss `κ > 0` for rejecting `P₀` when it is true, a loss `1` for
  accepting it when `P₁` is true, a cost `c > 0` per observation and prior odds `ℓ₀` of `P₁`
  against `P₀`. Up to the prior weight of `P₀`, the Bayes risk of a test `(T, D)` is
  `c (E₀ T + ℓ₀ E₁ T) + κ P₀(D) + ℓ₀ P₁(Dᶜ)`, and after `n` observations the posterior odds are
  `y = ℓ₀ Rₙ`.
* **Value function.** Backward induction gives `V₀ y = min κ y` and
  `V_{n+1} y = min (min κ y) (c (1 + y) + ∫ V_n (y r) dP₀)`; the decreasing limit `V` satisfies
  the Bellman equation `V y = min (min κ y) (C y)`, where `C y = c (1 + y) + ∫ V (y r) dP₀` is the
  expected loss of observing once more. By induction, `V` is monotone and `V (t y) ≤ t V y` for
  `t ≥ 1`, and multiplying the cost by `t ≥ 1` multiplies `V` by at most `t`.
* **Boundaries.** Accepting `P₀` is optimal exactly on `[0, A]` and rejecting it exactly on
  `[B, ∞]`, with `A ≤ κ ≤ B`, and observing is optimal on `(A, B)`; outside `[A, B]` stopping is
  strictly better than observing. Hence `A` and `B` depend continuously on `c`. For `c ≥ κ`,
  `A = B = κ`; for small `c`, `A` is small, because `V y ≤ m c (1 + y) + √(κ y) Hᵐ`, where
  `H = ∫ √r dP₀ < 1` is the Hellinger affinity of `P₀ ≠ P₁`. The intermediate value theorem gives
  a cost with `B = e^{b - a} A`, and with `ℓ₀ = e^{-a} A` the SPRT stops exactly when `ℓ₀ Rₙ`
  leaves `(A, B)`, accepting `P₀` at or below `A` and `P₁` at or above `B`.
* **Verification.** Integrating out the next observation (the coordinates are independent) and
  `V ≤ C` show, by induction on `n`, that `V ℓ₀` is at most the expected loss of a stopping time
  `T` accumulated before `min T n` plus the expected value `V (ℓ₀ Rₙ)` on `{n ≤ T}`. If
  `E₀ T < ∞`, letting `n → ∞` bounds `V ℓ₀` by the Bayes risk of `(T, D)`. For the SPRT, `V = C`
  while it observes and `V` is its decision loss when it stops, so its Bayes risk is at most
  `V ℓ₀`; in particular its expected sample sizes are finite.
* **Conclusion.** Comparing the two Bayes risks and cancelling the error terms gives
  `E₀ N + ℓ₀ E₁ N ≤ E₀ T + ℓ₀ E₁ T` with `κ e^{-b} ≤ ℓ₀ ≤ κ e^{-a}`; letting `κ → 0` and
  `κ → ∞` gives the two inequalities.

## References

* A. Wald and J. Wolfowitz, *Optimum character of the sequential probability ratio test*, Ann.
  Math. Statist. 19 (1948), no. 3, 326–339, doi:10.1214/aoms/1177730197: the theorem (§1, proved
  in §7) and the Bayes risk (§2).
* R. M. Dudley, *Mathematical Statistics*, unpublished lecture notes for MIT course 18.466
  (2003), Theorem 1.5.1 and §1.7 (Theorem 1.7.7, Lemmas 1.7.9 and 1.7.10); the 2005 revision
  numbers the same results Theorem 1.6.1 and §1.8 (Theorem 1.8.5, Lemmas 1.8.9 and 1.8.10).
* T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica
  11 (2001) 303–408, §2, p. 305.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ### The Bayes value function of the sequential testing problem -/

/-- Backward induction for the Bayes problem with horizon `n`, in the state `y` given by the
posterior odds of `P₁` against `P₀`: rejecting `P₀` costs `κ`, accepting it costs `y` (a unit loss
weighted by the odds), and each observation costs `c (1 + y)`. -/
private noncomputable def bayesIter (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) : ℕ → ℝ≥0∞ → ℝ≥0∞
  | 0 => fun y => min κ y
  | n + 1 => fun y => min (min κ y)
      (c * (1 + y) + ∫⁻ x, bayesIter P₀ P₁ κ c n (y * P₁.rnDeriv P₀ x) ∂P₀)

private theorem bayesIter_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) (y : ℝ≥0∞) :
    bayesIter P₀ P₁ κ c n y ≤ min κ y := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_left _ _

private theorem bayesIter_mono (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) :
    Monotone (bayesIter P₀ P₁ κ c n) := by
  induction n with
  | zero => exact fun y y' h => min_le_min_left _ h
  | succ n ih =>
    intro y y' h
    refine min_le_min (min_le_min_left _ h) (add_le_add ?_ ?_)
    · gcongr
    · exact lintegral_mono fun x => ih (mul_le_mul_left h _)

private theorem measurable_bayesIter (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) :
    Measurable (bayesIter P₀ P₁ κ c n) :=
  (bayesIter_mono P₀ P₁ κ c n).measurable

private theorem measurable_bayesIter_comp (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ)
    (y : ℝ≥0∞) : Measurable fun x => bayesIter P₀ P₁ κ c n (y * P₁.rnDeriv P₀ x) :=
  (measurable_bayesIter P₀ P₁ κ c n).comp (measurable_const.mul (Measure.measurable_rnDeriv _ _))

private theorem bayesIter_succ_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) (y : ℝ≥0∞) :
    bayesIter P₀ P₁ κ c (n + 1) y ≤ bayesIter P₀ P₁ κ c n y := by
  induction n generalizing y with
  | zero => exact min_le_left _ _
  | succ n ih =>
    refine min_le_min_left _ ?_
    gcongr with x
    exact ih _

private theorem antitone_bayesIter (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (y : ℝ≥0∞) :
    Antitone fun n => bayesIter P₀ P₁ κ c n y :=
  antitone_nat_of_succ_le fun n => bayesIter_succ_le P₀ P₁ κ c n y

private theorem bayesIter_mul_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (y : ℝ≥0∞) :
    bayesIter P₀ P₁ κ c n (t * y) ≤ t * bayesIter P₀ P₁ κ c n y := by
  have hbase : ∀ y, min κ (t * y) ≤ t * min κ y := fun y => by
    rw [mul_min]
    exact min_le_min_right _ (le_mul_of_one_le_left' ht)
  induction n generalizing y with
  | zero => exact hbase y
  | succ n ih =>
    simp only [bayesIter]
    rw [mul_min]
    refine min_le_min (hbase y) ?_
    rw [mul_add t]
    refine add_le_add ?_ ?_
    · calc c * (1 + t * y) = c + t * (c * y) := by ring
        _ ≤ t * c + t * (c * y) := by gcongr; exact le_mul_of_one_le_left' ht
        _ = t * (c * (1 + y)) := by ring
    · rw [← lintegral_const_mul _ (measurable_bayesIter_comp P₀ P₁ κ c n y)]
      refine lintegral_mono fun x => ?_
      rw [mul_assoc]
      exact ih _

private theorem bayesIter_mono_cost (P₀ P₁ : Measure X) (κ : ℝ≥0∞) {c c' : ℝ≥0∞}
    (hc : c ≤ c') (n : ℕ) (y : ℝ≥0∞) :
    bayesIter P₀ P₁ κ c n y ≤ bayesIter P₀ P₁ κ c' n y := by
  induction n generalizing y with
  | zero => exact le_rfl
  | succ n ih =>
    refine min_le_min_left _ ?_
    gcongr with x
    exact ih _

private theorem bayesIter_cost_mul_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (n : ℕ) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (y : ℝ≥0∞) :
    bayesIter P₀ P₁ κ (t * c) n y ≤ t * bayesIter P₀ P₁ κ c n y := by
  induction n generalizing y with
  | zero => exact le_mul_of_one_le_left' ht
  | succ n ih =>
    simp only [bayesIter]
    rw [mul_min]
    refine min_le_min (le_mul_of_one_le_left' ht) ?_
    rw [mul_add t, ← mul_assoc]
    refine add_le_add le_rfl ?_
    rw [← lintegral_const_mul _ (measurable_bayesIter_comp P₀ P₁ κ c n y)]
    exact lintegral_mono fun x => ih _

/-- The value function of the Bayes problem with unbounded horizon. -/
private noncomputable def bayesValue (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (y : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ n, bayesIter P₀ P₁ κ c n y

/-- The expected loss of taking one more observation and then acting optimally. -/
private noncomputable def bayesCont (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) (y : ℝ≥0∞) : ℝ≥0∞ :=
  c * (1 + y) + ∫⁻ x, bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x) ∂P₀

private theorem bayesValue_le (P₀ P₁ : Measure X) (κ c y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c y ≤ min κ y :=
  (iInf_le _ 0).trans (bayesIter_le P₀ P₁ κ c 0 y)

private theorem bayesValue_mono (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) :
    Monotone (bayesValue P₀ P₁ κ c) :=
  fun _ _ h => iInf_mono fun n => bayesIter_mono P₀ P₁ κ c n h

private theorem measurable_bayesValue (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) :
    Measurable (bayesValue P₀ P₁ κ c) :=
  (bayesValue_mono P₀ P₁ κ c).measurable

private theorem measurable_bayesValue_comp (P₀ P₁ : Measure X) (κ c y : ℝ≥0∞) :
    Measurable fun x => bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x) :=
  (measurable_bayesValue P₀ P₁ κ c).comp (measurable_const.mul (Measure.measurable_rnDeriv _ _))

private theorem bayesValue_mul_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) {t : ℝ≥0∞} (ht : 1 ≤ t)
    (ht' : t ≠ ∞) (y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c (t * y) ≤ t * bayesValue P₀ P₁ κ c y := by
  rw [bayesValue, bayesValue, ENNReal.mul_iInf_of_ne (one_pos.trans_le ht).ne' ht']
  exact iInf_mono fun n => bayesIter_mul_le P₀ P₁ κ c n ht y

private theorem bayesValue_mono_cost (P₀ P₁ : Measure X) (κ : ℝ≥0∞) {c c' : ℝ≥0∞}
    (hc : c ≤ c') (y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c y ≤ bayesValue P₀ P₁ κ c' y :=
  iInf_mono fun n => bayesIter_mono_cost P₀ P₁ κ hc n y

private theorem bayesValue_cost_mul_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ (t * c) y ≤ t * bayesValue P₀ P₁ κ c y := by
  rw [bayesValue, bayesValue, ENNReal.mul_iInf_of_ne (one_pos.trans_le ht).ne' ht']
  exact iInf_mono fun n => bayesIter_cost_mul_le P₀ P₁ κ c n ht y

/-- **Bellman equation** for the value function. -/
private theorem bayesValue_eq (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ : ℝ≥0∞} (hκ : κ ≠ ∞)
    (c y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c y = min (min κ y) (bayesCont P₀ P₁ κ c y) := by
  have hshift : bayesValue P₀ P₁ κ c y = ⨅ n, bayesIter P₀ P₁ κ c (n + 1) y :=
    le_antisymm (le_iInf fun n => iInf_le _ (n + 1))
      (iInf_mono fun n => bayesIter_succ_le P₀ P₁ κ c n y)
  rw [hshift]
  simp only [bayesIter, bayesCont]
  rw [← inf_iInf, ← ENNReal.add_iInf]
  congr 2
  simp only [bayesValue]
  rw [lintegral_iInf]
  · intro n
    exact (measurable_bayesIter P₀ P₁ κ c n).comp
      (measurable_const.mul (Measure.measurable_rnDeriv _ _))
  · intro n m hnm x
    exact antitone_bayesIter P₀ P₁ κ c _ hnm
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hκ (measure_ne_top P₀ Set.univ)) ?_
    rw [← lintegral_const]
    exact lintegral_mono fun x => (bayesIter_le P₀ P₁ κ c 0 _).trans (min_le_left _ _)

private theorem bayesValue_le_cont (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ : ℝ≥0∞}
    (hκ : κ ≠ ∞) (c y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c y ≤ bayesCont P₀ P₁ κ c y := by
  rw [bayesValue_eq P₀ P₁ hκ]
  exact min_le_right _ _

private theorem mul_le_bayesCont (P₀ P₁ : Measure X) (κ c y : ℝ≥0∞) :
    c * (1 + y) ≤ bayesCont P₀ P₁ κ c y :=
  le_self_add

private theorem lintegral_bayesValue_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (κ c y : ℝ≥0∞) : ∫⁻ x, bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x) ∂P₀ ≤ κ := by
  calc ∫⁻ x, bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x) ∂P₀ ≤ ∫⁻ _, κ ∂P₀ :=
        lintegral_mono fun x => (bayesValue_le P₀ P₁ κ c _).trans (min_le_left _ _)
    _ = κ := by simp

private theorem bayesCont_ne_top (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {κ c y : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hc : c ≠ ∞) (hy : y ≠ ∞) : bayesCont P₀ P₁ κ c y ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hc (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hy⟩),
    ne_top_of_le_ne_top hκ (lintegral_bayesValue_le P₀ P₁ κ c y)⟩

/-- Cross-multiplied form of the subhomogeneity of the value function. -/
private theorem mul_bayesValue_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) {y y' : ℝ≥0∞}
    (hyy' : y ≤ y') (hy : y ≠ 0) (hy' : y' ≠ ∞) :
    y * bayesValue P₀ P₁ κ c y' ≤ y' * bayesValue P₀ P₁ κ c y := by
  have hyt : y ≠ ∞ := ne_top_of_le_ne_top hy' hyy'
  have ht : 1 ≤ y' / y := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hy) (Or.inl hyt), one_mul]; exact hyy'
  have ht' : y' / y ≠ ∞ := ENNReal.div_ne_top hy' hy
  have hyy : y' = y' / y * y := (ENNReal.div_mul_cancel hy hyt).symm
  calc y * bayesValue P₀ P₁ κ c y' = y * bayesValue P₀ P₁ κ c (y' / y * y) := by rw [← hyy]
    _ ≤ y * (y' / y * bayesValue P₀ P₁ κ c y) := by
        gcongr; exact bayesValue_mul_le P₀ P₁ κ c ht ht' y
    _ = y' * bayesValue P₀ P₁ κ c y := by
        rw [← mul_assoc, ENNReal.mul_div_cancel hy hyt]

/-! ### The stopping boundaries -/

/-- The lower stopping boundary: the largest state at which accepting `P₀` is optimal. -/
private noncomputable def lowerBd (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {y | y ≤ κ ∧ bayesValue P₀ P₁ κ c y = y}

/-- The upper stopping boundary: the smallest state at which rejecting `P₀` is optimal. -/
private noncomputable def upperBd (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {y | κ ≤ y ∧ bayesValue P₀ P₁ κ c y = κ}

private theorem lowerBd_le (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) : lowerBd P₀ P₁ κ c ≤ κ :=
  sSup_le fun _ hy => hy.1

private theorem le_upperBd (P₀ P₁ : Measure X) (κ c : ℝ≥0∞) : κ ≤ upperBd P₀ P₁ κ c :=
  le_sInf fun _ hy => hy.1

private theorem bayesValue_eq_self_of_lt_lowerBd (P₀ P₁ : Measure X) {κ c y : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hy : y < lowerBd P₀ P₁ κ c) : bayesValue P₀ P₁ κ c y = y := by
  obtain ⟨y', ⟨hy'κ, hy'V⟩, hyy'⟩ := lt_sSup_iff.1 hy
  refine le_antisymm ((bayesValue_le P₀ P₁ κ c y).trans (min_le_right _ _)) ?_
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_le
  have hy'top : y' ≠ ∞ := ne_top_of_le_ne_top hκ hy'κ
  have h := mul_bayesValue_le P₀ P₁ κ c hyy'.le hy0 hy'top
  rw [hy'V, mul_comm] at h
  exact (ENNReal.mul_le_mul_iff_right (pos_of_gt hyy').ne' hy'top).1 h

private theorem bayesValue_lt_self (P₀ P₁ : Measure X) {κ c y : ℝ≥0∞}
    (hy : lowerBd P₀ P₁ κ c < y) (hyκ : y ≤ κ) : bayesValue P₀ P₁ κ c y < y :=
  lt_of_le_of_ne ((bayesValue_le P₀ P₁ κ c y).trans (min_le_right _ _))
    fun h => (le_sSup (s := {y | y ≤ κ ∧ bayesValue P₀ P₁ κ c y = y}) ⟨hyκ, h⟩).not_gt hy

private theorem bayesValue_lowerBd (P₀ P₁ : Measure X) {κ c : ℝ≥0∞} (hκ : κ ≠ ∞) :
    bayesValue P₀ P₁ κ c (lowerBd P₀ P₁ κ c) = lowerBd P₀ P₁ κ c := by
  refine le_antisymm ((bayesValue_le P₀ P₁ κ c _).trans (min_le_right _ _)) ?_
  refine le_of_forall_lt fun y hy => ?_
  obtain ⟨y'', hyy'', hy''⟩ := exists_between hy
  calc y < y'' := hyy''
    _ = bayesValue P₀ P₁ κ c y'' := (bayesValue_eq_self_of_lt_lowerBd P₀ P₁ hκ hy'').symm
    _ ≤ _ := bayesValue_mono P₀ P₁ κ c hy''.le

private theorem bayesValue_eq_of_le_lowerBd (P₀ P₁ : Measure X) {κ c y : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hy : y ≤ lowerBd P₀ P₁ κ c) : bayesValue P₀ P₁ κ c y = y := by
  rcases hy.lt_or_eq with hy | rfl
  · exact bayesValue_eq_self_of_lt_lowerBd P₀ P₁ hκ hy
  · exact bayesValue_lowerBd P₀ P₁ hκ

private theorem min_le_lowerBd (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ : ℝ≥0∞}
    (hκ : κ ≠ ∞) (c : ℝ≥0∞) : min κ c ≤ lowerBd P₀ P₁ κ c := by
  refine le_sSup ⟨min_le_left _ _, ?_⟩
  rw [bayesValue_eq P₀ P₁ hκ, min_eq_right (min_le_left κ c)]
  refine min_eq_left ?_
  calc min κ c ≤ c := min_le_right _ _
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * (1 + min κ c) := by gcongr; exact le_self_add
    _ ≤ _ := mul_le_bayesCont P₀ P₁ κ c _

private theorem lowerBd_pos (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c : ℝ≥0∞}
    (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) (hc0 : c ≠ 0) : 0 < lowerBd P₀ P₁ κ c :=
  (lt_min (pos_iff_ne_zero.2 hκ0) (pos_iff_ne_zero.2 hc0)).trans_le (min_le_lowerBd P₀ P₁ hκ c)

private theorem bayesValue_eq_of_upperBd_lt (P₀ P₁ : Measure X) {κ c y : ℝ≥0∞}
    (hy : upperBd P₀ P₁ κ c < y) : bayesValue P₀ P₁ κ c y = κ := by
  obtain ⟨y', ⟨hκy', hy'V⟩, hy'y⟩ := sInf_lt_iff.1 hy
  refine le_antisymm ((bayesValue_le P₀ P₁ κ c y).trans (min_le_left _ _)) ?_
  calc κ = bayesValue P₀ P₁ κ c y' := hy'V.symm
    _ ≤ _ := bayesValue_mono P₀ P₁ κ c hy'y.le

private theorem bayesValue_lt_of_lt_upperBd (P₀ P₁ : Measure X) {κ c y : ℝ≥0∞}
    (hκy : κ ≤ y) (hy : y < upperBd P₀ P₁ κ c) : bayesValue P₀ P₁ κ c y < κ :=
  lt_of_le_of_ne ((bayesValue_le P₀ P₁ κ c y).trans (min_le_left _ _))
    fun h => (sInf_le (s := {y | κ ≤ y ∧ bayesValue P₀ P₁ κ c y = κ}) ⟨hκy, h⟩).not_gt hy

private theorem upperBd_lt_top (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞) : upperBd P₀ P₁ κ c < ∞ := by
  have hmem : κ / c + κ ∈ {y | κ ≤ y ∧ bayesValue P₀ P₁ κ c y = κ} := by
    refine ⟨le_add_self, ?_⟩
    rw [bayesValue_eq P₀ P₁ hκ, min_eq_left (le_add_self : κ ≤ κ / c + κ)]
    refine min_eq_left ?_
    calc κ = c * (κ / c) := (ENNReal.mul_div_cancel hc0 hc).symm
      _ ≤ c * (1 + (κ / c + κ)) := by
          gcongr
          exact (le_self_add : κ / c ≤ κ / c + κ).trans le_add_self
      _ ≤ _ := mul_le_bayesCont P₀ P₁ κ c _
  exact (sInf_le hmem).trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.div_lt_top hκ hc0, hκ.lt_top⟩)

private theorem bayesValue_upperBd (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c : ℝ≥0∞}
    (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    bayesValue P₀ P₁ κ c (upperBd P₀ P₁ κ c) = κ := by
  set B := upperBd P₀ P₁ κ c
  have hB0 : B ≠ 0 := (pos_iff_ne_zero.2 hκ0).trans_le (le_upperBd P₀ P₁ κ c) |>.ne'
  have hBtop : B ≠ ∞ := (upperBd_lt_top P₀ P₁ hκ hc0 hc).ne
  have hle : bayesValue P₀ P₁ κ c B ≤ κ := (bayesValue_le P₀ P₁ κ c B).trans (min_le_left _ _)
  refine le_antisymm hle (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  have hε' : (ε : ℝ≥0∞) / κ ≠ 0 := ENNReal.div_pos (by exact_mod_cast hε.ne') hκ |>.ne'
  have ht1 : 1 ≤ 1 + (ε : ℝ≥0∞) / κ := le_self_add
  have httop : 1 + (ε : ℝ≥0∞) / κ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.div_ne_top ENNReal.coe_ne_top hκ0⟩
  have hlt : B < (1 + (ε : ℝ≥0∞) / κ) * B := by
    conv_lhs => rw [← one_mul B]
    exact (ENNReal.mul_lt_mul_iff_left hB0 hBtop).2 (ENNReal.lt_add_right ENNReal.one_ne_top hε')
  calc κ = bayesValue P₀ P₁ κ c ((1 + (ε : ℝ≥0∞) / κ) * B) :=
        (bayesValue_eq_of_upperBd_lt P₀ P₁ hlt).symm
    _ ≤ (1 + (ε : ℝ≥0∞) / κ) * bayesValue P₀ P₁ κ c B := bayesValue_mul_le P₀ P₁ κ c ht1 httop B
    _ = bayesValue P₀ P₁ κ c B + (ε : ℝ≥0∞) / κ * bayesValue P₀ P₁ κ c B := by ring
    _ ≤ bayesValue P₀ P₁ κ c B + (ε : ℝ≥0∞) / κ * κ := by gcongr
    _ = bayesValue P₀ P₁ κ c B + ε := by rw [ENNReal.div_mul_cancel hκ0 hκ]

private theorem bayesValue_eq_of_upperBd_le (P₀ P₁ : Measure X) [IsFiniteMeasure P₀]
    {κ c y : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hy : upperBd P₀ P₁ κ c ≤ y) : bayesValue P₀ P₁ κ c y = κ := by
  rcases hy.lt_or_eq with hy | rfl
  · exact bayesValue_eq_of_upperBd_lt P₀ P₁ hy
  · exact bayesValue_upperBd P₀ P₁ hκ0 hκ hc0 hc

/-- Between the boundaries, continuing is optimal. -/
private theorem bayesValue_eq_cont (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c y : ℝ≥0∞}
    (hκ : κ ≠ ∞) (h₁ : lowerBd P₀ P₁ κ c < y) (h₂ : y < upperBd P₀ P₁ κ c) :
    bayesValue P₀ P₁ κ c y = bayesCont P₀ P₁ κ c y := by
  have hlt : bayesValue P₀ P₁ κ c y < min κ y := by
    rcases le_total y κ with hyκ | hκy
    · rw [min_eq_right hyκ]; exact bayesValue_lt_self P₀ P₁ h₁ hyκ
    · rw [min_eq_left hκy]; exact bayesValue_lt_of_lt_upperBd P₀ P₁ hκy h₂
  have h := bayesValue_eq P₀ P₁ hκ c y
  rcases le_total (min κ y) (bayesCont P₀ P₁ κ c y) with hle | hle
  · rw [min_eq_left hle] at h; exact absurd h hlt.ne
  · rwa [min_eq_right hle] at h

/-- Strictly below the lower boundary, stopping is strictly better than continuing. -/
private theorem lt_bayesCont_of_lt_lowerBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {κ c y : ℝ≥0∞} (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞) (hy : y < lowerBd P₀ P₁ κ c) :
    y < bayesCont P₀ P₁ κ c y := by
  obtain ⟨y', ⟨hy'κ, hy'V⟩, hyy'⟩ := lt_sSup_iff.1 hy
  rcases eq_or_ne y 0 with rfl | hy0
  · calc (0 : ℝ≥0∞) < c * (1 + 0) := by simpa using pos_iff_ne_zero.2 hc0
      _ ≤ _ := mul_le_bayesCont P₀ P₁ κ c 0
  have hy'top : y' ≠ ∞ := ne_top_of_le_ne_top hκ hy'κ
  have hytop : y ≠ ∞ := ne_top_of_le_ne_top hy'top hyy'.le
  set t := y' / y with ht_def
  have ht1 : 1 < t := by
    rw [ht_def, ENNReal.lt_div_iff_mul_lt (Or.inl hy0) (Or.inl hytop), one_mul]; exact hyy'
  have httop : t ≠ ∞ := ENNReal.div_ne_top hy'top hy0
  have hty : t * y = y' := ENNReal.div_mul_cancel hy0 hytop
  set I := ∫⁻ x, bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x) ∂P₀ with hI
  have hItop : I ≠ ∞ := ne_top_of_le_ne_top hκ (lintegral_bayesValue_le P₀ P₁ κ c y)
  have hI' : ∫⁻ x, bayesValue P₀ P₁ κ c (y' * P₁.rnDeriv P₀ x) ∂P₀ ≤ t * I := by
    rw [hI, ← lintegral_const_mul _ (measurable_bayesValue_comp P₀ P₁ κ c y)]
    refine lintegral_mono fun x => ?_
    rw [← hty, mul_assoc]
    exact bayesValue_mul_le P₀ P₁ κ c ht1.le httop _
  have hfin : c * y' + t * I ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hc hy'top, ENNReal.mul_ne_top httop hItop⟩
  have key : t * y < t * bayesCont P₀ P₁ κ c y := by
    calc t * y = y' := hty
      _ = bayesValue P₀ P₁ κ c y' := hy'V.symm
      _ ≤ bayesCont P₀ P₁ κ c y' := bayesValue_le_cont P₀ P₁ hκ c y'
      _ ≤ c + (c * y' + t * I) := by
          rw [bayesCont, mul_add, mul_one, add_assoc]; gcongr
      _ < t * c + (c * y' + t * I) := by
          refine ENNReal.add_lt_add_right hfin ?_
          conv_lhs => rw [← one_mul c]
          exact (ENNReal.mul_lt_mul_iff_left hc0 hc).2 ht1
      _ = t * bayesCont P₀ P₁ κ c y := by
          rw [bayesCont, ← hI, ← hty]; ring
  exact (ENNReal.mul_lt_mul_iff_right (zero_lt_one.trans ht1).ne' httop).1 key

/-- Strictly above the upper boundary, stopping is strictly better than continuing. -/
private theorem lt_bayesCont_of_upperBd_lt (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {κ c y : ℝ≥0∞} (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞) (hy : upperBd P₀ P₁ κ c < y) :
    κ < bayesCont P₀ P₁ κ c y := by
  obtain ⟨y', ⟨hκy', hy'V⟩, hy'y⟩ := sInf_lt_iff.1 hy
  have hy'top : y' ≠ ∞ := hy'y.ne_top
  calc κ = bayesValue P₀ P₁ κ c y' := hy'V.symm
    _ ≤ bayesCont P₀ P₁ κ c y' := bayesValue_le_cont P₀ P₁ hκ c y'
    _ < bayesCont P₀ P₁ κ c y := by
        refine ENNReal.add_lt_add_of_lt_of_le
          (ne_top_of_le_ne_top hκ (lintegral_bayesValue_le P₀ P₁ κ c y')) ?_
          (lintegral_mono fun x => bayesValue_mono P₀ P₁ κ c (by gcongr))
        refine (ENNReal.mul_lt_mul_iff_right hc0 hc).2 ?_
        exact ENNReal.add_lt_add_left ENNReal.one_ne_top hy'y

/-! ### Continuity of the boundaries in the sampling cost -/

private theorem bayesValue_le_mul_of_le (P₀ P₁ : Measure X) (κ : ℝ≥0∞) {c c' t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (hc : c' ≤ t * c) (y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c' y ≤ t * bayesValue P₀ P₁ κ c y :=
  (bayesValue_mono_cost P₀ P₁ κ hc y).trans (bayesValue_cost_mul_le P₀ P₁ κ c ht ht' y)

private theorem bayesCont_le_mul_of_le (P₀ P₁ : Measure X) (κ : ℝ≥0∞) {c c' t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (hc : c' ≤ t * c) (y : ℝ≥0∞) :
    bayesCont P₀ P₁ κ c' y ≤ t * bayesCont P₀ P₁ κ c y := by
  rw [bayesCont, bayesCont, mul_add t,
    ← lintegral_const_mul _ (measurable_bayesValue_comp P₀ P₁ κ c y), ← mul_assoc]
  gcongr with x
  exact bayesValue_le_mul_of_le P₀ P₁ κ ht ht' hc _

private theorem ofReal_le_ofReal_max_mul {c₀ : ℝ} (hc₀ : 0 < c₀) (c : ℝ) :
    ENNReal.ofReal c ≤ ENNReal.ofReal (max 1 (c / c₀)) * ENNReal.ofReal c₀ := by
  rw [← ENNReal.ofReal_mul (le_max_of_le_left zero_le_one)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc c = c / c₀ * c₀ := (div_mul_cancel₀ c hc₀.ne').symm
    _ ≤ max 1 (c / c₀) * c₀ := mul_le_mul_of_nonneg_right (le_max_right _ _) hc₀.le

private theorem tendsto_ofReal_max_mul {c₀ : ℝ} {z : ℝ≥0∞} (hz : z ≠ ∞)
    {f : ℝ → ℝ} (hf : ContinuousAt f c₀) (hf₀ : f c₀ = 1) :
    Tendsto (fun c : ℝ => ENNReal.ofReal (max 1 (f c)) * z) (𝓝 c₀) (𝓝 z) := by
  have h1 : ContinuousAt (fun c : ℝ => max 1 (f c)) c₀ := continuousAt_const.max hf
  have := ENNReal.Tendsto.mul_const (b := z)
    (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto (Or.inr hz)
  simpa [hf₀] using this

private theorem eventually_bayesValue_lt (P₀ P₁ : Measure X) {κ : ℝ≥0∞} (hκ : κ ≠ ∞) {c₀ : ℝ}
    (hc₀ : 0 < c₀) {y z : ℝ≥0∞} (h : bayesValue P₀ P₁ κ (ENNReal.ofReal c₀) y < z) :
    ∀ᶠ c in 𝓝 c₀, bayesValue P₀ P₁ κ (ENNReal.ofReal c) y < z := by
  have hv : bayesValue P₀ P₁ κ (ENNReal.ofReal c₀) y ≠ ∞ :=
    ne_top_of_le_ne_top hκ ((bayesValue_le P₀ P₁ κ _ y).trans (min_le_left _ _))
  have hT := tendsto_ofReal_max_mul hv (f := fun c => c / c₀)
    (continuousAt_id.div_const c₀) (div_self hc₀.ne')
  filter_upwards [hT.eventually_lt_const h] with c hc
  exact (bayesValue_le_mul_of_le P₀ P₁ κ (ENNReal.one_le_ofReal.2 (le_max_left _ _))
    ENNReal.ofReal_ne_top (ofReal_le_ofReal_max_mul hc₀ c) y).trans_lt hc

private theorem eventually_lt_bayesCont (P₀ P₁ : Measure X) (κ : ℝ≥0∞) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {y z : ℝ≥0∞} (hz : z ≠ ∞) (h : z < bayesCont P₀ P₁ κ (ENNReal.ofReal c₀) y) :
    ∀ᶠ c in 𝓝 c₀, z < bayesCont P₀ P₁ κ (ENNReal.ofReal c) y := by
  have hT := tendsto_ofReal_max_mul hz (f := fun c => c₀ / c)
    (continuousAt_const.div continuousAt_id hc₀.ne') (div_self hc₀.ne')
  filter_upwards [hT.eventually_lt_const h, eventually_gt_nhds hc₀] with c hc hcpos
  have ht1 : 1 ≤ ENNReal.ofReal (max 1 (c₀ / c)) := ENNReal.one_le_ofReal.2 (le_max_left _ _)
  have hle := bayesCont_le_mul_of_le P₀ P₁ κ ht1 ENNReal.ofReal_ne_top
    (ofReal_le_ofReal_max_mul hcpos c₀) y
  exact (ENNReal.mul_lt_mul_iff_right (zero_lt_one.trans_le ht1).ne' ENNReal.ofReal_ne_top).1
    (hc.trans_le hle)

private theorem lowerBd_ne_top (P₀ P₁ : Measure X) {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (c : ℝ≥0∞) :
    lowerBd P₀ P₁ κ c ≠ ∞ :=
  ne_top_of_le_ne_top hκ (lowerBd_le P₀ P₁ κ c)

private theorem continuousAt_lowerBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {κ : ℝ≥0∞}
    (hκ : κ ≠ ∞) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ContinuousAt (fun c : ℝ => (lowerBd P₀ P₁ κ (ENNReal.ofReal c)).toReal) c₀ := by
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · rcases lt_or_ge a' 0 with ha0 | ha0
    · exact Eventually.of_forall fun c => ha0.trans_le ENNReal.toReal_nonneg
    obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have hy : ENNReal.ofReal a'' < lowerBd P₀ P₁ κ (ENNReal.ofReal c₀) :=
      (ENNReal.ofReal_lt_iff_lt_toReal (ha0.trans ha'a''.le) (lowerBd_ne_top P₀ P₁ hκ _)).2 ha''
    have hyκ : ENNReal.ofReal a'' ≤ κ := hy.le.trans (lowerBd_le P₀ P₁ κ _)
    have hcont := lt_bayesCont_of_lt_lowerBd P₀ P₁ hκ (ENNReal.ofReal_pos.2 hc₀).ne'
      ENNReal.ofReal_ne_top hy
    filter_upwards [eventually_lt_bayesCont P₀ P₁ κ hc₀ ENNReal.ofReal_ne_top hcont]
      with c hc
    have hV : bayesValue P₀ P₁ κ (ENNReal.ofReal c) (ENNReal.ofReal a'') = ENNReal.ofReal a'' := by
      rw [bayesValue_eq P₀ P₁ hκ, min_eq_right hyκ, min_eq_left hc.le]
    have hmem : ENNReal.ofReal a'' ≤ lowerBd P₀ P₁ κ (ENNReal.ofReal c) := le_sSup ⟨hyκ, hV⟩
    calc a' < a'' := ha'a''
      _ = (ENNReal.ofReal a'').toReal := (ENNReal.toReal_ofReal (ha0.trans ha'a''.le)).symm
      _ ≤ _ := ENNReal.toReal_mono (lowerBd_ne_top P₀ P₁ hκ _) hmem
  · rcases lt_or_ge κ.toReal a' with hκa | hκa
    · exact Eventually.of_forall fun c =>
        (ENNReal.toReal_mono hκ (lowerBd_le P₀ P₁ κ _)).trans_lt hκa
    obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have hy : lowerBd P₀ P₁ κ (ENNReal.ofReal c₀) < ENNReal.ofReal a'' :=
      (ENNReal.lt_ofReal_iff_toReal_lt (lowerBd_ne_top P₀ P₁ hκ _)).2 ha'a''
    have hyκ : ENNReal.ofReal a'' ≤ κ :=
      (ENNReal.ofReal_le_iff_le_toReal hκ).2 (ha''.le.trans hκa)
    have hV := bayesValue_lt_self P₀ P₁ hy hyκ
    filter_upwards [eventually_bayesValue_lt P₀ P₁ hκ hc₀ hV] with c hc
    have hle : lowerBd P₀ P₁ κ (ENNReal.ofReal c) ≤ ENNReal.ofReal a'' :=
      not_lt.1 fun h => hc.ne (bayesValue_eq_self_of_lt_lowerBd P₀ P₁ hκ h)
    calc (lowerBd P₀ P₁ κ (ENNReal.ofReal c)).toReal ≤ (ENNReal.ofReal a'').toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = a'' := ENNReal.toReal_ofReal (ENNReal.toReal_nonneg.trans ha'a''.le)
      _ < a' := ha''

private theorem continuousAt_upperBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {κ : ℝ≥0∞}
    (hκ : κ ≠ ∞) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ContinuousAt (fun c : ℝ => (upperBd P₀ P₁ κ (ENNReal.ofReal c)).toReal) c₀ := by
  have hfin : ∀ᶠ c in 𝓝 c₀, upperBd P₀ P₁ κ (ENNReal.ofReal c) ≠ ∞ := by
    filter_upwards [eventually_gt_nhds hc₀] with c hc
    exact (upperBd_lt_top P₀ P₁ hκ (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).ne
  have hB₀ : upperBd P₀ P₁ κ (ENNReal.ofReal c₀) ≠ ∞ :=
    (upperBd_lt_top P₀ P₁ hκ (ENNReal.ofReal_pos.2 hc₀).ne' ENNReal.ofReal_ne_top).ne
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · rcases lt_or_ge a' κ.toReal with hκa | hκa
    · filter_upwards [hfin] with c hc
      exact hκa.trans_le (ENNReal.toReal_mono hc (le_upperBd P₀ P₁ κ _))
    obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have ha0 : 0 ≤ a'' := ENNReal.toReal_nonneg.trans (hκa.trans ha'a''.le)
    have hy : ENNReal.ofReal a'' < upperBd P₀ P₁ κ (ENNReal.ofReal c₀) :=
      (ENNReal.ofReal_lt_iff_lt_toReal ha0 hB₀).2 ha''
    have hκy : κ ≤ ENNReal.ofReal a'' := by
      rw [← ENNReal.ofReal_toReal hκ]; exact ENNReal.ofReal_le_ofReal (hκa.trans ha'a''.le)
    have hV := bayesValue_lt_of_lt_upperBd P₀ P₁ hκy hy
    filter_upwards [eventually_bayesValue_lt P₀ P₁ hκ hc₀ hV, hfin] with c hc hcfin
    have hle : ENNReal.ofReal a'' ≤ upperBd P₀ P₁ κ (ENNReal.ofReal c) :=
      not_lt.1 fun h => hc.ne (bayesValue_eq_of_upperBd_lt P₀ P₁ h)
    calc a' < a'' := ha'a''
      _ = (ENNReal.ofReal a'').toReal := (ENNReal.toReal_ofReal ha0).symm
      _ ≤ _ := ENNReal.toReal_mono hcfin hle
  · obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have hy : upperBd P₀ P₁ κ (ENNReal.ofReal c₀) < ENNReal.ofReal a'' :=
      (ENNReal.lt_ofReal_iff_toReal_lt hB₀).2 ha'a''
    have hκy : κ ≤ ENNReal.ofReal a'' := (le_upperBd P₀ P₁ κ _).trans hy.le
    have hcont := lt_bayesCont_of_upperBd_lt P₀ P₁ hκ (ENNReal.ofReal_pos.2 hc₀).ne'
      ENNReal.ofReal_ne_top hy
    filter_upwards [eventually_lt_bayesCont P₀ P₁ κ hc₀ hκ hcont] with c hc
    have hV : bayesValue P₀ P₁ κ (ENNReal.ofReal c) (ENNReal.ofReal a'') = κ := by
      rw [bayesValue_eq P₀ P₁ hκ, min_eq_left hκy, min_eq_left hc.le]
    have hle : upperBd P₀ P₁ κ (ENNReal.ofReal c) ≤ ENNReal.ofReal a'' := sInf_le ⟨hκy, hV⟩
    calc (upperBd P₀ P₁ κ (ENNReal.ofReal c)).toReal ≤ (ENNReal.ofReal a'').toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = a'' := ENNReal.toReal_ofReal (ENNReal.toReal_nonneg.trans ha'a''.le)
      _ < a' := ha''

/-! ### The boundaries for large and small sampling costs -/

private theorem lowerBd_eq_of_le (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hcκ : κ ≤ c) : lowerBd P₀ P₁ κ c = κ := by
  refine le_antisymm (lowerBd_le P₀ P₁ κ c) (le_sSup ⟨le_rfl, ?_⟩)
  rw [bayesValue_eq P₀ P₁ hκ, min_self]
  refine min_eq_left ?_
  calc κ ≤ c := hcκ
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * (1 + κ) := by gcongr; exact le_self_add
    _ ≤ _ := mul_le_bayesCont P₀ P₁ κ c _

private theorem upperBd_eq_of_le (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {κ c : ℝ≥0∞}
    (hκ : κ ≠ ∞) (hcκ : κ ≤ c) : upperBd P₀ P₁ κ c = κ := by
  refine le_antisymm (sInf_le ⟨le_rfl, ?_⟩) (le_upperBd P₀ P₁ κ c)
  have h := lowerBd_eq_of_le P₀ P₁ hκ hcκ
  have := bayesValue_lowerBd P₀ P₁ (c := c) hκ
  rwa [h] at this

private theorem min_le_sqrt_mul (κ y : ℝ≥0∞) :
    min κ y ≤ κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) := by
  have hsq : ∀ x : ℝ≥0∞, x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  rcases le_total κ y with h | h
  · rw [min_eq_left h]
    calc κ = κ ^ (1 / 2 : ℝ) * κ ^ (1 / 2 : ℝ) := (hsq κ).symm
      _ ≤ _ := by gcongr
  · rw [min_eq_right h]
    calc y = y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) := (hsq y).symm
      _ ≤ _ := by gcongr

/-- `m`-step bound: observing `m` times and then taking the better decision costs at most
`m c (1 + y)` in sampling and `√(κ y) H^m` in decision loss, where `H` is the Hellinger
affinity `∫ √(dP₁/dP₀) dP₀`. -/
private theorem bayesValue_le_hellinger (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (c : ℝ≥0∞) (m : ℕ)
    (y : ℝ≥0∞) :
    bayesValue P₀ P₁ κ c y ≤ m * c * (1 + y) + κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
      (∫⁻ x, P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) ∂P₀) ^ m := by
  set H := ∫⁻ x, P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) ∂P₀ with hH
  have hr : ∫⁻ x, P₁.rnDeriv P₀ x ∂P₀ = 1 := by
    rw [Measure.lintegral_rnDeriv h₁₀, measure_univ]
  have hmr : Measurable fun x => P₁.rnDeriv P₀ x := Measure.measurable_rnDeriv _ _
  have hms : Measurable fun x => P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) := hmr.pow_const _
  induction m generalizing y with
  | zero =>
    simpa using (bayesValue_le P₀ P₁ κ c y).trans (min_le_sqrt_mul κ y)
  | succ m ih =>
    calc bayesValue P₀ P₁ κ c y ≤ bayesCont P₀ P₁ κ c y := bayesValue_le_cont P₀ P₁ hκ c y
      _ ≤ c * (1 + y) + ∫⁻ x, (m * c * (1 + y * P₁.rnDeriv P₀ x) +
            κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * H ^ m * P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ)) ∂P₀ := by
          refine add_le_add le_rfl (lintegral_mono fun x => (ih _).trans_eq ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]; ring
      _ = c * (1 + y) + (m * c * (1 + y) + κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * H ^ m * H) := by
          have h2 : Measurable fun x => 1 + y * P₁.rnDeriv P₀ x :=
            measurable_const.add (measurable_const.mul hmr)
          have h1 : Measurable fun x => (m : ℝ≥0∞) * c * (1 + y * P₁.rnDeriv P₀ x) :=
            measurable_const.mul h2
          rw [lintegral_add_left h1, lintegral_const_mul _ h2, lintegral_const_mul _ hms,
            lintegral_add_left measurable_const, lintegral_const_mul _ hmr, hr, ← hH]
          simp
      _ = (↑(m + 1) : ℝ≥0∞) * c * (1 + y) + κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * H ^ (m + 1) := by
          push_cast; ring

/-- The Hellinger affinity of two different laws is less than one. -/
private theorem hellinger_lt_one {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (hne : P₀ ≠ P₁) :
    ∫⁻ x, P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) ∂P₀ < 1 := by
  set f : X → ℝ := fun x => (P₁.rnDeriv P₀ x).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hlin : ∫⁻ x, P₁.rnDeriv P₀ x ∂P₀ = 1 := by
    rw [Measure.lintegral_rnDeriv h₁₀, measure_univ]
  have hfi : Integrable f P₀ :=
    integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
      (by rw [hlin]; exact ENNReal.one_ne_top)
  have hfint : ∫ x, f x ∂P₀ = 1 := by
    rw [hf, Measure.integral_toReal_rnDeriv h₁₀]; simp
  set g : X → ℝ := fun x => Real.sqrt (f x) with hg
  have hgm : Measurable g := hfm.sqrt
  have hgle : ∀ x, g x ≤ (1 + f x) / 2 := fun x => by
    have h1 := Real.sq_sqrt (hf0 x)
    nlinarith [sq_nonneg (g x - 1), Real.sqrt_nonneg (f x)]
  have hgi : Integrable g P₀ := by
    refine Integrable.mono' ((integrable_const 1).add hfi |>.div_const 2) hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hgle x
  have hsq : ∀ x, (g x - 1) ^ 2 = f x - 2 * g x + 1 := fun x => by
    have h1 := Real.sq_sqrt (hf0 x)
    simp only [hg] at h1 ⊢
    nlinarith
  have hint : ∫ x, (g x - 1) ^ 2 ∂P₀ = 2 - 2 * ∫ x, g x ∂P₀ := by
    simp_rw [hsq]
    have e1 : ∫ x, (f x - 2 * g x + 1) ∂P₀ = ∫ x, (f x - 2 * g x) ∂P₀ + ∫ _, (1 : ℝ) ∂P₀ :=
      integral_add (hfi.sub (hgi.const_mul 2)) (integrable_const 1)
    have e2 : ∫ x, (f x - 2 * g x) ∂P₀ = ∫ x, f x ∂P₀ - ∫ x, 2 * g x ∂P₀ :=
      integral_sub hfi (hgi.const_mul 2)
    rw [e1, e2, integral_const_mul, hfint]
    simp; ring
  have hglt : ∫ x, g x ∂P₀ < 1 := by
    by_contra hge
    push Not at hge
    have hsqi : Integrable (fun x => (g x - 1) ^ 2) P₀ := by
      simp_rw [hsq]; exact (hfi.sub (hgi.const_mul 2)).add (integrable_const 1)
    have hzero : ∫ x, (g x - 1) ^ 2 ∂P₀ = 0 :=
      le_antisymm (by rw [hint]; linarith) (integral_nonneg fun x => sq_nonneg _)
    rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsqi] at hzero
    have hae : P₁.rnDeriv P₀ =ᵐ[P₀] 1 := by
      filter_upwards [hzero, Measure.rnDeriv_lt_top P₁ P₀] with x hx hxt
      have hg1 : g x = 1 := by
        have : (g x - 1) ^ 2 = 0 := hx
        nlinarith [sq_nonneg (g x - 1)]
      have hf1 : f x = 1 := by
        have h1 := Real.sq_sqrt (hf0 x)
        rw [← h1]; simp only [hg] at hg1; rw [hg1]; norm_num
      simp only [hf] at hf1
      simpa using (ENNReal.toReal_eq_one_iff _).1 hf1
    refine hne ?_
    rw [← Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀, withDensity_congr_ae hae, withDensity_one]
  have hlg : ∫⁻ x, P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) ∂P₀ = ENNReal.ofReal (∫ x, g x ∂P₀) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun x => Real.sqrt_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top P₁ P₀] with x hx
    change P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (P₁.rnDeriv P₀ x).toReal)
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hx.ne]
  rw [hlg, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hglt

/-- For a small enough sampling cost the lower boundary is as small as we like. -/
private theorem exists_lowerBd_lt (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (hne : P₀ ≠ P₁) {κ : ℝ≥0∞} (hκ0 : κ ≠ 0)
    (hκ : κ ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ lowerBd P₀ P₁ κ (ENNReal.ofReal c) < ε := by
  set H := ∫⁻ x, P₁.rnDeriv P₀ x ^ (1 / 2 : ℝ) ∂P₀
  set y := min ε κ / 2 with hy
  have hmin0 : min ε κ ≠ 0 := (lt_min (pos_iff_ne_zero.2 hε) (pos_iff_ne_zero.2 hκ0)).ne'
  have hmintop : min ε κ ≠ ∞ := ne_top_of_le_ne_top hκ (min_le_right _ _)
  have hy0 : y ≠ 0 := (ENNReal.half_pos hmin0).ne'
  have hytop : y ≠ ∞ := ENNReal.div_ne_top hmintop two_ne_zero
  have hyε : y < ε := (ENNReal.half_lt_self hmin0 hmintop).trans_le (min_le_left _ _)
  have hyκ : y ≤ κ := (ENNReal.half_le_self).trans (min_le_right _ _)
  have hy2 : (0 : ℝ≥0∞) < y / 2 := ENNReal.half_pos hy0
  -- the decision-loss term
  have hK : κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hκ)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hytop)
  have hT : Tendsto (fun m : ℕ => κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * H ^ m) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hellinger_lt_one h₁₀ hne)) (Or.inr hK)
    rwa [mul_zero] at this
  obtain ⟨m, hm⟩ := (hT.eventually_lt_const hy2).exists
  -- the sampling term
  have hT' : Tendsto (fun c : ℝ => (m : ℝ≥0∞) * ENNReal.ofReal c * (1 + y)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun c : ℝ => ENNReal.ofReal c) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.natCast_ne_top m))
    have h3 := ENNReal.Tendsto.mul_const h2
      (Or.inr (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hytop⟩))
    simpa using h3
  obtain ⟨c, hc, hcpos⟩ := ((hT'.eventually_lt_const hy2).and self_mem_nhdsWithin).exists
  refine ⟨c, hcpos, ?_⟩
  have hV : bayesValue P₀ P₁ κ (ENNReal.ofReal c) y < y := by
    calc bayesValue P₀ P₁ κ (ENNReal.ofReal c) y ≤ m * ENNReal.ofReal c * (1 + y) +
          κ ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) * H ^ m :=
          bayesValue_le_hellinger P₀ P₁ h₁₀ hκ _ m y
      _ < y / 2 + y / 2 := ENNReal.add_lt_add hc hm
      _ = y := ENNReal.add_halves y
  have hle : lowerBd P₀ P₁ κ (ENNReal.ofReal c) ≤ y :=
    not_lt.1 fun h => hV.ne (bayesValue_eq_self_of_lt_lowerBd P₀ P₁ hκ h)
  exact hle.trans_lt hyε

/-- **Choice of the sampling cost.** For every ratio `ρ > 1` there is a sampling cost whose
boundaries have ratio exactly `ρ`. -/
private theorem exists_upperBd_eq_mul_lowerBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (hne : P₀ ≠ P₁) {κ : ℝ≥0∞} (hκ0 : κ ≠ 0)
    (hκ : κ ≠ ∞) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ c : ℝ, 0 < c ∧ (upperBd P₀ P₁ κ (ENNReal.ofReal c)).toReal =
      ρ * (lowerBd P₀ P₁ κ (ENNReal.ofReal c)).toReal := by
  have hκr : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκ
  obtain ⟨c₁, hc₁, hlt⟩ := exists_lowerBd_lt P₀ P₁ h₁₀ hne hκ0 hκ
    (ε := ENNReal.ofReal (κ.toReal / ρ)) (ENNReal.ofReal_pos.2 (by positivity)).ne'
  set c₂ := max c₁ κ.toReal + 1
  have hc₁₂ : c₁ ≤ c₂ := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hκc₂ : κ ≤ ENNReal.ofReal c₂ := by
    rw [← ENNReal.ofReal_toReal hκ]
    exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
  set F : ℝ → ℝ := fun c => (upperBd P₀ P₁ κ (ENNReal.ofReal c)).toReal -
    ρ * (lowerBd P₀ P₁ κ (ENNReal.ofReal c)).toReal with hF
  have hF₂ : F c₂ ≤ 0 := by
    simp only [hF, upperBd_eq_of_le P₀ P₁ hκ hκc₂, lowerBd_eq_of_le P₀ P₁ hκ hκc₂]
    nlinarith
  have hF₁ : 0 ≤ F c₁ := by
    have h1 : (lowerBd P₀ P₁ κ (ENNReal.ofReal c₁)).toReal < κ.toReal / ρ := by
      have := (ENNReal.toReal_lt_toReal (lowerBd_ne_top P₀ P₁ hκ _) ENNReal.ofReal_ne_top).2 hlt
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have h2 : κ.toReal ≤ (upperBd P₀ P₁ κ (ENNReal.ofReal c₁)).toReal :=
      ENNReal.toReal_mono (upperBd_lt_top P₀ P₁ hκ (ENNReal.ofReal_pos.2 hc₁).ne'
        ENNReal.ofReal_ne_top).ne (le_upperBd P₀ P₁ κ _)
    have h3 : ρ * (lowerBd P₀ P₁ κ (ENNReal.ofReal c₁)).toReal < κ.toReal := by
      have := mul_lt_mul_of_pos_left h1 (zero_lt_one.trans hρ)
      rwa [mul_div_cancel₀ _ (zero_lt_one.trans hρ).ne'] at this
    simp only [hF]; linarith
  have hcont : ContinuousOn F (Set.Icc c₁ c₂) := fun c hc =>
    ((continuousAt_upperBd P₀ P₁ hκ (hc₁.trans_le hc.1)).sub
      ((continuousAt_lowerBd P₀ P₁ hκ (hc₁.trans_le hc.1)).const_mul ρ)).continuousWithinAt
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc' hc₁₂ hcont ⟨hF₂, hF₁⟩
  exact ⟨c, hc₁.trans_le hc.1, by simp only [hF] at hFc; linarith⟩

/-! ### Likelihood ratios, stopping times and the Markov property -/

/-- The likelihood ratio `Rₙ = ∏_{i=1}^{n} (dP₁/dP₀)(Xᵢ)` of the first `n` observations, the
product over the coordinates `i < n` of `ℕ → X`. -/
private noncomputable def lrProd (P₀ P₁ : Measure X) (n : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  ∏ i ∈ range n, P₁.rnDeriv P₀ (ω i)

private theorem lrProd_zero (P₀ P₁ : Measure X) (ω : ℕ → X) : lrProd P₀ P₁ 0 ω = 1 := by
  simp [lrProd]

private theorem lrProd_succ (P₀ P₁ : Measure X) (n : ℕ) (ω : ℕ → X) :
    lrProd P₀ P₁ (n + 1) ω = lrProd P₀ P₁ n ω * P₁.rnDeriv P₀ (ω n) := by
  simp [lrProd, prod_range_succ]

private theorem measurable_lrProd (P₀ P₁ : Measure X) (n : ℕ) :
    Measurable[observationFiltration X n] (lrProd P₀ P₁ n) :=
  Finset.measurable_prod _ fun _ hi =>
    (Measure.measurable_rnDeriv _ _).comp
      (measurable_coord_observationFiltration (mem_range.1 hi))

/-! ### The potential argument -/

/-- Expected sampling cost at step `k` of a stopping time `T`, from the initial state `ℓ₀`. -/
private noncomputable def stepCost (P₀ P₁ : Measure X) (c ℓ₀ : ℝ≥0∞) (T : (ℕ → X) → WithTop ℕ)
    (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (k : WithTop ℕ) < T ω}, c * (1 + ℓ₀ * lrProd P₀ P₁ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Value of the state at which `T` stops, on the event `{T = k}`. -/
private noncomputable def stopValue (P₀ P₁ : Measure X) (κ c ℓ₀ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | T ω = k}, bayesValue P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Value of the state at time `n` on the event that `T` has not stopped before `n`. -/
private noncomputable def remValue (P₀ P₁ : Measure X) (κ c ℓ₀ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (n : WithTop ℕ) ≤ T ω}, bayesValue P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

private theorem remValue_eq (P₀ P₁ : Measure X) (κ c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    remValue P₀ P₁ κ c ℓ₀ T n = stopValue P₀ P₁ κ c ℓ₀ T n +
      ∫⁻ ω in {ω | (n : WithTop ℕ) < T ω}, bayesValue P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  have hset : {ω | (n : WithTop ℕ) ≤ T ω} = {ω | T ω = n} ∪ {ω | (n : WithTop ℕ) < T ω} := by
    ext ω; simp only [Set.mem_union, Set.mem_ofPred_eq, le_iff_eq_or_lt, eq_comm]
  have hS : MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < T ω} :=
    hT.measurableSet_gt n
  rw [remValue, stopValue, hset, lintegral_union ((observationFiltration X).le n _ hS)]
  refine Set.disjoint_left.2 fun ω h1 h2 => ?_
  simp only [Set.mem_ofPred_eq] at h1 h2
  rw [h1] at h2
  exact lt_irrefl _ h2

private theorem setLIntegral_bayesCont_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (κ c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    ∫⁻ ω in {ω | (n : WithTop ℕ) < T ω}, bayesCont P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) =
      stepCost P₀ P₁ c ℓ₀ T n + remValue P₀ P₁ κ c ℓ₀ T (n + 1) := by
  have hY : Measurable[observationFiltration X n] fun ω => ℓ₀ * lrProd P₀ P₁ n ω :=
    measurable_const.mul (measurable_lrProd P₀ P₁ n)
  have hYm : Measurable fun ω => ℓ₀ * lrProd P₀ P₁ n ω :=
    hY.mono ((observationFiltration X).le n) le_rfl
  have hh : Measurable (Function.uncurry fun y x => bayesValue P₀ P₁ κ c (y * P₁.rnDeriv P₀ x)) :=
    (measurable_bayesValue P₀ P₁ κ c).comp
      (measurable_fst.mul ((Measure.measurable_rnDeriv _ _).comp measurable_snd))
  have hS : MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < T ω} :=
    hT.measurableSet_gt n
  simp only [bayesCont]
  rw [lintegral_add_left (f := fun ω => c * (1 + ℓ₀ * lrProd P₀ P₁ n ω))
    (measurable_const.mul (measurable_const.add hYm)), stepCost, remValue,
    setOfPred_natCast_add_one_le_eq,
    ← setLIntegral_infinitePi_coord P₀ n hS hY hh]
  congr 2
  funext ω
  rw [lrProd_succ, mul_assoc]

private theorem remValue_zero (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (κ c ℓ₀ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) :
    remValue P₀ P₁ κ c ℓ₀ T 0 = bayesValue P₀ P₁ κ c ℓ₀ := by
  simp [remValue, lrProd_zero]

/-- For any stopping time `T` and horizon `n`, the value at the initial state `ℓ₀` is at most the
expected sampling cost of `T` before `min T n`, plus the value at the state where `T` stops before
`n`, plus the value at time `n` on `{n ≤ T}`. -/
private theorem bayesValue_le_sum_add_remValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    bayesValue P₀ P₁ κ c ℓ₀ ≤ ∑ k ∈ range n,
      (stepCost P₀ P₁ c ℓ₀ T k + stopValue P₀ P₁ κ c ℓ₀ T k) + remValue P₀ P₁ κ c ℓ₀ T n := by
  induction n with
  | zero => simp [remValue_zero]
  | succ n ih =>
    refine ih.trans ?_
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [remValue_eq P₀ P₁ κ c ℓ₀ hT, add_comm (stepCost _ _ _ _ _ _), add_assoc,
      ← setLIntegral_bayesCont_eq P₀ P₁ κ c ℓ₀ hT]
    refine add_le_add le_rfl (lintegral_mono fun ω => bayesValue_le_cont P₀ P₁ hκ c _)

/-- If continuing is optimal at the state of every time at which the stopping time `T` continues,
the bound of `bayesValue_le_sum_add_remValue` is reversed: the expected sampling cost of `T`
before `min T n`, plus the value at the state where `T` stops before `n`, plus the value at time
`n` on `{n ≤ T}`, is at most the value at the initial state `ℓ₀`. -/
private theorem sum_add_remValue_le_bayesValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (κ c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T)
    (hcont : ∀ n : ℕ, ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P₀), (n : WithTop ℕ) < T ω →
      bayesCont P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω) ≤ bayesValue P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω))
    (n : ℕ) :
    ∑ k ∈ range n, (stepCost P₀ P₁ c ℓ₀ T k + stopValue P₀ P₁ κ c ℓ₀ T k) +
      remValue P₀ P₁ κ c ℓ₀ T n ≤ bayesValue P₀ P₁ κ c ℓ₀ := by
  induction n with
  | zero => simp [remValue_zero]
  | succ n ih =>
    refine le_trans ?_ ih
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [remValue_eq P₀ P₁ κ c ℓ₀ hT n, add_comm (stepCost _ _ _ _ _ _), add_assoc,
      ← setLIntegral_bayesCont_eq P₀ P₁ κ c ℓ₀ hT]
    refine add_le_add le_rfl (setLIntegral_mono_ae ?_ ?_)
    · exact (measurable_bayesValue P₀ P₁ κ c).comp
        (measurable_const.mul ((measurable_lrProd P₀ P₁ n).mono
          ((observationFiltration X).le n) le_rfl)) |>.aemeasurable
    · filter_upwards [hcont n] with ω hω hmem
      exact hω hmem

/-! ### The risk of a test -/

private theorem measurableSet_eq_stoppingTime {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (k : ℕ) :
    MeasurableSet[observationFiltration X k] {ω | T ω = k} :=
  hT.measurableSet_eq k

private theorem measurableSet_inter_eq_stoppingTime {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) {D : Set (ℕ → X)}
    (hD : MeasurableSet[hT.measurableSpace] D) (k : ℕ) :
    MeasurableSet[observationFiltration X k] (D ∩ {ω | T ω = k}) := by
  have h := ((hT.measurableSet D).1 hD).2 k
  have hset : D ∩ {ω | T ω = k} = (D ∩ {ω | T ω ≤ k}) ∩ {ω | T ω = k} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hω, h'⟩; exact ⟨⟨hω, h'.le⟩, h'⟩
    · rintro ⟨⟨hω, -⟩, h'⟩; exact ⟨hω, h'⟩
  rw [hset]
  exact h.inter (measurableSet_eq_stoppingTime hT k)

private theorem tsum_measure_inter_eq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → WithTop ℕ} {E : Set Ω} (hE : ∀ k : ℕ, MeasurableSet (E ∩ {ω | T ω = k})) :
    ∑' k : ℕ, μ (E ∩ {ω | T ω = k}) ≤ μ E := by
  rw [← measure_iUnion _ hE]
  · exact measure_mono (Set.iUnion_subset fun k => Set.inter_subset_left)
  · intro i j hij
    refine Set.disjoint_left.2 fun ω h1 h2 => hij ?_
    have := h1.2.symm.trans h2.2
    exact_mod_cast this

/-- The expected sampling cost of a stopping time, written under `P₀`. -/
private theorem tsum_stepCost (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    ∑' k, stepCost P₀ P₁ c ℓ₀ T k =
      c * (∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) +
        ℓ₀ * ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁)) := by
  have hS : ∀ n : ℕ, MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < T ω} :=
    fun n => hT.measurableSet_gt n
  have hSm : ∀ k : ℕ, MeasurableSet {ω | (k : WithTop ℕ) < T ω} := fun k =>
    (observationFiltration X).le k _ (hS k)
  have hk : ∀ k, stepCost P₀ P₁ c ℓ₀ T k =
      c * (Measure.infinitePi (fun _ : ℕ => P₀) {ω | (k : WithTop ℕ) < T ω} +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) {ω | (k : WithTop ℕ) < T ω}) := by
    intro k
    have hlr : Measurable (lrProd P₀ P₁ k) :=
      (measurable_lrProd P₀ P₁ k).mono ((observationFiltration X).le k) le_rfl
    rw [stepCost, lintegral_const_mul (f := fun ω => 1 + ℓ₀ * lrProd P₀ P₁ k ω) _
      (measurable_const.add (measurable_const.mul hlr)),
      lintegral_add_left (f := fun _ => 1) measurable_const, setLIntegral_one,
      lintegral_const_mul _ hlr,
      infinitePi_apply_eq_setLIntegral_prod_rnDeriv P₀ P₁ h₁₀ k (hS k)]
    rfl
  simp_rw [hk]
  rw [ENNReal.tsum_mul_left, tsum_add, ENNReal.tsum_mul_left,
    lintegral_enat_eq_tsum _ hSm, lintegral_enat_eq_tsum _ hSm]

/-- The decision loss of a test `(T, D)` dominates the value at the stopping state. -/
private theorem tsum_stopValue_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (κ c ℓ₀ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) {D : Set (ℕ → X)}
    (hD : MeasurableSet[hT.measurableSpace] D) :
    ∑' k, stopValue P₀ P₁ κ c ℓ₀ T k ≤
      κ * Measure.infinitePi (fun _ : ℕ => P₀) D +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ := by
  have hDk := measurableSet_inter_eq_stoppingTime hT hD
  have hDck := measurableSet_inter_eq_stoppingTime hT hD.compl
  have hDm : MeasurableSet D := hT.measurableSpace_le D hD
  have hk : ∀ k, stopValue P₀ P₁ κ c ℓ₀ T k ≤
      κ * Measure.infinitePi (fun _ : ℕ => P₀) (D ∩ {ω | T ω = k}) +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (Dᶜ ∩ {ω | T ω = k}) := by
    intro k
    have hlr : Measurable (lrProd P₀ P₁ k) :=
      (measurable_lrProd P₀ P₁ k).mono ((observationFiltration X).le k) le_rfl
    calc stopValue P₀ P₁ κ c ℓ₀ T k ≤ ∫⁻ ω in {ω | T ω = k},
          (D.indicator (fun _ => κ) ω + Dᶜ.indicator (fun ω => ℓ₀ * lrProd P₀ P₁ k ω) ω)
            ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ D
          · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
              add_zero]
            exact (bayesValue_le P₀ P₁ κ c _).trans (min_le_left _ _)
          · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem hω, zero_add]
            exact (bayesValue_le P₀ P₁ κ c _).trans (min_le_right _ _)
      _ = κ * Measure.infinitePi (fun _ : ℕ => P₀) (D ∩ {ω | T ω = k}) +
          ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (Dᶜ ∩ {ω | T ω = k}) := by
          rw [lintegral_add_left (measurable_const.indicator hDm),
            lintegral_indicator_const hDm, Measure.restrict_apply hDm,
            lintegral_indicator hDm.compl, Measure.restrict_restrict hDm.compl,
            lintegral_const_mul _ hlr,
            infinitePi_apply_eq_setLIntegral_prod_rnDeriv P₀ P₁ h₁₀ k (hDck k)]
          rfl
  calc ∑' k, stopValue P₀ P₁ κ c ℓ₀ T k ≤ ∑' k : ℕ,
        (κ * Measure.infinitePi (fun _ : ℕ => P₀) (D ∩ {ω | T ω = k}) +
          ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (Dᶜ ∩ {ω | T ω = k})) :=
        tsum_le_tsum hk
    _ = κ * ∑' k : ℕ, Measure.infinitePi (fun _ : ℕ => P₀) (D ∩ {ω | T ω = k}) +
          ℓ₀ * ∑' k : ℕ, Measure.infinitePi (fun _ : ℕ => P₁) (Dᶜ ∩ {ω | T ω = k}) := by
        rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        · exact tsum_measure_inter_eq_le _ fun k => (observationFiltration X).le k _ (hDk k)
        · exact tsum_measure_inter_eq_le _ fun k => (observationFiltration X).le k _ (hDck k)

/-- **Lower bound for the Bayes risk of any test.** -/
private theorem bayesValue_le_risk (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (c ℓ₀ : ℝ≥0∞)
    {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    {D : Set (ℕ → X)} (hD : MeasurableSet[hT.measurableSpace] D)
    (hT₀ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) ≠ ∞) :
    bayesValue P₀ P₁ κ c ℓ₀ ≤
      c * (∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) +
        ℓ₀ * ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁)) +
      (κ * Measure.infinitePi (fun _ : ℕ => P₀) D +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ) := by
  have hSm : ∀ k : ℕ, MeasurableSet {ω | (k : WithTop ℕ) < T ω} := fun k =>
    (observationFiltration X).le k _ (hT.measurableSet_gt k)
  set S := ∑' k, (stepCost P₀ P₁ c ℓ₀ T k + stopValue P₀ P₁ κ c ℓ₀ T k) with hSdef
  have hbound : ∀ n : ℕ, bayesValue P₀ P₁ κ c ℓ₀ ≤
      S + κ * Measure.infinitePi (fun _ : ℕ => P₀) {ω | (n : WithTop ℕ) < T ω} := by
    intro n
    refine (bayesValue_le_sum_add_remValue P₀ P₁ hκ c ℓ₀ hT (n + 1)).trans (add_le_add
      (sum_le_tsum _) ?_)
    rw [remValue, setOfPred_natCast_add_one_le_eq, ← setLIntegral_const]
    exact lintegral_mono fun ω => (bayesValue_le P₀ P₁ κ c _).trans (min_le_left _ _)
  have htend : Tendsto (fun n : ℕ =>
      S + κ * Measure.infinitePi (fun _ : ℕ => P₀) {ω | (n : WithTop ℕ) < T ω}) atTop (𝓝 S) := by
    have h0 : Tendsto (fun n : ℕ =>
        Measure.infinitePi (fun _ : ℕ => P₀) {ω | (n : WithTop ℕ) < T ω}) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by rwa [← lintegral_enat_eq_tsum _ hSm])
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h0 (Or.inr hκ))
  refine (ge_of_tendsto' htend hbound).trans ?_
  rw [hSdef, tsum_add, tsum_stepCost P₀ P₁ h₁₀ c ℓ₀ hT]
  exact add_le_add le_rfl (tsum_stopValue_le P₀ P₁ h₁₀ κ c ℓ₀ hT hD)

/-! ### The SPRT attains the Bayes value -/

private theorem ae_rnDeriv_coord_pos_lt_top (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₀₁ : P₀ ≪ P₁) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P₀),
      ∀ i, 0 < P₁.rnDeriv P₀ (ω i) ∧ P₁.rnDeriv P₀ (ω i) < ∞ := by
  have h1 : ∀ᵐ x ∂P₀, 0 < P₁.rnDeriv P₀ x ∧ P₁.rnDeriv P₀ x < ∞ :=
    (Measure.rnDeriv_pos' h₀₁).and (Measure.rnDeriv_lt_top P₁ P₀)
  refine ae_all_iff.mpr fun i => ?_
  exact ae_of_ae_map (μ := Measure.infinitePi fun _ : ℕ => P₀) (f := fun ω : ℕ → X => ω i)
    (p := fun x => 0 < P₁.rnDeriv P₀ x ∧ P₁.rnDeriv P₀ x < ∞)
    (measurable_pi_apply i).aemeasurable
    (by rw [Measure.infinitePi_map_eval (fun _ : ℕ => P₀) i]; exact h1)

private theorem lrProd_eq_ofReal_exp (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (n : ℕ) {ω : ℕ → X}
    (hω : ∀ i, 0 < P₁.rnDeriv P₀ (ω i) ∧ P₁.rnDeriv P₀ (ω i) < ∞) :
    lrProd P₀ P₁ n ω = ENNReal.ofReal (Real.exp (llrSum P₀ P₁ h₁₀ h₀₁ n ω)) := by
  rw [lrProd, llrSum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  refine prod_congr rfl fun i _ => ?_
  have hpos : 0 < (P₁.rnDeriv P₀ (ω i)).toReal :=
    ENNReal.toReal_pos (hω i).1.ne' (hω i).2.ne
  rw [llr, Real.exp_log hpos, ENNReal.ofReal_toReal (hω i).2.ne]

private theorem llrSum_mem_Ioo_of_lt_sprtTime (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {a b : ℝ} (ha : a < 0)
    (hb : 0 < b) {n : ℕ} {ω : ℕ → X} (h : (n : WithTop ℕ) < sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) :
    llrSum P₀ P₁ h₁₀ h₀₁ n ω ∈ Set.Ioo a b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [llrSum, ha, hb]
  have h' := notMem_of_lt_hittingAfter h hn
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] at h'
  exact ⟨h'.1, h'.2⟩

/-- The events on which the SPRT stops at time `k` and accepts `P₀`, respectively `P₁`. -/
private theorem measurableSet_sprt_stop (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (a b : ℝ) (k : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    MeasurableSet[observationFiltration X k]
      ({ω | sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = k} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ k) ⁻¹' s) :=
  ((isStoppingTime_sprtTime P₀ P₁ h₁₀ h₀₁ a b).measurableSet_eq k).inter
    (adapted_llrSum P₀ P₁ h₁₀ h₀₁ k hs)

private theorem measure_sprt_accept_eq_tsum {μ : Measure (ℕ → X)} (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁)
    (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ {ω | ∃ n : ℕ, sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = n ∧ llrSum P₀ P₁ h₁₀ h₀₁ n ω ∈ s} =
      ∑' k : ℕ, μ ({ω | sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = k} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ k) ⁻¹' s) := by
  have hU : {ω | ∃ n : ℕ, sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = n ∧ llrSum P₀ P₁ h₁₀ h₀₁ n ω ∈ s} =
      ⋃ k : ℕ, ({ω | sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = k} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ k) ⁻¹' s) := by
    ext ω; simp
  rw [hU, measure_iUnion]
  · intro n m hnm
    refine Set.disjoint_left.mpr fun ω h1 h2 => hnm ?_
    have := h1.1.symm.trans h2.1
    exact_mod_cast this
  · exact fun k => (observationFiltration X).le k _
      (measurableSet_sprt_stop P₀ P₁ h₁₀ h₀₁ a b k hs)

/-- **The SPRT whose boundaries are the Bayes boundaries attains the Bayes value.** -/
private theorem sprt_risk_le_bayesValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {a b : ℝ} (ha : a < 0)
    (hb : 0 < b) {κ c ℓ₀ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hℓ0 : ℓ₀ ≠ 0) (hℓ : ℓ₀ ≠ ∞) (hA : ℓ₀ * ENNReal.ofReal (Real.exp a) = lowerBd P₀ P₁ κ c)
    (hB : ℓ₀ * ENNReal.ofReal (Real.exp b) = upperBd P₀ P₁ κ c) :
    c * (∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
          ∂Measure.infinitePi (fun _ : ℕ => P₀) +
        ℓ₀ * ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
          ∂Measure.infinitePi (fun _ : ℕ => P₁)) +
      (κ * Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b)) ≤
      bayesValue P₀ P₁ κ c ℓ₀ := by
  set N := sprtTime P₀ P₁ h₁₀ h₀₁ a b with hNdef
  have hN : IsStoppingTime (observationFiltration X) N := isStoppingTime_sprtTime P₀ P₁ h₁₀ h₀₁ a b
  have hcoord := ae_rnDeriv_coord_pos_lt_top P₀ P₁ h₀₁
  have hmono : StrictMono fun t : ℝ => ℓ₀ * ENNReal.ofReal (Real.exp t) := fun s t hst =>
    (ENNReal.mul_lt_mul_iff_right hℓ0 hℓ).2
      ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos t)).2 (Real.exp_lt_exp.2 hst))
  -- continuing is optimal while the SPRT continues
  have hcont : ∀ n : ℕ, ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P₀), (n : WithTop ℕ) < N ω →
      bayesCont P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω) ≤
        bayesValue P₀ P₁ κ c (ℓ₀ * lrProd P₀ P₁ n ω) := by
    intro n
    filter_upwards [hcoord] with ω hω hn
    have hmem := llrSum_mem_Ioo_of_lt_sprtTime P₀ P₁ h₁₀ h₀₁ ha hb hn
    rw [lrProd_eq_ofReal_exp P₀ P₁ h₁₀ h₀₁ n hω]
    refine (bayesValue_eq_cont P₀ P₁ hκ ?_ ?_).ge
    · rw [← hA]; exact hmono hmem.1
    · rw [← hB]; exact hmono hmem.2
  have hsum : ∑' k, (stepCost P₀ P₁ c ℓ₀ N k + stopValue P₀ P₁ κ c ℓ₀ N k) ≤
      bayesValue P₀ P₁ κ c ℓ₀ :=
    ENNReal.tsum_le_of_sum_range_le fun n =>
      le_self_add.trans (sum_add_remValue_le_bayesValue P₀ P₁ κ c ℓ₀ hN hcont n)
  rw [tsum_add, tsum_stepCost P₀ P₁ h₁₀ c ℓ₀ hN] at hsum
  refine le_trans (add_le_add le_rfl ?_) hsum
  -- the decision loss of the SPRT is the value at its stopping state
  set E₁ : ℕ → Set (ℕ → X) := fun k => {ω | N ω = k} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ k) ⁻¹' Set.Ici b
  set E₀ : ℕ → Set (ℕ → X) := fun k => {ω | N ω = k} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ k) ⁻¹' Set.Iic a
  have hE₁ : ∀ k, MeasurableSet[observationFiltration X k] (E₁ k) := fun k =>
    measurableSet_sprt_stop P₀ P₁ h₁₀ h₀₁ a b k measurableSet_Ici
  have hE₀ : ∀ k, MeasurableSet[observationFiltration X k] (E₀ k) := fun k =>
    measurableSet_sprt_stop P₀ P₁ h₁₀ h₀₁ a b k measurableSet_Iic
  have hacc1 : Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) =
      ∑' k, Measure.infinitePi (fun _ : ℕ => P₀) (E₁ k) :=
    measure_sprt_accept_eq_tsum P₀ P₁ h₁₀ h₀₁ a b measurableSet_Ici
  have hacc0 : Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b) =
      ∑' k, Measure.infinitePi (fun _ : ℕ => P₁) (E₀ k) :=
    measure_sprt_accept_eq_tsum P₀ P₁ h₁₀ h₀₁ a b measurableSet_Iic
  rw [hacc1, hacc0, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun k => ?_
  have hE₁m : MeasurableSet (E₁ k) := (observationFiltration X).le k _ (hE₁ k)
  have hE₀m : MeasurableSet (E₀ k) := (observationFiltration X).le k _ (hE₀ k)
  have hlr : Measurable (lrProd P₀ P₁ k) :=
    (measurable_lrProd P₀ P₁ k).mono ((observationFiltration X).le k) le_rfl
  have hEq : κ * Measure.infinitePi (fun _ : ℕ => P₀) (E₁ k) +
      ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (E₀ k) =
      ∫⁻ ω in {ω | N ω = k}, ((E₁ k).indicator (fun _ => κ) ω +
        (E₀ k).indicator (fun ω => ℓ₀ * lrProd P₀ P₁ k ω) ω)
          ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
    rw [lintegral_add_left (measurable_const.indicator hE₁m), lintegral_indicator_const hE₁m,
      Measure.restrict_apply hE₁m, Set.inter_eq_left.2 Set.inter_subset_left,
      lintegral_indicator hE₀m, Measure.restrict_restrict hE₀m,
      Set.inter_eq_left.2 Set.inter_subset_left, lintegral_const_mul _ hlr,
      infinitePi_apply_eq_setLIntegral_prod_rnDeriv P₀ P₁ h₁₀ k (hE₀ k)]
    rfl
  rw [hEq, stopValue]
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hcoord] with ω hω
  have hY := lrProd_eq_ofReal_exp P₀ P₁ h₁₀ h₀₁ k hω
  by_cases h1 : ω ∈ E₁ k
  · have h0 : ω ∉ E₀ k := fun h0 => by
      have := h1.2; have := h0.2
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic] at *
      linarith
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h0, add_zero]
    refine (bayesValue_eq_of_upperBd_le P₀ P₁ hκ0 hκ hc0 hc ?_).ge
    rw [hY, ← hB]
    exact hmono.monotone h1.2
  · rw [Set.indicator_of_notMem h1, zero_add]
    by_cases h0 : ω ∈ E₀ k
    · rw [Set.indicator_of_mem h0]
      refine (bayesValue_eq_of_le_lowerBd P₀ P₁ hκ ?_).ge
      rw [hY, ← hA]
      exact hmono.monotone h0.2
    · rw [Set.indicator_of_notMem h0]
      exact zero_le

/-! ### The Wald–Wolfowitz theorem -/

/-- For every loss `κ` the SPRT is Bayes for a suitable prior: the expected sample sizes satisfy
`E₀ N + ℓ₀ E₁ N ≤ E₀ T + ℓ₀ E₁ T` for a weight `ℓ₀` between `κ e^{-b}` and `κ e^{-a}`. -/
private theorem sprt_weighted_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) {D : Set (ℕ → X)}
    (hD : MeasurableSet[hT.measurableSpace] D)
    (hT₀ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) ≠ ∞)
    (hα : Measure.infinitePi (fun _ : ℕ => P₀) D ≤
      Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b))
    (hβ : Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ ≤
      Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b))
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) :
    ∃ ℓ₀ : ℝ≥0∞, ℓ₀ ≠ ∞ ∧ κ * ENNReal.ofReal (Real.exp (-b)) ≤ ℓ₀ ∧
      ℓ₀ ≤ κ * ENNReal.ofReal (Real.exp (-a)) ∧
      ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
          ∂Measure.infinitePi (fun _ : ℕ => P₀) +
        ℓ₀ * ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
          ∂Measure.infinitePi (fun _ : ℕ => P₁) ≤
      ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) +
        ℓ₀ * ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁) := by
  obtain ⟨c, hc, hBA⟩ := exists_upperBd_eq_mul_lowerBd P₀ P₁ h₁₀ hne hκ0 hκ
    (ρ := Real.exp (b - a)) (Real.one_lt_exp_iff.2 (by linarith))
  set A := lowerBd P₀ P₁ κ (ENNReal.ofReal c) with hAdef
  set B := upperBd P₀ P₁ κ (ENNReal.ofReal c) with hBdef
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hA0 : A ≠ 0 := (lowerBd_pos P₀ P₁ hκ0 hκ hc0).ne'
  have hAtop : A ≠ ∞ := lowerBd_ne_top P₀ P₁ hκ _
  have hBtop : B ≠ ∞ := (upperBd_lt_top P₀ P₁ hκ hc0 ENNReal.ofReal_ne_top).ne
  set ℓ₀ := ENNReal.ofReal (Real.exp (-a)) * A with hℓdef
  have hℓ0 : ℓ₀ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hA0
  have hℓ : ℓ₀ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop
  have hexp : ∀ s t : ℝ, ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (Real.exp t) =
      ENNReal.ofReal (Real.exp (s + t)) := fun s t => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos s).le, Real.exp_add]
  have hAeq : ℓ₀ * ENNReal.ofReal (Real.exp a) = A := by
    rw [hℓdef, mul_comm _ A, mul_assoc, hexp, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one,
      mul_one]
  have hBeq : ℓ₀ * ENNReal.ofReal (Real.exp b) = B := by
    rw [hℓdef, mul_comm _ A, mul_assoc, hexp, ← ENNReal.ofReal_toReal hBtop, hBA,
      ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hAtop, mul_comm, neg_add_eq_sub]
  refine ⟨ℓ₀, hℓ, ?_, ?_, ?_⟩
  · calc κ * ENNReal.ofReal (Real.exp (-b)) ≤ B * ENNReal.ofReal (Real.exp (-b)) := by
          gcongr; exact le_upperBd P₀ P₁ κ _
      _ = ℓ₀ := by
          rw [← hBeq, mul_assoc, hexp, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  · rw [hℓdef, mul_comm]
    gcongr
    exact lowerBd_le P₀ P₁ κ _
  · have h1 := sprt_risk_le_bayesValue P₀ P₁ h₁₀ h₀₁ ha hb hκ0 hκ hc0 ENNReal.ofReal_ne_top hℓ0 hℓ
      hAeq hBeq
    have h2 := bayesValue_le_risk P₀ P₁ h₁₀ hκ (ENNReal.ofReal c) ℓ₀ hT hD hT₀
    have h3 : κ * Measure.infinitePi (fun _ : ℕ => P₀) D +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ ≤
        κ * Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) +
          ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b) := by
      gcongr
    have hfin : κ * Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) +
        ℓ₀ * Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b) ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hκ (measure_ne_top _ _),
        ENNReal.mul_ne_top hℓ (measure_ne_top _ _)⟩
    have h4 := ENNReal.le_of_add_le_add_right hfin ((h1.trans h2).trans (add_le_add le_rfl h3))
    exact (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).1 h4

/-- **Wald–Wolfowitz theorem: optimality of the SPRT.** Let `P₀ ≠ P₁` be mutually absolutely
continuous and consider the SPRT with log-boundaries `a < 0 < b`. Let `(T, D)` be any test: a
stopping time `T` of the observations with finite expected value under both hypotheses, and a
rejection region `D` for `P₀` in the stopped `σ`-algebra, whose error probabilities
`P₀(D)` and `P₁(Dᶜ)` do not exceed those of the SPRT. Then the SPRT has smaller expected sample
size under both `P₀` and `P₁`. This is the Wald–Wolfowitz theorem (1948) as stated in Lai 2001,
§2, p. 305, for non-randomised tests; randomised tests are not covered by this statement. -/
theorem sprt_wald_wolfowitz {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) {D : Set (ℕ → X)}
    (hD : MeasurableSet[hT.measurableSpace] D)
    (hT₀ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) < ∞)
    (hT₁ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁) < ∞)
    (hα : Measure.infinitePi (fun _ : ℕ => P₀) D ≤
      Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b))
    (hβ : Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ ≤
      Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b)) :
    ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) ≤
        ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) ∧
      ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => P₁) ≤
        ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁) := by
  set EN₀ := ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)
  set EN₁ := ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
    ∂Measure.infinitePi (fun _ : ℕ => P₁)
  set ET₀ := ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀)
  set ET₁ := ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁)
  have hkey := fun {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) =>
    sprt_weighted_le P₀ P₁ h₁₀ h₀₁ hne ha hb hT hD hT₀.ne hα hβ hκ0 hκ
  constructor
  · -- small `κ`: the weight of `P₁` vanishes
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set K := ENNReal.ofReal (Real.exp (-a)) * ET₁ with hK
    have hKtop : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT₁.ne
    have hK1 : K + 1 ≠ 0 := by simp
    have hK1top : K + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hKtop, ENNReal.one_ne_top⟩
    have hκ0 : (ε : ℝ≥0∞) / (K + 1) ≠ 0 :=
      (ENNReal.div_pos (by exact_mod_cast hε.ne') hK1top).ne'
    have hκ : (ε : ℝ≥0∞) / (K + 1) ≠ ∞ := ENNReal.div_ne_top ENNReal.coe_ne_top hK1
    obtain ⟨ℓ₀, -, -, hle, hmain⟩ := hkey hκ0 hκ
    calc EN₀ ≤ EN₀ + ℓ₀ * EN₁ := le_self_add
      _ ≤ ET₀ + ℓ₀ * ET₁ := hmain
      _ ≤ ET₀ + (ε : ℝ≥0∞) / (K + 1) * (K + 1) := by
          gcongr ET₀ + ?_
          calc ℓ₀ * ET₁ ≤ (ε : ℝ≥0∞) / (K + 1) * ENNReal.ofReal (Real.exp (-a)) * ET₁ := by
                gcongr
            _ = (ε : ℝ≥0∞) / (K + 1) * K := by rw [hK, mul_assoc]
            _ ≤ (ε : ℝ≥0∞) / (K + 1) * (K + 1) := by gcongr; exact le_self_add
      _ = ET₀ + ε := by rw [ENNReal.div_mul_cancel hK1 hK1top]
  · -- large `κ`: the weight of `P₁` dominates
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
    set κ := ET₀ * ENNReal.ofReal (Real.exp b) / ε + 1 with hκdef
    have hκ0 : κ ≠ 0 := by simp [hκdef]
    have hκ : κ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top
      (ENNReal.mul_ne_top hT₀.ne ENNReal.ofReal_ne_top) hε0, ENNReal.one_ne_top⟩
    obtain ⟨ℓ₀, hℓ, hge, -, hmain⟩ := hkey hκ0 hκ
    have hℓ0 : ℓ₀ ≠ 0 := by
      refine (lt_of_lt_of_le ?_ hge).ne'
      exact ENNReal.mul_pos hκ0 (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hET₀ : ET₀ ≤ ℓ₀ * ε := by
      calc ET₀ = ET₀ * ENNReal.ofReal (Real.exp b) / ε * ε * ENNReal.ofReal (Real.exp (-b)) := by
            rw [ENNReal.div_mul_cancel hε0 ENNReal.coe_ne_top, mul_assoc,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
              Real.exp_zero, ENNReal.ofReal_one, mul_one]
        _ ≤ κ * ε * ENNReal.ofReal (Real.exp (-b)) := by gcongr; exact le_self_add
        _ = κ * ENNReal.ofReal (Real.exp (-b)) * ε := by ring
        _ ≤ ℓ₀ * ε := by gcongr
    have h : ℓ₀ * EN₁ ≤ ℓ₀ * (ET₁ + ε) := by
      calc ℓ₀ * EN₁ ≤ EN₀ + ℓ₀ * EN₁ := le_add_self
        _ ≤ ET₀ + ℓ₀ * ET₁ := hmain
        _ ≤ ℓ₀ * ε + ℓ₀ * ET₁ := by gcongr
        _ = ℓ₀ * (ET₁ + ε) := by ring
    exact (ENNReal.mul_le_mul_iff_right hℓ0 hℓ).1 h

end MeasureTheory
